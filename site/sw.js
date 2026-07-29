/* ==========================================================================
   sw.js — offline support.

   Two jobs:

   1. Serve the workbook from cache, so it works with the network off. The text
      is small and cached on install; the 222 MB Lean runtime is only fetched
      when you ask for it, on the "Make available offline" button — nobody
      should download that by accident on mobile data.

   2. Re-send the COOP/COEP headers on cached responses. The Lean runtime needs
      SharedArrayBuffer, which the browser only grants to a cross-origin
      isolated page. Offline there is no server to send those headers, so the
      service worker has to put them back or Lean silently refuses to start.
   ========================================================================== */

const VERSION = 'sl-v5';
const SHELL = VERSION + '-shell';
const LEAN = VERSION + '-lean';

/* Everything needed to read the course. Small — a couple of megabytes. */
const SHELL_FILES = [
  './', './index.html', './manifest.webmanifest',
  './assets/base.css', './assets/blocks.css', './assets/editor.css', './assets/responsive.css',
  './assets/app.js', './assets/editor.js', './assets/lean-runtime.js',
  './assets/icon.svg',
  './lean/context.lean', './lean/context-index.json',
  './content/00-overview.js', './content/01-m0.js', './content/02-m1.js',
  './content/03-m2.js', './content/04-m3.js', './content/05-m4.js',
  './content/06-m5.js', './content/07-m6.js', './content/08-m7.js',
  './content/09-m8.js', './content/10-m9.js', './content/11-m10.js',
  './content/12-m11.js', './content/13-m12.js', './content/14-m13.js',
  './content/15-m14.js', './content/16-ref.js'
];

/* The Lean runtime. Big, and deliberately opt-in. */
const LEAN_FILES = [
  './lean-wasm/lean.js',
  './lean-wasm/lean.wasm',
  './lean-wasm/lean-worker.js',
  './lean-wasm/lean-lib-files.json',
  './lean-wasm/snapshots/init.snap'
];

self.addEventListener('install', (e) => {
  e.waitUntil((async () => {
    const c = await caches.open(SHELL);
    /* One bad URL must not fail the whole install, so add them individually. */
    await Promise.all(SHELL_FILES.map(u => c.add(new Request(u, { cache: 'reload' })).catch(() => {})));
    self.skipWaiting();
  })());
});

self.addEventListener('activate', (e) => {
  e.waitUntil((async () => {
    const keep = new Set([SHELL, LEAN]);
    for (const k of await caches.keys()) if (!keep.has(k)) await caches.delete(k);
    await self.clients.claim();
  })());
});

/* Cross-origin isolation must survive going offline. */
function isolated(res) {
  if (!res || res.status === 0) return res;             // opaque: leave alone
  const h = new Headers(res.headers);
  h.set('Cross-Origin-Opener-Policy', 'same-origin');
  h.set('Cross-Origin-Embedder-Policy', 'require-corp');
  h.set('Cross-Origin-Resource-Policy', 'same-origin');
  return new Response(res.body, { status: res.status, statusText: res.statusText, headers: h });
}

self.addEventListener('fetch', (e) => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== location.origin) return;

  const bare = new Request(url.origin + url.pathname, { headers: req.headers });
  const isLean = url.pathname.includes('/lean-wasm/');

  e.respondWith((async () => {
    /* The Lean runtime is hundreds of megabytes and never changes within a
       build, so serve it from cache and do not go near the network. */
    if (isLean) {
      const hit = await caches.match(bare, { ignoreSearch: true });
      if (hit) return isolated(hit);
      const res = await fetch(req);
      return isolated(res);
    }

    /* Everything else races the network against a short deadline and falls back
       to cache. Cache-first served stale assets; plain network-first hangs when
       the wi-fi is gone but the radio is still associated — the browser can sit
       on a dead connection for half a minute, which reads as "it broke". A
       1.5 s deadline keeps offline snappy without ever serving a stale file
       while there is a working network. */
    const cached = caches.match(bare, { ignoreSearch: true });

    let res = null;
    try {
      res = await Promise.race([
        fetch(req),
        new Promise((_, rej) => setTimeout(() => rej(new Error('slow')), 1500))
      ]);
    } catch (err) {
      const hit = await cached;
      if (hit) return isolated(hit);
      try { res = await fetch(req); }                 // no cache: wait it out
      catch (err2) {
        if (req.mode === 'navigate') {
          const shell = await caches.match('./index.html', { ignoreSearch: true });
          if (shell) return isolated(shell);
        }
        throw err2;
      }
    }

    if (res && res.ok) {
      const copy = res.clone();
      caches.open(SHELL).then(c => c.put(bare, copy)).catch(() => {});
    }
    return isolated(res);
  })());
});

/* ---- "Make available offline" ----------------------------------------
   Downloads the Lean runtime with progress, so the page can show a bar
   instead of appearing to hang for 222 MB. */
self.addEventListener('message', (e) => {
  const msg = e.data || {};
  if (msg.type === 'cache-lean') e.waitUntil(cacheLean(e.source));
  if (msg.type === 'lean-cached?') e.waitUntil(reportCached(e.source));
  if (msg.type === 'drop-lean') e.waitUntil(caches.delete(LEAN).then(() => reportCached(e.source)));
});

async function reportCached(client) {
  const c = await caches.open(LEAN);
  const have = await Promise.all(LEAN_FILES.map(u => c.match(u, { ignoreSearch: true })));
  client && client.postMessage({ type: 'lean-cache-state', cached: have.every(Boolean) });
}

async function cacheLean(client) {
  const c = await caches.open(LEAN);
  let done = 0;
  for (const u of LEAN_FILES) {
    try {
      if (!(await c.match(u, { ignoreSearch: true }))) {
        await c.add(new Request(u, { cache: 'reload' }));
      }
    } catch (err) {
      client && client.postMessage({ type: 'lean-cache-error', url: u, error: String(err) });
    }
    done++;
    client && client.postMessage({ type: 'lean-cache-progress', done, total: LEAN_FILES.length, url: u });
  }
  /* The .olean files are deliberately NOT cached. The snapshot already carries
     the whole imported Init environment, so the runtime never asks for them —
     verified in tools/lean-harness.cjs with NO_LIB=1. Caching 1256 files that
     are never read cost a long install and a lot of storage for nothing. */
  client && client.postMessage({ type: 'lean-cache-done' });
  await reportCached(client);
}
