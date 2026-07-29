/* ==========================================================================
   lean-runtime.js — one warm Lean process for the whole site.

   Boots the Lean 4 WASM build in a Web Worker, keeps it alive, and exposes a
   single async check(). The expensive part is starting up: the first compile
   imports Init, which takes a minute or two. After that the environment is
   cached inside Lean and each check costs only what your own proof costs.

   So: we start warming up the moment the reader opens a chapter that has
   exercises, in the background, and the UI stays usable throughout.

   Requires cross-origin isolation (COOP/COEP) for SharedArrayBuffer —
   tools/serve.py sends the headers, and sw.js re-sends them offline.
   ========================================================================== */

const LeanRuntime = (() => {
  const BASE = 'lean-wasm';

  const S = {
    IDLE: 'idle', BOOTING: 'booting', LOADING_LIB: 'loading-library',
    WARMING: 'warming', READY: 'ready', BUSY: 'busy', FAILED: 'failed',
    UNSUPPORTED: 'unsupported'
  };

  let worker = null;
  let dead = false;                // set once the runtime stops responding
  let state = S.IDLE;
  let detail = '';
  let startedAt = 0;
  let pending = null;              // {resolve, lines:[]}
  let warmupPromise = null;
  const listeners = new Set();

  const emit = () => listeners.forEach(f => { try { f(snapshot()); } catch (e) {} });
  const snapshot = () => ({ state, detail, elapsed: startedAt ? Date.now() - startedAt : 0 });

  function on(f) { listeners.add(f); f(snapshot()); return () => listeners.delete(f); }
  function set(s, d) { state = s; detail = d || ''; emit(); }

  /* SharedArrayBuffer is the hard requirement. Without cross-origin isolation
     the worker boots and then dies confusingly, so check up front. */
  function supported() {
    if (typeof Worker === 'undefined') return 'this browser has no Web Workers';
    if (typeof SharedArrayBuffer === 'undefined') {
      return self.crossOriginIsolated === false
        ? 'the page is not cross-origin isolated (COOP/COEP headers missing)'
        : 'this browser does not expose SharedArrayBuffer';
    }
    if (typeof WebAssembly === 'undefined') return 'this browser has no WebAssembly';
    return null;
  }

  /* ---- boot ------------------------------------------------------------ */

  function warmup() {
    if (warmupPromise) return warmupPromise;

    const why = supported();
    if (why) { set(S.UNSUPPORTED, why); return warmupPromise = Promise.resolve(false); }

    startedAt = Date.now();
    set(S.BOOTING, 'starting the Lean worker');

    warmupPromise = new Promise((resolve) => {
      try {
        worker = new Worker(`${BASE}/lean-worker.js?assetBase=/${BASE}`);
      } catch (e) {
        set(S.FAILED, 'could not start the worker: ' + (e.message || e));
        return resolve(false);
      }

      let libFiles = null;
      let useSnapshot = false;

      worker.onerror = (e) => {
        set(S.FAILED, 'worker error: ' + (e.message || 'unknown'));
        resolve(false);
      };

      worker.onmessage = async (ev) => {
        const m = ev.data || {};
        switch (m.type) {

          case 'worker_boot':
            /* The .olean files must be on Lean's search path even when a
               snapshot is used: the snapshot seeds the *environment*, but the
               module resolver still stats /lib/lean to resolve `import Init`.
               Skipping them yields "unknown module prefix 'Init'". */
            useSnapshot = await hasSnapshot();
            set(S.LOADING_LIB, 'fetching the Lean standard library');
            libFiles = await fetchLibrary();
            if (!libFiles) { set(S.FAILED, 'could not fetch the Lean library'); return resolve(false); }
            worker.postMessage({ type: 'load_library', files: libFiles }, libFiles.map(f => f.data));
            break;

          case 'library_received':
            set(S.BOOTING, 'initialising the Lean runtime');
            worker.postMessage({ type: 'start_worker' });
            break;

          case 'worker_ready':
            /* Use a baked snapshot when the build has one — it replaces the
               multi-minute Init import with a few seconds of region load. */
            if (useSnapshot) {
              set(S.WARMING, 'downloading the pre-baked Lean environment');
              try {
                const resp = await fetch(`${BASE}/snapshots/init.snap`);
                const buf = await resp.arrayBuffer();
                set(S.WARMING, 'loading the pre-baked Lean environment');
                worker.postMessage({ type: 'load_snapshot_bytes', data: buf }, [buf]);
              } catch (e) {
                set(S.WARMING, 'importing Lean’s core library (one time, a minute or two)');
                primeByCompiling(resolve);
              }
            } else {
              set(S.WARMING, 'importing Lean’s core library (one time, a minute or two)');
              primeByCompiling(resolve);
            }
            break;

          case 'snapshot_loaded':
            if (m.success) { set(S.READY, 'ready'); resolve(true); }
            else { set(S.WARMING, 'importing Lean’s core library (one time, a minute or two)'); primeByCompiling(resolve); }
            break;

          case 'import_progress':
            if (state === S.WARMING && m.total) {
              set(S.WARMING, `importing Lean’s core library — ${Math.round(m.loaded / m.total * 100)}%`);
            }
            break;

          case 'snapshot_progress':
            if (m.total) set(S.WARMING, `loading Lean environment — ${Math.round(m.received / m.total * 100)}%`);
            break;

          case 'stdout':
          case 'stderr':
            if (pending) pending.lines.push(m.data);
            break;

          case 'compile_result':
            if (pending) { const p = pending; pending = null; p.resolve(p.lines.join('\n')); }
            break;

          case 'error':
            if (pending) { const p = pending; pending = null; p.resolve('__WORKER_ERROR__ ' + m.data); }
            else { set(S.FAILED, m.data || 'worker error'); resolve(false); }
            break;
        }
      };
    });

    return warmupPromise;
  }

  /* Builds with no snapshot support: force the Init import now, with a trivial
     file, so the reader pays it while reading rather than on their first proof. */
  function primeByCompiling(resolve) {
    rawCompile('example : True := trivial\n').then(() => {
      set(S.READY, 'ready'); resolve(true);
    }).catch(() => { set(S.FAILED, 'the Lean runtime failed to start'); resolve(false); });
  }

  async function hasSnapshot() {
    try {
      const r = await fetch(`${BASE}/snapshots/init.snap`, { method: 'HEAD' });
      return r.ok && Number(r.headers.get('content-length') || 0) > 1024;
    } catch (e) { return false; }
  }

  /* ~1250 small files. Serially that is a round-trip storm; 16 at a time keeps
     the connection busy without swamping the browser's socket pool. */
  async function fetchLibrary() {
    try {
      const list = await (await fetch(`${BASE}/lean-lib-files.json`)).json();
      /* macOS tars leave AppleDouble ._ shadows in the archive; Lean chokes on them */
      const names = list.filter(n => !n.split('/').some(p => p.startsWith('._')));
      const out = new Array(names.length);
      let next = 0, done = 0;

      async function pump() {
        for (;;) {
          const i = next++;
          if (i >= names.length) return;
          const r = await fetch(`${BASE}/lean-lib/${names[i]}`);
          if (!r.ok) throw new Error(`${names[i]}: ${r.status}`);
          out[i] = { name: names[i], data: await r.arrayBuffer() };
          if (++done % 64 === 0) {
            set(S.LOADING_LIB, `fetching Lean’s core library — ${Math.round(done / names.length * 100)}%`);
          }
        }
      }
      await Promise.all(Array.from({ length: 16 }, pump));
      return out;
    } catch (e) { return null; }
  }

  /* ---- compiling ------------------------------------------------------- */

  function rawCompile(code, path) {
    return new Promise((resolve, reject) => {
      if (!worker) return reject(new Error('no worker'));
      if (pending) return reject(new Error('a check is already running'));
      pending = { resolve, lines: [] };
      worker.postMessage({ type: 'compile', code, path: path || '/workspace/input.lean' });
    });
  }

  /* Lean failing to *run* is not the same as Lean rejecting a proof, and the
     difference must never be silently reported as success. These are the shapes
     a runtime failure takes: an Emscripten abort, a Lean-side uncaught
     exception, or the module resolver not finding its own library. */
  const RUNTIME_FAILURE = /uncaught exception|unknown module prefix|no directory .* or file|Aborted\(|__WORKER_ERROR__|out of memory|RuntimeError/i;

  /* Printed by every run; its absence means Lean never got to the end of the
     file. `Nat.succ 0` is chosen because its elaborated form is distinctive
     and cannot appear by accident in this course's output. */
  const PROBE_SRC = '\n#check (Nat.succ 0)\n';
  const PROBE_RE = /Nat\.succ 0 : Nat/;

  /* ---- the public entry point ------------------------------------------ */

  /* Check `userCode` in the context of `prelude`.
     Returns {ok, messages:[{severity, line, col, text}], raw, elapsed}
     with line numbers already translated back into the reader's own text. */
  async function check(userCode, prelude) {
    if (dead) return { ok: false, broken: true, messages: [], raw: 'The Lean runtime stopped responding. Reload the page to restart it.' };
    const ok = await warmup();
    if (!ok) return { ok: false, messages: [], raw: detail, unavailable: true };
    if (state === S.BUSY) return { ok: false, messages: [], raw: 'a check is already running', busy: true };

    /* The WASM build tracks Lean master, where declarations are private by
       default — a public `infix` notation then cannot see the `def` it names.
       `public section` restores the stable-Lean behaviour and is accepted by
       4.28, 4.32 and master alike. */
    const head = 'public section\n';
    const body = (prelude ? prelude.replace(/\s*$/, '') + '\n\n' : '') + userCode;
    /* A liveness probe. A dead or wedged Lean produces no output at all, which
       is byte-identical to "your proof was accepted". So make every run print
       something we can insist on: if this line's output is missing, Lean did
       not actually run the file and we must not report a pass. */
    const source = head + body + '\nend\n' + PROBE_SRC;

    /* Everything before the reader's own first line, so we can shift back. */
    const offset = head.split('\n').length - 1
      + (prelude ? prelude.replace(/\s*$/, '').split('\n').length + 1 : 0);

    const t0 = performance.now();
    set(S.BUSY, 'checking');
    let raw;
    try { raw = await rawCompile(source); }
    catch (e) { set(S.READY, 'ready'); return { ok: false, messages: [], raw: String(e.message || e), broken: true }; }
    set(S.READY, 'ready');

    const elapsed = Math.round(performance.now() - t0);

    /* Distinguish "your proof is wrong" from "Lean did not run". Reporting the
       second as a pass would be the worst possible failure of this tool. */
    if (RUNTIME_FAILURE.test(raw)) {
      return { ok: false, broken: true, messages: [], raw: String(raw).trim(), elapsed };
    }
    if (!PROBE_RE.test(raw)) {
      dead = true;
      set(S.FAILED, 'the Lean runtime stopped responding');
      return {
        ok: false, broken: true, messages: [], elapsed,
        raw: 'Lean produced no output for this file, not even the liveness probe, '
           + 'so it is no longer running. Reload the page to restart it.\n\n'
           + String(raw || '').trim()
      };
    }

    const messages = parseMessages(raw, offset);
    const hardErrors = messages.filter(m => m.severity === 'error');
    /* Lean tells us about `sorry` itself, which is more reliable than looking
       for the word in the reader's text (it could be in a comment or a name). */
    const usesSorry = messages.some(m => m.kind === 'hasSorry' || /declaration uses `sorry`/.test(m.text));

    const unexplained = messages.length === 0 && residualNoise(raw).length > 0;

    return {
      ok: hardErrors.length === 0 && !unexplained,
      proved: hardErrors.length === 0 && !unexplained && !usesSorry,
      usesSorry, unexplained,
      messages, raw, elapsed
    };
  }

  /* The WASM build reports each diagnostic as one line of JSON:
       {"data":"Unknown identifier `foo`","severity":"error",
        "pos":{"line":1,"column":29},"endPos":{...},"kind":"..."}
     which is much better than the CLI's text format — we get the exact range
     and Lean's own message kind, including `hasSorry`. Lines are 1-based and
     columns 0-based, both relative to the spliced file. */
  function parseMessages(raw, offset) {
    const out = [];
    for (const line of String(raw || '').split('\n')) {
      const s = line.trim();
      if (s[0] !== '{' || !s.includes('"severity"')) continue;
      let j;
      try { j = JSON.parse(s); } catch (e) { continue; }
      if (!j || !j.severity) continue;
      if (PROBE_RE.test(String(j.data || ''))) continue;   // our own liveness probe
      const at = j.pos || {};
      const absLine = typeof at.line === 'number' ? at.line : 0;
      out.push({
        severity: j.severity,
        kind: j.kind || '',
        line: Math.max(1, absLine - offset),
        col: (typeof at.column === 'number' ? at.column : 0) + 1,
        endLine: j.endPos ? Math.max(1, j.endPos.line - offset) : undefined,
        endCol: j.endPos ? j.endPos.column + 1 : undefined,
        text: String(j.data == null ? '' : j.data),
        inPrelude: absLine > 0 && absLine <= offset
      });
    }
    return out;
  }

  /* Anything that is neither a diagnostic nor known chatter. Used to refuse to
     call a run successful when we did not understand what Lean said. */
  function residualNoise(raw) {
    return String(raw || '').split('\n').filter(l => {
      const s = l.trim();
      if (!s) return false;
      if (s[0] === '{' && s.includes('"severity"')) return false;      // diagnostic
      if (PROBE_RE.test(s)) return false;                              // liveness probe
      if (/^\[(WASM DEBUG|DEBUG|COMPILE|PWORKER|PROFILE)/.test(s)) return false;
      if (/^-\s+\/lib\/lean\/.*\.olean$/.test(s)) return false;
      return true;
    });
  }

  return { warmup, check, on, state: () => state, snapshot, S, supported };
})();

window.LeanRuntime = LeanRuntime;
