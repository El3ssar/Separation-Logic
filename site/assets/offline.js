/* ==========================================================================
   offline.js — registers the service worker and drives the offline panel.

   The course text caches itself on first visit (a couple of megabytes). The
   Lean runtime is ~295 MB and is only downloaded when you press the button —
   deliberately, because nobody wants that arriving unannounced on mobile data.
   ========================================================================== */

(function () {
  const el = () => document.getElementById('offlinePanel');
  let reg = null;

  if (!('serviceWorker' in navigator)) { paint({ unsupported: true }); return; }

  navigator.serviceWorker.register('sw.js').then(r => {
    reg = r;
    ask();
  }).catch(e => paint({ error: String(e.message || e) }));

  navigator.serviceWorker.addEventListener('message', (ev) => {
    const m = ev.data || {};
    if (m.type === 'lean-cache-state') paint({ cached: m.cached });
    if (m.type === 'lean-cache-progress') {
      paint({
        busy: true,
        text: m.lib !== undefined
          ? `Lean library — ${m.lib} / ${m.libTotal} files`
          : `Downloading Lean — ${m.done} / ${m.total}`,
        pct: m.lib !== undefined
          ? 40 + Math.round(m.lib / m.libTotal * 60)
          : Math.round(m.done / m.total * 40)
      });
    }
    if (m.type === 'lean-cache-done') paint({ cached: true, justFinished: true });
    if (m.type === 'lean-cache-error') console.warn('[offline]', m.url, m.error);
  });

  function send(type) {
    const c = navigator.serviceWorker.controller;
    if (c) c.postMessage({ type });
    else navigator.serviceWorker.ready.then(r => r.active && r.active.postMessage({ type }));
  }
  const ask = () => send('lean-cached?');

  function paint(s) {
    const node = el();
    if (!node) return;
    if (s.unsupported) { node.innerHTML = '<div class="off-note">This browser has no service worker, so offline use is not available.</div>'; return; }
    if (s.error) { node.innerHTML = '<div class="off-note">Offline setup failed: ' + s.error + '</div>'; return; }

    if (s.busy) {
      node.innerHTML = '<div class="off-t">Saving for offline</div>'
        + '<div class="off-bar"><i style="width:' + (s.pct || 0) + '%"></i></div>'
        + '<div class="off-note">' + (s.text || '') + '</div>';
      return;
    }
    if (s.cached) {
      node.innerHTML = '<div class="off-t off-ok">Available offline</div>'
        + '<div class="off-note">Lean runs with the network off. '
        + '<button class="off-link" id="offDrop">remove the runtime</button></div>';
      const d = document.getElementById('offDrop');
      if (d) d.onclick = () => { paint({ busy: true, text: 'removing…', pct: 0 }); send('drop-lean'); };
      return;
    }
    node.innerHTML = '<div class="off-t">Offline use</div>'
      + '<div class="off-note">The course text is already saved. The Lean runtime is a '
      + '<b>295 MB</b> one-time download — do it on wi-fi.</div>'
      + '<button class="off-btn" id="offGo">Save Lean for offline</button>';
    const g = document.getElementById('offGo');
    if (g) g.onclick = () => { paint({ busy: true, text: 'starting…', pct: 0 }); send('cache-lean'); };
  }

  paint({});
  navigator.serviceWorker.ready.then(ask);
})();
