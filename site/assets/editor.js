/* ==========================================================================
   editor.js — the interactive part.

   Each exercise gets a real editor: syntax highlighting, line numbers, Lean's
   \to-style abbreviations, a tap-able symbol palette (typing ∗ or ↦ on a phone
   keyboard is otherwise hopeless), and a Check button that runs the actual
   Lean kernel over your proof, in the context the course has built up to that
   point — cut before that exercise's own solution.

   Marking an exercise done is driven by Lean, not by a checkbox: it turns
   green when your proof compiles with no errors and no `sorry`.
   ========================================================================== */

/* ---- Lean's abbreviations, restricted to what this course actually uses --- */
const ABBREV = {
  'to': '→', 'r': '→', 'imp': '→', 'l': '←', 'gets': '←',
  'and': '∧', 'or': '∨', 'not': '¬', 'iff': '↔', 'lr': '↔',
  'forall': '∀', 'all': '∀', 'exists': '∃', 'ex': '∃',
  'ne': '≠', 'le': '≤', 'ge': '≥', 'lt': '<', 'gt': '>',
  'in': '∈', 'nin': '∉', 'sub': '⊆', 'union': '∪', 'cup': '∪', 'inter': '∩', 'cap': '∩',
  'emptyset': '∅', 'empty': '∅',
  '<': '⟨', '>': '⟩', 'langle': '⟨', 'rangle': '⟩',
  'star': '∗', 'sep': '∗', 'ast': '∗',
  'mapsto': '↦', 'pointsto': '↦',
  'vdash': '⊢', 'entails': '⊢', 'proves': '⊢',
  'wand': '-∗', 'magic': '-∗',
  'lceil': '⌜', 'rceil': '⌝', 'ulcorner': '⌜', 'urcorner': '⌝',
  'Down': '⇓', 'downarrow': '⇓',
  'equiv': '≡', 'bot': '⊥', 'top': '⊤',
  'circ': '∘', 'cdot': '·', 'times': '×',
  'alpha': 'α', 'beta': 'β', 'gamma': 'γ', 'delta': 'δ', 'sigma': 'σ', 'phi': 'φ',
  'psi': 'ψ', 'rho': 'ρ', 'tau': 'τ', 'lam': 'λ', 'lambda': 'λ',
  'Sigma': 'Σ', 'Pi': 'Π', 'Gamma': 'Γ',
  '1': '₁', '2': '₂', '3': '₃', '4': '₄', '0': '₀',
  'sub1': '₁', 'sub2': '₂', 'sub3': '₃',
  'triangle': '▸', 'nat': 'ℕ'
};

/* the palette, grouped — these are the keys you cannot type on a phone */
const PALETTE = [
  ['∗', 'separating conjunction'], ['↦', 'points-to'], ['⊢', 'entails'],
  ['-∗', 'magic wand'], ['⟨', 'anonymous constructor'], ['⟩', 'close'],
  ['→', 'implies'], ['∧', 'and'], ['∨', 'or'], ['¬', 'not'],
  ['∀', 'for all'], ['∃', 'exists'], ['≠', 'not equal'], ['↔', 'iff'],
  ['σ', 'store'], ['₁', 'subscript 1'], ['₂', 'subscript 2'], ['·', 'focus dot'],
  ['⌜', 'pure open'], ['⌝', 'pure close'], ['≡', 'equiv'], ['∅', 'empty']
];

const EDITORS = new Map();     // exercise id -> editor instance

/* ---- one editor ------------------------------------------------------- */

function mountEditor(root, ex) {
  const ta = root.querySelector('.ed-ta');
  const hl = root.querySelector('.ed-hl');
  const gutter = root.querySelector('.ed-gutter');
  const runBtn = root.querySelector('[data-run]');
  const resetBtn = root.querySelector('[data-reset-ed]');
  const out = root.querySelector('.ed-out');
  const statusEl = root.querySelector('.ed-status');

  const storeKey = 'sl:code:' + ex.id;

  function paint() {
    hl.innerHTML = hlLean(ta.value) + '\n';
    const n = ta.value.split('\n').length;
    gutter.textContent = Array.from({ length: n }, (_, i) => i + 1).join('\n');
    hl.scrollTop = ta.scrollTop; hl.scrollLeft = ta.scrollLeft;
    /* grow with content instead of scrolling in a tiny box */
    ta.style.height = 'auto';
    ta.style.height = Math.max(120, ta.scrollHeight) + 'px';
    hl.style.height = ta.style.height;
    gutter.style.height = ta.style.height;
  }

  /* \to + space -> →  ------------------------------------------------- */
  function expandAbbrev() {
    const pos = ta.selectionStart;
    const before = ta.value.slice(0, pos);
    const m = /\\([A-Za-z<>0-9]*)$/.exec(before);
    if (!m) return false;
    const rep = ABBREV[m[1]];
    if (!rep) return false;
    const start = pos - m[0].length;
    ta.value = ta.value.slice(0, start) + rep + ta.value.slice(pos);
    ta.selectionStart = ta.selectionEnd = start + rep.length;
    return true;
  }

  function insert(text) {
    const s = ta.selectionStart, e = ta.selectionEnd;
    ta.value = ta.value.slice(0, s) + text + ta.value.slice(e);
    ta.selectionStart = ta.selectionEnd = s + text.length;
    ta.focus(); paint(); save();
  }

  const save = () => { try { localStorage.setItem(storeKey, ta.value); } catch (e) {} };

  ta.addEventListener('input', () => { paint(); save(); });
  ta.addEventListener('scroll', () => { hl.scrollTop = ta.scrollTop; hl.scrollLeft = ta.scrollLeft; });

  ta.addEventListener('keydown', (e) => {
    if (e.key === ' ' || e.key === 'Tab') {
      if (expandAbbrev()) { e.preventDefault(); paint(); save(); return; }
    }
    if (e.key === 'Tab') {                       // indent, don't leave the field
      e.preventDefault(); insert('  '); return;
    }
    if (e.key === 'Enter') {                     // keep the current indentation
      const pos = ta.selectionStart;
      const line = ta.value.slice(0, pos).split('\n').pop();
      const ind = (line.match(/^\s*/) || [''])[0];
      e.preventDefault(); insert('\n' + ind); return;
    }
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); run(); }
  });

  root.querySelectorAll('[data-sym]').forEach(b => {
    b.addEventListener('click', () => insert(b.dataset.sym));
  });

  resetBtn?.addEventListener('click', () => {
    ta.value = starterFor(ex); paint(); save();
    out.innerHTML = ''; out.classList.remove('on');
    setStatus('', '');
  });

  function setStatus(cls, text) {
    statusEl.className = 'ed-status ' + cls;
    statusEl.textContent = text;
  }

  /* ---- run ---- */
  async function run() {
    if (runBtn.disabled) return;
    runBtn.disabled = true;
    out.classList.add('on');

    /* There is one Lean process, so a check started elsewhere has to finish
       first. LeanRuntime.check queues rather than refusing; say so. */
    const rt = LeanRuntime.snapshot();
    if (rt.state === LeanRuntime.S.BUSY) {
      out.innerHTML = '<div class="ed-msg info">Waiting for the check already running…</div>';
      setStatus('running', 'queued');
    } else if (rt.state !== LeanRuntime.S.READY) {
      out.innerHTML = '<div class="ed-msg info"><b>Starting Lean…</b><br>'
        + 'The first run of a session loads Lean’s core library — about ten seconds, '
        + 'once. After that every check is quick. You can keep reading meanwhile.</div>';
      setStatus('running', 'starting Lean');
    } else {
      out.innerHTML = '<div class="ed-msg info">Checking…</div>';
      setStatus('running', 'checking');
    }

    const context = await loadContext(ex.id);
    const res = await LeanRuntime.check(ta.value, context);
    runBtn.disabled = false;
    renderResult(res);
  }

  function renderResult(res) {
    if (res.unavailable) {
      setStatus('warn', 'unavailable');
      out.innerHTML = '<div class="ed-msg warn"><b>Lean cannot run here.</b><br>' + esc(res.raw)
        + '<br><br>Serve the site with <code>site/tools/serve.py</code>, which sends the '
        + 'COOP/COEP headers the Lean runtime needs.</div>';
      return;
    }
    if (res.broken) {
      setStatus('err', 'Lean failed');
      out.innerHTML = '<div class="ed-msg err"><b>The Lean runtime failed — this is not a verdict on your proof.</b>'
        + '<pre>' + esc(res.raw) + '</pre></div>';
      return;
    }

    const errs = res.messages.filter(m => m.severity === 'error');
    const warns = res.messages.filter(m => m.severity === 'warning' && m.kind !== 'hasSorry');
    const infos = res.messages.filter(m => m.severity === 'info');

    let h = '';
    if (res.proved) {
      setStatus('ok', 'proved · ' + res.elapsed + 'ms');
      h += '<div class="ed-msg ok"><b>Lean accepts this proof.</b> No errors, no <code>sorry</code>.</div>';
      markSolved(ex.id);
    } else if (res.ok && res.usesSorry) {
      setStatus('warn', 'has sorry');
      h += '<div class="ed-msg warn"><b>It compiles, but there is still a <code>sorry</code> in it.</b> '
        + 'Lean is taking your word for that part, so this does not count as proved.</div>';
    } else {
      setStatus('err', errs.length + (errs.length === 1 ? ' error' : ' errors'));
    }

    for (const m of [...errs, ...warns, ...infos]) {
      const cls = m.severity === 'error' ? 'err' : m.severity === 'warning' ? 'warn' : 'info';
      h += '<div class="ed-msg ' + cls + '">'
        + (m.inPrelude
            ? '<span class="ed-loc">in the chapter prelude</span>'
            : '<span class="ed-loc">line ' + m.line + ', col ' + m.col + '</span>')
        + '<pre>' + esc(m.text) + '</pre></div>';
    }
    if (res.unexplained) {
      h += '<div class="ed-msg err"><b>Lean produced output that could not be interpreted.</b> '
        + 'Treating it as a failure rather than guessing.<pre>' + esc(res.raw || '') + '</pre></div>';
    } else if (!res.messages.length && !res.ok) {
      h += '<div class="ed-msg err"><pre>' + esc(res.raw || 'no output') + '</pre></div>';
    }
    out.innerHTML = h;
  }

  runBtn.addEventListener('click', run);

  /* restore the reader's own last attempt */
  let saved = null;
  try { saved = localStorage.getItem(storeKey); } catch (e) {}
  ta.value = saved != null ? saved : starterFor(ex);
  paint();

  EDITORS.set(ex.id, { run, paint, ta });
}

/* The starting text: the theorem statement as given, with the proof left open. */
function starterFor(ex) {
  const goal = (ex.goal || '').replace(/\s*$/, '');
  if (!goal) return '-- write your proof here\n';
  return /:=\s*(by\b|$)/.test(goal) ? goal + '\n  sorry\n' : goal + ' := by\n  sorry\n';
}

/* ---- the Lean context each exercise is checked against ------------------
   One 45 KB file holding the whole course in order, plus an index saying how
   much of it precedes each exercise. Crucially the cut is *before* that
   exercise's own solution — otherwise Lean answers "already been declared"
   instead of checking the reader's proof. Built by tools/gen-contexts.mjs. */
let CONTEXT = null, CONTEXT_INDEX = null;
async function loadContext(exId) {
  if (CONTEXT === null) {
    try {
      const [c, i] = await Promise.all([
        fetch('lean/context.lean').then(r => r.text()),
        fetch('lean/context-index.json').then(r => r.json())
      ]);
      CONTEXT = c; CONTEXT_INDEX = i;
    } catch (e) { CONTEXT = ''; CONTEXT_INDEX = {}; }
  }
  const cut = CONTEXT_INDEX[exId];
  return typeof cut === 'number' ? CONTEXT.slice(0, cut) : CONTEXT;
}

/* ---- marking solved --------------------------------------------------- */
function markSolved(id) {
  if (DONE[id]) return;
  DONE[id] = true;
  Store.set('sl:done', JSON.stringify(DONE));
  const card = document.querySelector('[data-ex="' + id + '"]');
  if (card) {
    card.classList.add('done', 'just-proved');
    setTimeout(() => card.classList.remove('just-proved'), 1600);
  }
  renderNav();
}

/* ---- the markup ------------------------------------------------------- */
function editorHtml(ex) {
  const pal = PALETTE.map(([s, t]) =>
    '<button class="sym" data-sym="' + s + '" title="' + t + '" type="button">' + s + '</button>').join('');
  return ''
    + '<div class="ed" data-ed="' + ex.id + '">'
    +   '<div class="ed-bar">'
    +     '<span class="ed-t">Your proof</span>'
    +     '<span class="ed-status"></span>'
    +     '<button class="ed-btn ghost" data-reset-ed type="button">Reset</button>'
    +     '<button class="ed-btn go" data-run type="button">Check with Lean</button>'
    +   '</div>'
    +   '<div class="ed-pal">' + pal + '</div>'
    +   '<div class="ed-wrap">'
    +     '<pre class="ed-gutter">1</pre>'
    +     '<div class="ed-code">'
    +       '<pre class="ed-hl" aria-hidden="true"></pre>'
    +       '<textarea class="ed-ta" spellcheck="false" autocapitalize="off" autocomplete="off" autocorrect="off"></textarea>'
    +     '</div>'
    +   '</div>'
    +   '<div class="ed-hintbar">Type <code>\\to</code> then space for <code>→</code>, <code>\\star</code> for <code>∗</code>, '
    +     '<code>\\mapsto</code> for <code>↦</code>. <kbd>Ctrl</kbd>+<kbd>Enter</kbd> checks.</div>'
    +   '<div class="ed-out"></div>'
    + '</div>';
}

/* ---- runtime status pill in the topbar -------------------------------- */
function mountLeanStatus() {
  const el = document.getElementById('leanStatus');
  if (!el) return;
  LeanRuntime.on(({ state, detail }) => {
    const S = LeanRuntime.S;
    let cls = '', text = '';
    switch (state) {
      case S.IDLE: cls = 'idle'; text = 'Lean idle'; break;
      case S.BOOTING: case S.LOADING_LIB: case S.WARMING: cls = 'warm'; text = detail || 'starting Lean'; break;
      case S.READY: cls = 'ok'; text = 'Lean ready'; break;
      case S.BUSY: cls = 'busy'; text = 'checking'; break;
      case S.UNSUPPORTED: cls = 'off'; text = 'Lean unavailable'; break;
      default: cls = 'off'; text = 'Lean failed';
    }
    el.className = 'lean-pill ' + cls;
    el.textContent = text;
    el.title = detail || text;
  });
  el.addEventListener('click', () => LeanRuntime.warmup());
}

window.EditorUI = { editorHtml, mountEditor, mountLeanStatus, EDITORS };
