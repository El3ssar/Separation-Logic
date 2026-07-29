/* ==========================================================================
   app.js — the whole workbook engine.

   Content lives in content/*.js; each of those files calls registerChapter().
   Nothing here knows anything about separation logic; it only knows how to
   turn a block list into HTML. To add a new kind of block: add a case to
   renderBlock(), a style rule in blocks.css, and a line in AUTHORING.md.
   ========================================================================== */

/* ============ chapter registry ============ */
const COURSE = [];
window.registerChapter = function (ch) { COURSE.push(ch); };

/* ============ storage: window.storage when available, localStorage, memory ============ */
const mem = {};
const Store = {
  mode: (() => {
    if (typeof window !== 'undefined' && window.storage) return 'host';
    try { localStorage.setItem('sl:probe', '1'); localStorage.removeItem('sl:probe'); return 'local'; }
    catch (e) { return 'mem'; }
  })(),
  async get(k) {
    if (Store.mode === 'host') { try { const r = await window.storage.get(k); return r ? r.value : null; } catch (e) { return mem[k] ?? null; } }
    if (Store.mode === 'local') { try { return localStorage.getItem(k); } catch (e) { return mem[k] ?? null; } }
    return mem[k] ?? null;
  },
  async set(k, v) {
    mem[k] = v;
    if (Store.mode === 'host') { try { await window.storage.set(k, v); } catch (e) {} return; }
    if (Store.mode === 'local') { try { localStorage.setItem(k, v); } catch (e) {} }
  }
};

let DONE = {};        // exercise id -> true
let THEME = 'auto';
let cur = 0;

/* ============ escaping + Lean highlighting ============ */
const KW = ['theorem', 'lemma', 'def', 'abbrev', 'inductive', 'structure', 'namespace', 'end', 'import',
  'infixr', 'infixl', 'infix', 'notation', 'fun', 'match', 'with', 'if', 'then', 'else', 'where', 'Prop', 'Sort',
  'let', 'have', 'show', 'by', 'do', 'deriving', 'open', 'instance', 'class', 'example', 'intro', 'intros',
  'exact', 'refine', 'obtain', 'rcases', 'cases', 'induction', 'funext', 'simp', 'rw', 'rfl', 'constructor',
  'subst', 'apply', 'by_cases', 'generalizing', 'rename_i', 'unfold', 'exfalso', 'omega', 'decide',
  'left', 'right', 'use', 'calc', 'sorry', 'trivial', 'contradiction', 'specialize', 'ext', 'split', 'rintro',
  'first', 'repeat', 'all_goals', 'any_goals', 'nomatch', 'attribute', 'variable', 'section', 'mutual', 'partial',
  'protected', 'private', 'noncomputable', 'macro', 'syntax', 'set_option', 'universe', 'from', 'this', 'at'];
const kwRe = new RegExp('\\b(' + KW.join('|') + ')\\b', 'g');
const opRe = /(∗|⊣⊢|⊢|↦|-∗|∧|∨|∃|∀|≠|↔|⟨|⟩|⇓|⌜|⌝|→|≡|⊥|←|;;|⊆|∪|·|▸|⟪|⟫|≫=|⊨|∅|×|∘)/g;
const numRe = /\b(\d+)\b/g;

const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const strip = s => String(s || '').replace(/<[^>]+>/g, ' ');

function hlLean(src) {
  return src.split('\n').map(line => {
    const ci = line.indexOf('--');
    let head = line, tail = '';
    if (ci >= 0) { head = line.slice(0, ci); tail = '<span class="tk-cm">' + esc(line.slice(ci)) + '</span>'; }
    let out = esc(head);
    out = out.replace(kwRe, '<span class="tk-kw">$1</span>');
    out = out.replace(opRe, '<span class="tk-op">$1</span>');
    out = out.replace(numRe, '<span class="tk-num">$1</span>');
    return out + tail;
  }).join('\n');
}

/* ============ code blocks ============ */
let cbn = 0;
const ICON_COPY = '<svg width="11" height="11" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><rect x="9" y="9" width="13" height="13" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/></svg>';

/* tag -> [label, css class, highlight?] */
const CB_TAG = {
  verified:    ['Lean 4 · verified',    '',       true],
  illustration:['Lean 4 · illustration', 'illus',  true],
  sketch:      ['Lean 4 · sketch',       'sketch', true],
  state:       ['proof state',           'state',  false],
  txt:         ['schema',                'txt',    false]
};

function codeBlock(src, tag, cap) {
  const id = 'cb' + (cbn++);
  const [label, cls, lean] = CB_TAG[tag] || CB_TAG.verified;
  const body = lean ? hlLean(src) : esc(src);
  return '<div class="cb"><div class="cb-bar"><span class="cb-lang ' + cls + '">' + label + '</span>'
    + '<button class="copy" data-cb="' + id + '">' + ICON_COPY + '<span>Copy</span></button></div>'
    + '<pre class="' + (lean ? '' : 'txt') + '"><code id="' + id + '">' + body + '</code></pre></div>'
    + (cap ? '<div class="cap">' + cap + '</div>' : '');
}

/* ============ icons ============ */
const I_INFO = '<svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="12" cy="12" r="9.5"/><path d="M12 16.5v-5M12 8h.01"/></svg>';
const I_WARN = '<svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M10.3 3.9 1.9 18a2 2 0 0 0 1.7 3h16.8a2 2 0 0 0 1.7-3L13.7 3.9a2 2 0 0 0-3.4 0Z"/><path d="M12 9v4M12 17h.01"/></svg>';
const I_KEY = '<svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="m12 2 2.6 6.3 6.8.5-5.2 4.4 1.6 6.6L12 16.3 6.2 19.8l1.6-6.6L2.6 8.8l6.8-.5Z"/></svg>';
const I_TIP = '<svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M9 18h6M10 22h4M12 2a7 7 0 0 0-4 12.7V17h8v-2.3A7 7 0 0 0 12 2Z"/></svg>';
const I_CHECK = '<svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3.4" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6 9 17l-5-5"/></svg>';
const I_DOD = '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="m9 11 3 3L22 4"/><path d="M21 12v7a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11"/></svg>';
const I_TW = '<svg width="11" height="11" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="m9 18 6-6-6-6"/></svg>';
const I_PIN = '<svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 2v6M5 8h14l-2 6H7L5 8ZM9 14v8"/></svg>';
const I_GOAL = '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="12" cy="12" r="9.5"/><circle cx="12" cy="12" r="4.5"/></svg>';
const I_NEED = '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 19.5V6a2 2 0 0 1 2-2h13v16H6.5A2.5 2.5 0 0 0 4 22.5V19.5Z"/></svg>';

const ARROWHEAD = '<defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" fill="currentColor" opacity=".55"/></marker></defs>';

/* ============ block renderer ============ */
let hn = 0;                                  // heading counter, for in-page anchors
const slug = s => 'h-' + (hn++) + '-' + strip(s).toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '').slice(0, 40);

function renderBlock(b) {
  if (!b || !b.t) return '';
  switch (b.t) {

    /* ---- prose ---- */
    case 'p':     return '<p>' + b.h + '</p>';
    case 'h3':    return '<h3 id="' + slug(b.s) + '">' + b.s + '</h3>';
    case 'h4':    return '<h4 id="' + slug(b.s) + '">' + b.s + '</h4>';
    case 'sec':   return '<div class="sec-head" id="' + slug(b.s) + '">' + b.s + '</div>';
    case 'ul':    return '<ul>' + b.items.map(i => '<li>' + i + '</li>').join('') + '</ul>';
    case 'ol':    return '<ol>' + b.items.map(i => '<li>' + i + '</li>').join('') + '</ol>';
    case 'quote': return '<blockquote>' + b.h + '</blockquote>';

    /* ---- code ---- */
    case 'code':  return codeBlock(b.src, b.tag || 'verified', b.cap);
    case 'txt':   return codeBlock(b.src, 'txt', b.cap);
    case 'state': return codeBlock(b.src, 'state', b.cap);

    case 'svg':
      return '<div class="dgwrap">' + b.src.replace('<g class="dg">', ARROWHEAD + '<g class="dg">') + '</div>'
        + (b.cap ? '<div class="cap">' + b.cap + '</div>' : '');

    /* ---- callouts ---- */
    case 'note': {
      const ic = b.kind === 'warn' ? I_WARN : b.kind === 'key' ? I_KEY : b.kind === 'tip' ? I_TIP : I_INFO;
      return '<div class="note ' + (b.kind || 'info') + '"><span class="ic">' + ic + '</span><div>'
        + (b.title ? '<div class="nt">' + b.title + '</div>' : '') + '<p>' + b.h + '</p></div></div>';
    }
    case 'dod':
      return '<div class="dod"><div class="nt">' + I_DOD + ' Definition of done</div><p>' + b.h + '</p></div>';

    case 'defn':
      return '<div class="defn"><div class="defn-t">Definition</div>'
        + (b.term ? '<div class="defn-term">' + b.term + '</div>' : '')
        + '<p>' + b.h + '</p>'
        + (b.cap ? '<div class="cap" style="margin:8px 0 0">' + b.cap + '</div>' : '')
        + '</div>';

    /* ---- structured ---- */
    case 'steps':
      return '<div class="steps">'
        + (b.title ? '<div class="steps-t">' + b.title + '</div>' : '')
        + b.items.map((it, i) =>
            '<div class="step"><div class="step-n">' + (i + 1) + '</div><div>'
            + (it.k ? '<div class="step-k">' + it.k + '</div>' : '')
            + '<div class="step-b">' + wrapProse(it.h) + '</div></div></div>').join('')
        + '</div>';

    case 'tbl':
      return '<div class="tblwrap"><table>'
        + (b.head ? '<thead><tr>' + b.head.map(x => '<th>' + x + '</th>').join('') + '</tr></thead>' : '')
        + '<tbody>' + b.rows.map(r => '<tr>' + r.map(x => '<td>' + x + '</td>').join('') + '</tr>').join('') + '</tbody>'
        + '</table></div>' + (b.cap ? '<div class="cap">' + b.cap + '</div>' : '');

    case 'dl':
      return '<div class="dl">' + b.items.map(it =>
        '<div class="dl-row"><div class="dl-k">' + it.k + '</div><div class="dl-v">' + wrapProse(it.h) + '</div></div>'
      ).join('') + '</div>';

    case 'cmp':
      return '<div class="cmp">'
        + ['left', 'right'].map(side => {
            const c = b[side]; if (!c) return '';
            return '<div class="cmp-c ' + (c.kind || '') + '">'
              + (c.t ? '<div class="cmp-t">' + c.t + '</div>' : '')
              + wrapProse(c.h)
              + (c.src ? codeBlock(c.src, c.tag || 'verified') : '')
              + '</div>';
          }).join('')
        + '</div>';

    /* ---- proof-state trace: the tactic-by-tactic movie ---- */
    case 'trace':
      return '<div class="trace">'
        + '<div class="trace-t"><span class="pin">' + I_PIN + '</span>' + (b.title || 'Proof state, step by step') + '</div>'
        + (b.start ? '<div class="tr-step"><pre class="tr-state">' + esc(b.start) + '</pre></div>' : '')
        + b.steps.map(s =>
            '<div class="tr-step">'
            + (s.tac ? '<div class="tr-tac"><span class="tr-ar">›</span><code>' + esc(s.tac) + '</code></div>' : '')
            + (s.state ? '<pre class="tr-state">' + esc(s.state) + '</pre>' : '')
            + (s.h ? '<div class="tr-note">' + wrapProse(s.h) + '</div>' : '')
            + '</div>').join('')
        + (b.done ? '<div class="tr-done">' + I_CHECK + ' ' + b.done + '</div>' : '')
        + '</div>' + (b.cap ? '<div class="cap">' + b.cap + '</div>' : '');

    /* ---- annotated code ---- */
    case 'anat':
      return '<div class="anat">' + codeBlock(b.src, b.tag || 'verified')
        + '<div class="anat-parts">' + b.parts.map(p =>
            '<div class="anat-p"><span class="anat-m">' + esc(p.m) + '</span><div class="anat-h">' + wrapProse(p.h) + '</div></div>'
          ).join('') + '</div></div>'
        + (b.cap ? '<div class="cap">' + b.cap + '</div>' : '');

    /* ---- collapsible ---- */
    case 'detail':
      return '<details class="detail"' + (b.open ? ' open' : '') + '><summary><span class="tw">' + I_TW + '</span>'
        + (b.title || 'Go deeper')
        + (b.tag ? '<span class="dtag">' + b.tag + '</span>' : '')
        + '</summary><div class="detail-body">' + (b.blocks || []).map(renderBlock).join('') + '</div></details>';

    case 'ex': return renderEx(b);
  }
  return '';
}

/* A field may be a plain HTML string (wrapped in <p>) or an array of blocks. */
function wrapProse(h) {
  if (h == null) return '';
  if (Array.isArray(h)) return h.map(renderBlock).join('');
  return /^\s*<(p|div|ul|ol|details|blockquote|table|pre|h[1-6])[\s>]/i.test(h) ? h : '<p>' + h + '</p>';
}

/* ============ exercises ============ */
function renderEx(b) {
  const done = !!DONE[b.id];
  let h = '<div class="ex' + (done ? ' done' : '') + '" data-ex="' + b.id + '" id="ex-' + b.id + '">';
  h += '<div class="ex-top"><button class="ck" data-ck="' + b.id + '" aria-label="Mark done">' + I_CHECK + '</button><div>';
  h += '<span class="ex-name">' + b.name + '</span>' + (b.hard ? '<span class="ex-tag">substantial</span>' : '');
  if (b.why) h += '<p class="ex-why">' + b.why + '</p>';
  h += '</div></div>';

  let body = '';
  if (b.setup) body += '<div class="ex-setup">' + wrapProse(b.setup) + '</div>';
  if (b.goal) body += codeBlock(b.goal, 'verified');
  /* the live editor: present whenever there is something to prove */
  if (b.goal && window.EditorUI) body += EditorUI.editorHtml(b);
  if (body) h += '<div class="ex-body">' + body + '</div>';

  const hasHint = !!(b.hint || (b.hints && b.hints.length));
  const hasDeep = !!(b.expl || (b.walk && b.walk.length) || (b.deep && b.deep.length) || b.pitfall || b.variants);

  const parts = [];
  if (hasHint) parts.push(['hint', 'Hint']);
  if (b.sol)   parts.push(['sol', 'Solution']);
  if (hasDeep) parts.push(['expl', 'Why it works']);

  if (parts.length) {
    h += '<div class="reveals">';
    parts.forEach(([k, label]) => { h += '<button class="rv ' + k + '" data-rv="' + b.id + ':' + k + '">' + label + '</button>'; });
    h += '</div>';

    parts.forEach(([k]) => {
      let inner = '';

      if (k === 'hint') {
        if (b.hints && b.hints.length) {
          inner = '<div class="hintlist">' + b.hints.map((x, i) =>
            '<div class="hint-i"><span class="hint-n">' + (i + 1) + '</span><div class="hint-h">' + wrapProse(x) + '</div></div>'
          ).join('') + '</div>';
        } else {
          inner = wrapProse(b.hint);
        }
      }

      if (k === 'sol') {
        inner = codeBlock(b.sol, 'verified');
        if (b.solNote) inner += wrapProse(b.solNote);
      }

      if (k === 'expl') {
        if (b.expl) inner += wrapProse(b.expl);
        if (b.walk && b.walk.length) {
          inner += '<div class="walk"><div class="walk-t">Line by line</div>'
            + b.walk.map(w => '<div class="walk-r"><div class="walk-tac">' + esc(w.tac) + '</div>'
                + '<div class="walk-h">' + wrapProse(w.h) + '</div></div>').join('')
            + '</div>';
        }
        if (b.deep && b.deep.length) inner += b.deep.map(renderBlock).join('');
        if (b.pitfall) inner += '<div class="note warn"><span class="ic">' + I_WARN + '</span><div>'
          + '<div class="nt">Where this goes wrong</div><p>' + b.pitfall + '</p></div></div>';
        if (b.variants) inner += '<div class="note info"><span class="ic">' + I_INFO + '</span><div>'
          + '<div class="nt">If you change the statement</div><p>' + b.variants + '</p></div></div>';
      }

      h += '<div class="panel ' + k + '" data-panel="' + b.id + ':' + k + '"><div class="panel-inner">' + inner + '</div></div>';
    });
  }
  h += '</div>';
  return h;
}

/* ============ counting ============ */
const exOf = m => m.blocks.filter(b => b.t === 'ex' && (b.sol || b.goal));
const allEx = () => COURSE.flatMap(exOf);
const doneIn = m => exOf(m).filter(e => DONE[e.id]).length;

/* ============ nav ============ */
function renderNav() {
  const el = document.getElementById('nav');
  let h = '', phase = null;
  COURSE.forEach((m, i) => {
    if (m.phase !== phase) { phase = m.phase; h += '<div class="phase">' + phase + '</div>'; }
    const tot = exOf(m).length, dn = doneIn(m);
    let dots = '';
    if (tot) {
      const shown = Math.min(tot, 10);
      for (let k = 0; k < shown; k++) dots += '<span class="n-dot' + (k < Math.round(dn / tot * shown) ? ' done' : '') + '"></span>';
    }
    h += '<button class="nav-item' + (i === cur ? ' on' : '') + '" data-go="' + i + '">'
      + '<span class="n-num">' + m.num + '</span><span class="n-body"><span class="n-title">' + m.title + '</span>'
      + (tot ? '<span class="n-meta"><span class="n-dots">' + dots + '</span><span class="n-frac">' + dn + '/' + tot + '</span></span>' : '')
      + '</span></button>';
  });
  el.innerHTML = h;
  const total = allEx().length, done = allEx().filter(e => DONE[e.id]).length;
  document.getElementById('pct').textContent = total ? Math.round(done / total * 100) + '%' : '0%';
  document.getElementById('pbar').style.width = total ? (done / total * 100) + '%' : '0%';
  document.getElementById('pcount').textContent = done + ' / ' + total;
}

/* ============ orientation card + in-page TOC ============ */
function renderOrient(o) {
  if (!o) return '';
  let h = '<div class="orient"><div class="orient-grid">';
  h += '<div class="orient-col"><div class="orient-h">' + I_GOAL + 'What you will be able to do</div><ul>'
    + (o.youWill || []).map(x => '<li>' + x + '</li>').join('') + '</ul></div>';
  h += '<div class="orient-col"><div class="orient-h">' + I_NEED + 'What you need first</div><ul>'
    + (o.needs || []).map(x => '<li>' + x + '</li>').join('') + '</ul></div>';
  h += '</div>';
  if (o.payoff) h += '<div class="orient-pay">' + o.payoff + '</div>';
  return h + '</div>';
}

const TOC_LEVEL = { sec: '', h3: 'sub', h4: 'sub2' };

function renderToc(m) {
  const rows = m.blocks.filter(b => b.t in TOC_LEVEL).map(b => [b.s, TOC_LEVEL[b.t]]);
  if (rows.length < 3) return '';
  const links = rows.map(([s, cls]) => '<a class="' + cls + '" href="#">' + strip(s) + '</a>');
  return '<div class="toc"><div class="toc-t">In this chapter</div>' + links.join('') + '</div>';
}

/* ============ lesson ============ */
function renderLesson() {
  const m = COURSE[cur];
  const wrap = document.getElementById('content');

  /* TOC first (it resets hn), then the body with matching slugs */
  const tocHtml = renderToc(m);
  hn = 0;

  let h = '<div class="lead"><div class="kicker">' + m.phase + (m.num !== '§' ? ' · ' + m.num : '') + '</div>'
    + '<h2 class="title">' + m.title + '</h2><p class="blurb">' + m.blurb + '</p></div>';
  h += renderOrient(m.orient);
  h += '<div class="rule"></div>';

  /* build body, capturing heading slugs in order so the TOC can link to them */
  const slugs = [];
  const bodyParts = m.blocks.map(b => {
    const out = renderBlock(b);
    if (b.t in TOC_LEVEL) {
      const mm = out.match(/id="([^"]+)"/);
      if (mm) slugs.push(mm[1]);
    }
    return out;
  });

  let i = 0;
  const toc = tocHtml.replace(/href="#"/g, () => 'href="#' + (slugs[i++] || '') + '"');
  h += toc + bodyParts.join('');

  const prev = COURSE[cur - 1], next = COURSE[cur + 1];
  h += '<div class="pager">'
    + '<button class="pg" data-go="' + (cur - 1) + '"' + (prev ? '' : ' disabled') + '><div class="d">← Previous</div><div class="t">' + (prev ? prev.title : '—') + '</div></button>'
    + '<button class="pg next" data-go="' + (cur + 1) + '"' + (next ? '' : ' disabled') + '><div class="d">Next →</div><div class="t">' + (next ? next.title : '—') + '</div></button>'
    + '</div>';

  wrap.innerHTML = h;

  /* Bring the editors to life, and start Lean warming up in the background the
     moment a chapter with exercises is opened — the reader gets a head start
     on the one slow step while they read the prose. */
  if (window.EditorUI) {
    const exs = m.blocks.filter(b => b.t === 'ex' && b.goal);
    exs.forEach(b => {
      const node = wrap.querySelector('[data-ed="' + b.id + '"]');
      if (node) EditorUI.mountEditor(node, b);
    });
    if (exs.length && window.LeanRuntime && !LeanRuntime.supported()) LeanRuntime.warmup();
  }

  document.getElementById('crumb').innerHTML = m.phase + ' &nbsp;·&nbsp; <b>' + m.title + '</b>';
  document.title = m.num !== '§' ? (m.num + ' · ' + m.title + ' — Separation Logic in Lean')
                                 : (m.title + ' — Separation Logic in Lean');
  window.scrollTo({ top: 0, behavior: 'instant' });
}

function go(i, opts) {
  if (i < 0 || i >= COURSE.length) return;
  cur = i;
  renderLesson(); renderNav();
  if (narrow()) setRail(false);
  Store.set('sl:cur', String(i));
  if (!opts || !opts.silent) history.replaceState(null, '', '#' + COURSE[i].id);
}

/* ============ events ============ */
document.addEventListener('click', async e => {
  const nav = e.target.closest('[data-go]');
  if (nav && !nav.disabled) { go(+nav.dataset.go); return; }

  const ck = e.target.closest('[data-ck]');
  if (ck) {
    const id = ck.dataset.ck;
    DONE[id] = !DONE[id];
    if (!DONE[id]) delete DONE[id];
    document.querySelector('[data-ex="' + id + '"]').classList.toggle('done', !!DONE[id]);
    renderNav();
    await Store.set('sl:done', JSON.stringify(DONE));
    return;
  }

  const rv = e.target.closest('[data-rv]');
  if (rv) {
    const key = rv.dataset.rv;
    const panel = document.querySelector('[data-panel="' + key + '"]');
    const open = panel.classList.toggle('on');
    rv.classList.toggle('on', open);
    return;
  }

  const cp = e.target.closest('.copy');
  if (cp) {
    const node = document.getElementById(cp.dataset.cb);
    try { await navigator.clipboard.writeText(node.innerText); } catch (_) {}
    cp.classList.add('ok'); cp.querySelector('span').textContent = 'Copied';
    setTimeout(() => { cp.classList.remove('ok'); cp.querySelector('span').textContent = 'Copy'; }, 1400);
    return;
  }

  const hit = e.target.closest('.hit');
  if (hit) {
    closeFind(); go(+hit.dataset.i);
    if (hit.dataset.ex) setTimeout(() => {
      const n = document.getElementById('ex-' + hit.dataset.ex);
      if (n) n.scrollIntoView({ block: 'center' });
    }, 60);
    return;
  }
});

/* ---- theme ---- */
const TH_ICON = {
  auto: '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="9"/><path d="M12 3a9 9 0 0 0 0 18Z" fill="currentColor" stroke="none"/></svg>',
  light: '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="12" cy="12" r="4.2"/><path d="M12 2v2.4M12 19.6V22M4.2 4.2l1.7 1.7M18.1 18.1l1.7 1.7M2 12h2.4M19.6 12H22M4.2 19.8l1.7-1.7M18.1 5.9l1.7-1.7"/></svg>',
  dark: '<svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linejoin="round"><path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8Z"/></svg>'
};
function applyTheme() {
  const root = document.documentElement;
  const resolved = THEME === 'auto'
    ? (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light')
    : THEME;
  root.setAttribute('data-theme', resolved);
  document.getElementById('themeLabel').textContent =
    THEME === 'auto' ? 'Auto' : (THEME === 'dark' ? 'Dark' : 'Light');
  const ic = document.getElementById('themeIcon');
  if (ic) ic.innerHTML = TH_ICON[THEME];
  const btn = document.getElementById('theme');
  if (btn) btn.title = 'Theme: ' + THEME + ' — click for ' +
    (THEME === 'auto' ? 'light' : THEME === 'light' ? 'dark' : 'auto');
}
document.getElementById('theme').onclick = () => {
  THEME = THEME === 'auto' ? 'light' : THEME === 'light' ? 'dark' : 'auto';
  applyTheme(); Store.set('sl:theme', THEME);
};

/* ---- reset ---- */
document.getElementById('reset').onclick = async () => {
  DONE = {}; await Store.set('sl:done', '{}'); renderLesson(); renderNav();
};

/* ---- rail (the sidebar) ----
   Hideable at every width, because "wide enough for a sidebar" is not the same
   question as "wants a sidebar" — and a phone reporting a desktop-sized
   viewport should not be stuck with one it cannot dismiss.

   Narrow: it slides over the page, and closes on the dimmed area, the × in its
   corner, Escape, or picking a chapter.
   Wide: it is a column, and the ☰ button collapses it. That choice is
   remembered; the narrow drawer always starts closed. */
const railEl = document.getElementById('rail');
const railScrim = document.getElementById('railScrim');
const appEl = document.querySelector('.app');
/* Drawer mode, not column mode. Width alone is not enough: a phone at a
   larger display-size setting can report a desktop-width viewport, and it
   still wants a drawer. Must stay in step with responsive.css. */
const DRAWER_Q = '(max-width:960px), (pointer:coarse) and (max-width:1400px)';
const narrow = () => matchMedia(DRAWER_Q).matches;
let railOpen = false;

function setRail(open, remember) {
  railOpen = !!open;
  const overlay = railOpen && narrow();
  appEl.dataset.rail = railOpen ? 'open' : 'closed';
  railEl.classList.toggle('on', overlay);
  if (railScrim) railScrim.classList.toggle('on', overlay);
  document.body.classList.toggle('rail-open', overlay);
  if (remember !== false && !narrow()) Store.set('sl:rail', railOpen ? '1' : '0');
}

document.getElementById('railToggle').onclick = () => setRail(!railOpen);
if (railScrim) railScrim.onclick = () => setRail(false);
const railCloseBtn = document.getElementById('railClose');
if (railCloseBtn) railCloseBtn.onclick = () => setRail(false);

/* Crossing the breakpoint (rotating the phone, resizing a window) changes what
   "open" means, so re-derive rather than leaving a drawer stuck open. */
matchMedia(DRAWER_Q).addEventListener('change', () => setRail(!narrow() && railOpen, false));

/* ---- notation drawer ---- */
const drawer = document.getElementById('drawer');
document.getElementById('notation').onclick = () => drawer.classList.add('on');
document.getElementById('drClose').onclick = () => drawer.classList.remove('on');

/* ---- search ---- */
const scrim = document.getElementById('scrim'), finder = document.getElementById('finder'),
  qin = document.getElementById('q'), hits = document.getElementById('hits');
let INDEX = [], selIdx = 0;

/* pull every scrap of searchable text out of a block, recursively */
function blockText(b) {
  if (!b) return '';
  const parts = [b.s, b.h, b.title, b.term, b.src, b.cap, b.name, b.why, b.goal, b.hint, b.expl, b.pitfall, b.variants, b.solNote];
  (b.items || []).forEach(i => parts.push(typeof i === 'string' ? i : (i.k || '') + ' ' + (i.h || '')));
  (b.hints || []).forEach(i => parts.push(i));
  (b.parts || []).forEach(p => parts.push(p.m + ' ' + p.h));
  (b.steps || []).forEach(s => parts.push((s.tac || '') + ' ' + (s.h || '')));
  (b.walk || []).forEach(w => parts.push((w.tac || '') + ' ' + (w.h || '')));
  (b.rows || []).forEach(r => r.forEach(c => parts.push(c)));
  (b.head || []).forEach(c => parts.push(c));
  if (b.left) parts.push(b.left.t + ' ' + b.left.h);
  if (b.right) parts.push(b.right.t + ' ' + b.right.h);
  (b.blocks || []).forEach(x => parts.push(blockText(x)));
  (b.deep || []).forEach(x => parts.push(blockText(x)));
  return parts.filter(x => typeof x === 'string').map(strip).join(' ');
}

function buildIndex() {
  INDEX = [];
  COURSE.forEach((m, i) => {
    INDEX.push({ i, ex: null, title: m.title, sub: m.phase, text: (m.title + ' ' + m.blurb).toLowerCase() });
    m.blocks.forEach(b => {
      if (b.t === 'ex') {
        INDEX.push({
          i, ex: b.id, title: b.name, sub: m.num + ' · ' + m.title,
          text: blockText(b).toLowerCase()
        });
      } else if (b.t === 'h3' || b.t === 'sec' || b.t === 'defn' || b.t === 'detail') {
        INDEX.push({
          i, ex: null, title: strip(b.s || b.term || b.title), sub: m.num + ' · ' + m.title,
          text: blockText(b).toLowerCase()
        });
      }
    });
  });
}
function search(q) {
  q = q.trim().toLowerCase();
  if (!q) return INDEX.slice(0, 14);
  const terms = q.split(/\s+/);
  return INDEX.map(r => {
    let sc = 0;
    for (const t of terms) {
      const inTitle = r.title.toLowerCase().includes(t);
      const inText = r.text.includes(t);
      if (!inTitle && !inText) return null;
      sc += inTitle ? 3 : 1;
    }
    return { r, sc };
  }).filter(Boolean).sort((a, b) => b.sc - a.sc).slice(0, 24).map(x => x.r);
}
function mark(s, q) {
  if (!q.trim()) return s;
  const t = q.trim().split(/\s+/)[0].replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return s.replace(new RegExp('(' + t + ')', 'ig'), '<mark>$1</mark>');
}
function renderHits() {
  const q = qin.value, rows = search(q);
  selIdx = 0;
  hits.innerHTML = rows.length
    ? rows.map((r, k) => '<button class="hit' + (k === 0 ? ' sel' : '') + '" data-i="' + r.i + '"' + (r.ex ? ' data-ex="' + r.ex + '"' : '') + '>'
      + '<div class="h1">' + mark(esc(r.title), q) + '</div><div class="h2">' + esc(r.sub) + '</div></button>').join('')
    : '<div class="noHit">Nothing matches that.</div>';
}
function openFind() { scrim.classList.add('on'); finder.classList.add('on'); qin.value = ''; renderHits(); qin.focus(); }
function closeFind() { scrim.classList.remove('on'); finder.classList.remove('on'); }
document.getElementById('find').onclick = openFind;
scrim.onclick = closeFind;
qin.oninput = renderHits;
qin.onkeydown = e => {
  const list = [...hits.querySelectorAll('.hit')];
  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
    e.preventDefault();
    if (!list.length) return;
    list[selIdx].classList.remove('sel');
    selIdx = (selIdx + (e.key === 'ArrowDown' ? 1 : -1) + list.length) % list.length;
    list[selIdx].classList.add('sel');
    list[selIdx].scrollIntoView({ block: 'nearest' });
  } else if (e.key === 'Enter') { if (list[selIdx]) list[selIdx].click(); }
};

/* ---- keyboard ---- */
document.addEventListener('keydown', e => {
  if (e.key === 'Escape') { closeFind(); drawer.classList.remove('on'); setRail(false); return; }
  const typing = /^(INPUT|TEXTAREA)$/.test(document.activeElement.tagName);
  if (typing) return;
  if (e.key === '/' || (e.key === 'k' && (e.metaKey || e.ctrlKey))) { e.preventDefault(); openFind(); }
  else if (e.key === 'ArrowRight' || e.key === 'j') { go(cur + 1); }
  else if (e.key === 'ArrowLeft' || e.key === 'k') { go(cur - 1); }
  else if (e.key === 'n') { drawer.classList.toggle('on'); }
  else if (e.key === 't') { document.getElementById('theme').onclick(); }
  else if (e.key === 'e') {                       // expand every reveal on the page
    document.querySelectorAll('.panel').forEach(p => p.classList.add('on'));
    document.querySelectorAll('.rv').forEach(b => b.classList.add('on'));
    document.querySelectorAll('details.detail').forEach(d => d.open = true);
  }
});

/* ---- reading progress ---- */
addEventListener('scroll', () => {
  const h = document.body.scrollHeight - innerHeight;
  document.getElementById('read').style.width = h > 0 ? (scrollY / h * 100) + '%' : '0%';
}, { passive: true });

matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { if (THEME === 'auto') applyTheme(); });

/* ---- boot ----
   Called from index.html *after* every content script has registered, so the
   registry is complete before we render. Do not turn this back into an IIFE. */
window.__boot = async function boot() {
  const t = await Store.get('sl:theme'); if (t) THEME = t;
  applyTheme();
  const d = await Store.get('sl:done');
  if (d) { try { DONE = JSON.parse(d) || {}; } catch (_) { DONE = {}; } }

  /* #id in the URL wins over the stored position */
  const hash = location.hash.replace(/^#/, '');
  const byHash = COURSE.findIndex(c => c.id === hash);
  if (byHash >= 0) cur = byHash;
  else {
    const c = await Store.get('sl:cur');
    if (c !== null && !isNaN(+c)) cur = Math.min(+c, COURSE.length - 1);
  }

  /* Wide screens remember whether the sidebar was collapsed; the narrow
     drawer always starts closed. */
  const railPref = await Store.get('sl:rail');
  setRail(!narrow() && railPref !== '0', false);

  buildIndex(); renderLesson(); renderNav();
  if (window.EditorUI) EditorUI.mountLeanStatus();
  if (Store.mode === 'mem') document.getElementById('storeNote').style.display = 'block';
};
