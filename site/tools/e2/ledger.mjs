#!/usr/bin/env node
/* The ledger check: nothing may be used before it has been introduced.
 *
 *   node site/tools/e2/ledger.mjs                  check every content/*.js
 *   node site/tools/e2/ledger.mjs 16-star          check one file
 *   node site/tools/e2/ledger.mjs --json           machine-readable
 *   node site/tools/e2/ledger.mjs --audit          is the ledger still true?
 *   node site/tools/e2/ledger.mjs --no-prose       Lean blocks only
 *   node site/tools/e2/ledger.mjs --strict-names   promote unknown-name warnings
 *   node site/tools/e2/ledger.test.mjs             run it over Edition 1
 *
 * WHY THIS EXISTS. Edition 1's second chapter expects the reader to parse
 *
 *     rcases hd l₁ with h | h <;> · rw [singleton_same] at h; exact absurd h (by simp)
 *
 * in which `rcases`, `<;>`, `·`, `;` and `absurd` all appear for the first time
 * with no introduction. That is not a slip; it is what happens when the reading
 * order lives only in an author's head. Edition 2 writes it down — COURSE-PLAN.md
 * §E, the global ledger — and this tool mechanises it. `ledger.json` is §E as
 * data: every tactic, keyword, syntactic form, library name and course-internal
 * lemma, with the FILE (NN-id) that first introduces it.
 *
 * Three checks, in descending order of how much they matter:
 *
 *   1. ORDER.   An item used in NN-x whose ledger row says MM-y with MM > NN is
 *               an error. This is the rule the whole edition exists to keep.
 *   2. EXISTENCE. A course-internal lemma may be cited only if it is declared in
 *               site/lean/e2/ at or before the citing unit's own fragment. This
 *               is what would have caught Edition 1 citing `self_disjoint_empty`,
 *               a lemma that does not exist. If site/lean/e2/ is empty or partial
 *               the check degrades to a warning against lean/corpus.lean and says
 *               so, rather than crashing or lying.
 *   3. COVERAGE. A name that looks like a citation but has no ledger row is a
 *               warning: either a plan gap or a typo, and both are worth seeing.
 *
 * WHAT IT READS. Every scrap of Lean in a chapter: code.src, txt.src, state.src,
 * anat.src and anat.parts[].m, ex.goal, ex.sol, ex.walk[].tac, trace.start,
 * trace.steps[].tac and .state, cmp.left/right.src, and everything nested inside
 * detail.blocks[], ex.deep[] and steps.items[].h. Plus the <code> spans of the
 * prose, because §E's rule is about mentioning, not only about compiling — see
 * false-positive class (g). Comments and string literals are blanked first. A
 * name DECLARED in a file is not a use of it, and neither are the binders of
 * that file's own proofs.
 *
 * The fourth check, `--audit`, points the other way: it compares every
 * `internal` ledger row against site/lean/e2/, so that when the Lean moves the
 * ledger is told about it. §H.8 of the plan is titled "The ledger drifts".
 *
 * THE RULE FOR ADDING AN EXEMPTION. Every class below makes the tool quieter,
 * and quieter is how a check dies. So: an exemption must be paid for by naming
 * what it stopped reporting. If you cannot name that, you do not yet understand
 * what you are exempting, and you are not ready to add it.
 *
 * The worked example is class (j). Quoting a Lean error message in prose was
 * firing order errors on the keywords inside it — `instance`, `Decidable` —
 * which are Lean talking, not the author citing, and `06-errors` exists to
 * print twelve such messages. Exempting them was obviously right. But paying
 * the price first — running Edition 1 and listing what went silent — showed the
 * exemption also killed five real findings, among them `00-overview` displaying
 * a typeclass-synthesis failure on page one, an exhibit §D had independently
 * decided must move to `07-heap`. Five true positives for one convenience is a
 * bad trade and it would have been invisible a week later.
 *
 * So the mechanism changed instead of the trade being accepted: class (j)
 * DOWNGRADES to a `diagnostic` warning rather than silencing. The five findings
 * are still reported, reclassified, and `06-errors` is still writable. The test
 * that caught it is the one to copy — before adding an exemption, run
 * `ledger.test.mjs` before and after and read the difference.
 *
 * KNOWN FALSE-POSITIVE CLASSES — read these before you switch the tool off:
 *
 *   a. `cases`. §E books three different forms of it in three different units
 *      (`cases h : e with` at 02, bare inversion and `cases h with | ctor` at
 *      19). The token is booked at the earliest, so a bare `cases h` inversion
 *      used before unit 19 is missed — a false NEGATIVE, not a positive.
 *   b. `subst` is both a tactic (unit 08) and the assertion transformer defined
 *      in unit 22. Booked at the earlier; the transformer is unchecked.
 *   c. `state` blocks are goal displays, not author-written Lean. A goal that
 *      mentions `Heap.union` is evidence about the proof, not a citation the
 *      reader must already understand — but it is still reported, flavour
 *      `display`, because usually it does mean the unit is out of place.
 *      `⊢` is special-cased: only the INFIX use (something to its left on the
 *      line) counts as the entailment notation of unit 12.
 *   d. `txt` blocks are deliberately schematic pseudo-notation with invented
 *      placeholder names. Order checks apply; the name-existence check does not.
 *   e. Shape rows like "explicit binder (x : T)" and "implicit binder {x : T}"
 *      are matched by regex and also fire on type ascriptions and on structure
 *      instance literals. Both are booked at or before the shape they collide
 *      with, so the collision is silent — but a regex row is never as sharp as
 *      a name row, and `--json` marks which is which (`via: "re"`).
 *   f. Binder collection over-approximates: every `| ident` at the start of a
 *      line is treated as a constructor/pattern binder, which also swallows
 *      `rcases … with a | b`. Over-collecting only makes the tool quieter.
 *   g. PROSE FORWARD REFERENCES. §E's rule is that an item below your row "does
 *      not exist yet and must not be mentioned", so the `<code>` spans of the
 *      prose are checked too — that is where Edition 1 cites the nonexistent
 *      `self_disjoint_empty`. But a roadmap paragraph ("Unit 28 proves this")
 *      is a legitimate mention, and it is the single largest false-positive
 *      class. A chapter that means it declares
 *
 *          registerChapter({ …, ledgerForward: ['wp', 'lseg'], … })
 *
 *      and those names pass in prose only. `--no-prose` turns the pass off.
 *      The same hatch covers prose that names a lemma in order to say it does
 *      NOT exist — Edition 1's `union_eq_none` walk says "there is no
 *      `union_eq_some`", and the tool cannot hear the negation.
 *   h. DELIBERATE EXHIBITS. A chapter that shows a banned tactic failing, or
 *      prints a `sorry`, is using the thing on purpose. `ledgerAllow: [...]`
 *      on the chapter object waives named items in every block of that chapter.
 *   j. QUOTED LEAN DIAGNOSTICS. A `<code>` span holding a real error message —
 *      "failed to synthesize instance of type class …" — contains keywords the
 *      author is not citing. `06-errors` exists to print twelve of them. Lines
 *      of prose that came out of a span matching DIAGNOSTIC below are exempt
 *      from `keyword` and `command` rows, and from those only: a lemma name in
 *      `simp?` output is still a citation, and so is `∗`.
 *   i. `simp?` output quoted verbatim in a chapter cites Lean core simp lemmas
 *      (`ne_eq`, `Option.some.injEq`, `decide_eq_true_eq`, …). Those are not in
 *      the ledger and cannot be; CORE below lists the ones the course actually
 *      quotes, and anything else lands in the unknown-name WARNING bucket, not
 *      the error bucket, unless it is a near-miss of a real course lemma.
 *
 * No dependencies, no build step. Exits non-zero on any error.
 */
import fs from 'fs';
import path from 'path';
import vm from 'vm';
import { fileURLToPath, pathToFileURL } from 'url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const SITE = path.join(HERE, '..', '..');

/* Lean core names a chapter may cite without a ledger row. Kept short on
   purpose: every addition is a decision that the reader is expected to know a
   name the course never taught them. */
const CORE = new Set(`
rfl trivial id absurd funext congrArg congrFun propext Classical Decidable DecidableEq
Eq Eq.symm Eq.trans Eq.mp Eq.mpr Eq.refl Eq.subst Ne Ne.symm Ne.intro Not
Iff Iff.rfl Iff.intro Iff.mp Iff.mpr And And.intro And.left And.right Or Or.inl Or.inr
Or.symm Or.elim Exists Exists.intro True False True.intro False.elim
Prop Sort Type Nat Bool Option Unit List String Char Int Prod Sigma Subtype Fin Empty
Nat.succ Nat.zero Nat.succ_ne_zero Nat.le_refl Nat.le_trans Nat.lt_irrefl Nat.pred
Nat.add_zero Nat.zero_add Nat.succ_sub_one Nat.sub_zero Nat.sub_self Nat.le_of_lt_succ
Nat.lt_succ_of_le Nat.le_succ Nat.le_max_left Nat.le_max_right Nat.max_def
Option.some Option.none Option.some.inj Option.some.injEq Option.noConfusion Option.isSome
List.length List.append List.nil List.cons List.length_cons List.length_nil
Bool.true Bool.false Bool.noConfusion decide ite dite if_pos if_neg if_true if_false
ne_eq not_false_eq_true not_true_eq_false eq_self_iff_true decide_eq_true_eq
beq_iff_eq eq_comm and_true true_and or_false false_or and_self imp_self
Function Function.comp Repr Inhabited Nonempty
`.trim().split(/\s+/));

/* ------------------------------------------------------------------ loading */

const loadLedger = (file) => {
  const L = JSON.parse(fs.readFileSync(file, 'utf8'));
  L.index = new Map(L.order.map((u, i) => [u, i]));
  L.byName = new Map();
  L.shapes = [];
  for (const e of L.entries) {
    if (e.check === false) continue;
    if (e.re) { e.rx = new RegExp(e.re, (e.flags || '') + 'g'); L.shapes.push(e); continue; }
    for (const n of [e.name, ...(e.aliases || [])]) {
      if (!L.byName.has(n)) L.byName.set(n, []);
      L.byName.get(n).push(e);
    }
  }
  return L;
};

/* Every declaration name the verified Lean knows about, and where. Prefers the
   Edition-2 fragments; falls back, loudly, to the Edition-1 corpus. */
const DECL = /^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|partial[ \t]+)*(theorem|lemma|def|abbrev|instance|structure|inductive|opaque|axiom)[ \t]+([^\s({[:]+)/gm;

function leanUniverse() {
  const decls = new Map();          // name -> unit id (or null when unknown)
  const e2 = path.join(SITE, 'lean', 'e2');
  const frags = fs.existsSync(e2) ? fs.readdirSync(e2).filter(f => f.endsWith('.lean')).sort() : [];
  /* `def write` inside `namespace Heap` is cited as `Heap.write`, so record
     both. Namespaces do not nest in this corpus, but closing is by `end`. */
  const scan = (text, unit) => {
    let ns = [];
    for (const line of text.split('\n')) {
      const open = line.match(/^\s*namespace\s+([A-Za-z_][\w'.]*)/);
      if (open) { ns.push(open[1]); continue; }
      if (/^\s*end\b/.test(line)) { ns.pop(); continue; }
      for (const m of line.matchAll(DECL)) {
        const short = m[2];
        if (!decls.has(short)) decls.set(short, unit);
        if (ns.length) {
          const q = ns.join('.') + '.' + short;
          if (!decls.has(q)) decls.set(q, unit);
        }
      }
    }
  };
  if (frags.length) {
    for (const f of frags) scan(fs.readFileSync(path.join(e2, f), 'utf8'), f.replace(/\.lean$/, ''));
    return { mode: 'e2', decls, frags, last: frags[frags.length - 1].replace(/\.lean$/, '') };
  }
  const corpus = path.join(SITE, 'lean', 'corpus.lean');
  if (fs.existsSync(corpus)) scan(fs.readFileSync(corpus, 'utf8'), null);
  const ed2 = path.join(SITE, 'lean', 'edition2');
  if (fs.existsSync(ed2)) for (const f of fs.readdirSync(ed2).filter(f => f.endsWith('.lean')))
    scan(fs.readFileSync(path.join(ed2, f), 'utf8'), null);
  return { mode: 'fallback', decls, frags: [], last: null };
}

function chaptersOf(dir, files) {
  const out = [];
  for (const f of files) {
    const got = [];
    const ctx = vm.createContext({ registerChapter: (c) => got.push(c), console });
    try { vm.runInContext(fs.readFileSync(path.join(dir, f), 'utf8'), ctx, { filename: f }); }
    catch (e) { out.push({ file: f, error: e.message }); continue; }
    for (const c of got) out.push({ file: f, chapter: c });
  }
  return out;
}

/* ---------------------------------------------------------------- harvesting */

/* flavour: 'lean' author-written Lean · 'display' a goal Lean printed ·
   'schematic' a txt block, pseudo-notation */
function harvest(ch) {
  const out = [];
  const put = (p, flavour, text) => { if (typeof text === 'string' && text.trim()) out.push({ path: p, flavour, text }); };

  const block = (b, p) => {
    if (!b || typeof b !== 'object') return;
    switch (b.t) {
      case 'code': put(p + '.src', 'lean', b.src); break;
      case 'txt': put(p + '.src', 'schematic', b.src); break;
      case 'state': put(p + '.src', 'display', b.src); break;
      case 'anat':
        put(p + '.src', 'lean', b.src);
        (b.parts || []).forEach((q, i) => put(`${p}.parts[${i}].m`, 'lean', q.m));
        break;
      case 'trace':
        put(p + '.start', 'display', b.start);
        (b.steps || []).forEach((s, i) => {
          put(`${p}.steps[${i}].tac`, 'lean', s.tac);
          put(`${p}.steps[${i}].state`, 'display', s.state);
        });
        put(p + '.done', 'display', b.done);
        break;
      case 'cmp':
        for (const side of ['left', 'right']) if (b[side]) put(`${p}.${side}.src`, 'lean', b[side].src);
        break;
      case 'detail': (b.blocks || []).forEach((x, i) => block(x, `${p}.blocks[${i}]`)); break;
      case 'steps': (b.items || []).forEach((it, i) => {
        if (Array.isArray(it.h)) it.h.forEach((x, j) => block(x, `${p}.items[${i}].h[${j}]`));
      }); break;
      case 'ex': {
        const q = `${p}(${b.id})`;
        put(q + '.goal', 'lean', b.goal);
        put(q + '.sol', 'lean', b.sol);
        (b.walk || []).forEach((w, i) => put(`${q}.walk[${i}].tac`, 'lean', w.tac));
        (b.deep || []).forEach((x, i) => block(x, `${q}.deep[${i}]`));
        break;
      }
      default: /* prose, tables, svg: not Lean */ break;
    }
  };
  (ch.blocks || []).forEach((b, i) => block(b, `blocks[${i}]`));

  /* §E: an item below your row "does not exist yet and must not be mentioned".
     So the <code> spans of the prose count too — that is where Edition 1 cites
     `self_disjoint_empty`, a lemma that does not exist. Only name rows are
     applied to prose; a code span is a fragment, not a syntactic context. */
  const PLAIN = new Set(['src', 'state', 'goal', 'sol', 'tac', 'm', 'start', 'done']);
  const spans = (node, p, acc) => {
    if (typeof node === 'string') {
      for (const m of node.matchAll(/<code[^>]*>([\s\S]*?)<\/code>/g)) acc.push(unhtml(m[1]));
      return;
    }
    if (Array.isArray(node)) return node.forEach((x, i) => spans(x, p, acc));
    if (node && typeof node === 'object')
      for (const k of Object.keys(node)) if (!PLAIN.has(k)) spans(node[k], p, acc);
  };
  const prose = (node, path) => {
    const acc = [];
    spans(node, '', acc);
    if (!acc.length) return;
    /* Which lines of the joined text came out of a quoted Lean diagnostic.
       `06-errors` exists to print twelve of them, and every one is full of
       words like `instance` and `structure` that are Lean talking, not the
       author citing. See false-positive class (j). */
    const diag = new Set(), bare = new Set();
    let line = 1;
    for (const span of acc) {
      const n = span.split('\n').length;
      if (DIAGNOSTIC.test(span)) for (let k = 0; k < n; k++) diag.add(line + k);
      /* a span that is one bare word, with no arguments and no punctuation:
         `<code>right</code>` is naming a thing, not invoking a tactic */
      if (n === 1 && /^[A-Za-z_][A-Za-z0-9_']*$/.test(span.trim())) bare.add(line);
      line += n;
    }
    out.push({ path, flavour: 'prose', text: acc.join('\n'), diag, bare });
  };
  (ch.blocks || []).forEach((b, i) => prose(b, `blocks[${i}]<code>`));
  prose(ch.orient || {}, 'orient<code>');
  return out;
}

/* The opening words of a Lean 4 message. Deliberately anchored on stems that do
   not occur in ordinary prose about Lean. */
const DIAGNOSTIC = new RegExp([
  'failed to synthesize', 'type mismatch', 'unknown identifier', 'unknown constant',
  'unsolved goals', 'has already been declared', 'function expected',
  'numerals are polymorphic', 'motive is not type correct', 'fail to show termination',
  "declaration uses 'sorry'", 'invalid field notation', 'maximum recursion depth',
  'deterministic timeout', 'simp made no progress', 'unexpected token',
  'could not synthesize', 'ambiguous, possible interpretations',
  'error:', 'warning:',
  /* continuation lines of a multi-part message, anchored so ordinary prose
     beginning "note" is not swept up */
  '^\\s*note:', '^\\s*hint:', 'but is expected to have type'
].join('|'), 'im');

const ENT = { lt: '<', gt: '>', amp: '&', quot: '"', nbsp: ' ', hellip: '…', apos: "'", '#39': "'" };
const unhtml = (s) => s
  .replace(/<[^>]*>/g, '')
  .replace(/&(#?\w+);/g, (m, e) => (e in ENT ? ENT[e] : m));

/* ------------------------------------------------------------------ scanning */

/* Blank comments and string literals, keeping every offset so line numbers in
   the report still point at the right place. */
function strip(src) {
  const a = src.split('');
  const blank = (i, j) => { for (; i < j; i++) if (a[i] !== '\n') a[i] = ' '; };
  for (let i = 0; i < src.length; i++) {
    if (src[i] === '/' && src[i + 1] === '-') {           // /- … -/, nested
      let d = 1, j = i + 2;
      while (j < src.length && d) {
        if (src[j] === '/' && src[j + 1] === '-') { d++; j += 2; }
        else if (src[j] === '-' && src[j + 1] === '/') { d--; j += 2; }
        else j++;
      }
      blank(i, j); i = j - 1;
    } else if (src[i] === '-' && src[i + 1] === '-') {    // -- to end of line
      let j = src.indexOf('\n', i); if (j < 0) j = src.length;
      blank(i, j); i = j - 1;
    } else if (src[i] === '"') {                          // "…"
      let j = i + 1;
      while (j < src.length && src[j] !== '"') j += src[j] === '\\' ? 2 : 1;
      blank(i, Math.min(j + 1, src.length)); i = j;
    }
  }
  return a.join('');
}

const IDS = 'A-Za-z_\\u0370-\\u03FF\\u00C0-\\u024F';
const IDC = IDS + "0-9'\\u2080-\\u209C\\u271D";
const ID_RE = new RegExp(`[${IDS}][${IDC}]*(?:\\.[${IDS}0-9][${IDC}]*)*`, 'g');
/* what a tactic may sit immediately after */
const TACTIC_AFTER = /(^|\n|;|·|\||>|\(|\{|=>|\bby|\bthen|\belse|\bdo)$/;

function tokenise(text) {
  const out = [];
  for (const m of text.matchAll(ID_RE)) {
    const before = text.slice(0, m.index).replace(/[ \t]+$/, '');
    out.push({
      name: m[0], at: m.index,
      dotted: m[0].includes('.'),
      afterDot: before.endsWith('.'),
      tactic: TACTIC_AFTER.test(before)
    });
  }
  return out;
}

const lineOf = (text, at) => text.slice(0, at).split('\n').length;

/* Names a file declares or binds, which are therefore not citations. */
const BINDERS = [
  /\b(?:theorem|lemma|def|abbrev|instance|structure|inductive|opaque|axiom)\s+([^\s({[:]+)/g,
  /^[ \t]*\|\s*([^\n=]*?)(?:=>|$)/gm,
  /\bhave\s+([A-Za-z_][^\s:=]*)/g,
  /\b(?:by_cases|cases)\s+([A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*)\s*:/g,
  /\bintro\s+([^\n]*)/g, /\brintro\s+([^\n]*)/g,
  /\bobtain\s+([^\n]*?):=/g,
  /\brcases\b[^\n]*?\bwith\b([^\n]*)/g,
  /\bfun\s+([^\n=]*)=>/g,
  /\bcase\s+([^\n=]*?)(?:=>|$)/gm,
  /\bnext\s+([^\n=]*)=>/g,
  /\brename_i\s+([^\n]*)/g,
  /\bgeneralizing\s+([^\n]*)/g,
  /\bwith\s*\|\s*([^\n=]*)=>/g,
  /[(){]\s*([^():{}\n]+?)\s*:[^=]/g,            // binder groups (a b : T), {a : T}
  /^[ \t]+([A-Za-z_][A-Za-z0-9_']*)\s*:(?!=)/gm, // structure / inductive fields
  /^[ \t]+([A-Za-z_][A-Za-z0-9_']*)\s*:=/gm,     // `where` instance fields
  /[∀∃]\s*([^,\n]*),/g,
  /\blet\s+([A-Za-z_][^\s:=]*)/g
];
function localNames(texts) {
  const s = new Set();
  for (const t of texts) for (const re of BINDERS) {
    for (const m of t.matchAll(re)) for (const w of (m[1] || '').matchAll(ID_RE)) s.add(w[0]);
  }
  return s;
}

/* is `name` a plausible citation of a declaration, as opposed to a bound
   variable, a word out of a quoted error message, or an inaccessible name Lean
   invented (`refine_1`, `x_1`, `u_1`)? */
const citationish = (n) =>
  !/^_/.test(n) && !/_\d+$/.test(n) &&
  (n.includes('.') || n.includes('_') || /^[A-Z][A-Za-z0-9]*[a-z][A-Za-z0-9]*[A-Z]/.test(n));

/* a name close enough to a real one to be a typo rather than a library name we
   have never heard of. Longest shared prefix wins, and it has to be a real
   prefix — four characters and a whole underscore-segment. */
function nearMiss(name, universe) {
  let best = null, bestLen = 0;
  const seg = (s, n) => s.split('_').slice(0, n).join('_');
  for (const other of universe) {
    if (other === name || other.includes('.')) continue;
    let i = 0;
    while (i < name.length && i < other.length && name[i] === other[i]) i++;
    if (i < 4 || i <= bestLen) continue;
    if (!(name.startsWith(seg(other, 2)) || other.startsWith(seg(name, 2)))) continue;
    best = other; bestLen = i;
  }
  return best;
}

/* -------------------------------------------------------------------- checks */

export function run(opts = {}) {
  const contentDir = opts.contentDir || path.join(SITE, 'content');
  const L = loadLedger(opts.ledger || path.join(HERE, 'ledger.json'));
  const lean = opts.leanUniverse || leanUniverse();
  const strictNames = !!opts.strictNames;
  const only = opts.only;

  let files = fs.readdirSync(contentDir).filter(f => f.endsWith('.js')).sort();
  if (only) files = files.filter(f => f.includes(only));

  /* content file -> ledger unit. Identity for Edition 2; the test supplies a
     mapping for Edition 1, whose chapters are not ledger units. */
  const unitOf = (f) => {
    const base = f.replace(/\.js$/, '');
    if (opts.map && base in opts.map) return opts.map[base];
    if (opts.map && !opts.mapPartial) return null;
    return L.index.has(base) ? base : null;
  };

  const findings = [];
  const notes = [];
  let checked = 0;
  const idx = (u) => (L.index.has(u) ? L.index.get(u) : -1);
  const fenceAt = idx(L.fence.unit);
  const maxFrag = lean.last ? idx(lean.last) : -1;

  if (lean.mode === 'fallback') {
    notes.push('site/lean/e2/ is empty — the existence check is running against lean/corpus.lean ' +
      'and lean/edition2/*.lean, which have no unit order. Citation-order errors are reported as ' +
      'warnings; rerun once the fragments exist.');
  } else if (maxFrag >= 0 && maxFrag < L.order.length - 3) {
    notes.push(`site/lean/e2/ has ${lean.frags.length} fragment(s), the last being ${lean.last}. ` +
      'Existence is only checked for names the ledger places at or before that point.');
  }

  for (const { file, chapter, error } of chaptersOf(contentDir, files)) {
    const base = file.replace(/\.js$/, '');
    if (error) { findings.push({ file: base, path: '-', severity: 'error', rule: 'load', msg: `does not run: ${error}` }); continue; }
    const unit = unitOf(file);
    if (unit === null) { notes.push(`${base}: no ledger unit — skipped`); continue; }
    const here = idx(unit);
    checked++;

    let scraps = harvest(chapter).map(s => {
      const t = { ...s, clean: strip(s.text) };
      /* a `state` block usually holds a goal, but sometimes holds a quoted
         compiler error — `error: … / Note: … inductive type with a single
         constructor`. Either way it is Lean talking, so grammar in it is not a
         citation. Prose spans get this per span; a state block is one unit. */
      if (t.flavour === 'display' && DIAGNOSTIC.test(t.text)) {
        t.diag = new Set(t.text.split('\n').map((_, i) => i + 1));
      }
      return t;
    });
    if (opts.noProse) scraps = scraps.filter(s => s.flavour !== 'prose');
    /* Two escape hatches, both declared on the chapter object, both by name so
       that a reviewer can see exactly what was waived.
         ledgerForward — prose only: a roadmap ("Unit 28 proves this"), or a
                         name mentioned in order to say it does NOT exist
                         ("there is no `union_eq_some`").
         ledgerAllow   — everywhere: a deliberate exhibit, such as showing
                         `omega` failing on `Loc`, or displaying a `sorry`. */
    const forward = new Set(chapter.ledgerForward || []);
    const allow = new Set(chapter.ledgerAllow || []);
    /* A waiver that no longer suppresses anything is a waiver that has rotted —
       a renamed ledger row, or an exhibit that was edited out. Say so. */
    const waived = new Set();
    const declared = localNames(scraps.filter(s => s.flavour !== 'display').map(s => s.clean));
    for (const b of chapter.blocks || []) if (b.t === 'ex' && b.name) declared.add(b.name);

    /* one row per (file, rule, item): the first site, plus a count. A report
       that lists ⊢ a hundred and sixty times is a report nobody reads. */
    const seenHere = new Map();
    const report = (s, at, o) => {
      const key = `${o.rule}|${o.entryKind || ''}|${o.name}`;
      const hit = seenHere.get(key);
      if (hit) { hit.count++; if (hit.also.length < 3) hit.also.push(`${s.path}:${lineOf(s.text, at)}`); return; }
      const f = {
        file: base, unit, path: s.path, flavour: s.flavour,
        line: lineOf(s.text, at), count: 1, also: [], ...o
      };
      seenHere.set(key, f);
      findings.push(f);
    };

    for (const s of scraps) {
      /* --- shape rows (regexes) --- */
      if (s.flavour !== 'prose') for (const e of L.shapes) {
        e.rx.lastIndex = 0;
        let m, seen = 0;
        while ((m = e.rx.exec(s.clean)) && seen < 4) {
          seen++;
          orderCheck(e, s, m.index, 're');
          if (e.rx.lastIndex === m.index) e.rx.lastIndex++;
        }
      }

      /* --- name rows --- */
      const toks = tokenise(s.clean);
      const firstSeen = new Set();
      for (const t of toks) {
        if (t.afterDot) continue;
        /* `Exec.seq` is a constructor of `Exec`: the ledger books the type, and
           a constructor is not a separate thing to introduce. */
        let rows = L.byName.get(t.name);
        if (!rows && t.dotted) {
          const parent = L.byName.get(t.name.split('.')[0]);
          if (parent && parent.some(e => e.kind === 'internal')) rows = parent.filter(e => e.kind === 'internal');
        }
        if (rows) {
          for (const e of rows) {
            if (e.kind === 'tactic' && !t.tactic && s.flavour !== 'prose') continue;
            /* Grammar quoted inside a Lean message is Lean talking, not the
               author citing — so it is not an ORDER error. But a unit that
               displays a diagnostic about a construct the reader has not met is
               still showing them something they cannot read, which is a real
               editorial question. Downgraded, never silenced. */
            if (s.diag && (e.kind === 'keyword' || e.kind === 'command') &&
                s.diag.has(lineOf(s.text, t.at))) {
              const there = idx(e.unit);
              if (there > here && !allow.has(e.name)) report(s, t.at, {
                severity: 'warn', rule: 'diagnostic', name: e.name, entryKind: e.kind,
                introducedIn: e.unit,
                msg: `a Lean message displayed here mentions \`${e.name}\`, which ${e.unit} introduces — not a citation, but is this exhibit in the right unit?`
              });
              else if (there > here) waived.add(e.name);
              continue;
            }
            /* a row flagged `english` is a word before it is a tactic; alone in
               a prose span it is naming something, not citing the tactic */
            if (s.bare && e.english && s.bare.has(lineOf(s.text, t.at))) continue;
            if (e.kind === 'internal' && declared.has(t.name)) continue;
            const key = e.kind + ' ' + e.name;
            if (firstSeen.has(key)) continue;
            firstSeen.add(key);
            orderCheck(e, s, t.at, 'name');
            if (e.kind === 'internal') existenceCheck(e, s, t);
          }
          continue;
        }
        /* --- coverage: a citation with no ledger row --- */
        if (s.flavour === 'display' || s.flavour === 'schematic') continue;
        if (!citationish(t.name) || CORE.has(t.name) || declared.has(t.name)) continue;
        if (allow.has(t.name)) { waived.add(t.name); continue; }
        if (s.flavour === 'prose' && forward.has(t.name)) { waived.add(t.name); continue; }
        /* in prose only a near-miss of a real lemma is worth saying anything about */
        if (s.flavour === 'prose' && (lean.decls.has(t.name) || !/^[a-z][A-Za-z0-9']*(_[A-Za-z0-9']+)+$/.test(t.name))) continue;
        if (t.dotted && !/^[A-Z]/.test(t.name)) continue;      // dot notation on a term
        if (t.dotted && CORE.has(t.name.split('.')[0])) continue;
        const key = 'unknown ' + t.name;
        if (firstSeen.has(key)) continue;
        firstSeen.add(key);
        const known = lean.decls.has(t.name);
        if (known) {
          report(s, t.at, {
            severity: 'warn', rule: 'coverage', name: t.name,
            msg: `declared in the Lean but has no ledger row — add one to §E or it will drift`
          });
        } else {
          const miss = /^[a-z][A-Za-z0-9']*(_[A-Za-z0-9']+)+$/.test(t.name)
            ? nearMiss(t.name, lean.decls.keys()) : null;
          report(s, t.at, {
            severity: miss || strictNames ? 'error' : 'warn',
            rule: miss ? 'existence' : 'coverage', name: t.name,
            msg: miss
              ? `cited but declared nowhere in the verified Lean — did you mean \`${miss}\`?`
              : `not in the ledger and not declared in the verified Lean (Lean core? then add it to CORE)`
          });
        }
      }
    }

    for (const [n, field] of [...[...allow].map(n => [n, 'ledgerAllow']), ...[...forward].map(n => [n, 'ledgerForward'])]) {
      if (waived.has(n)) continue;
      findings.push({
        file: base, unit, path: field, flavour: '', line: 0, count: 1, also: [],
        severity: 'warn', rule: 'waiver', name: n,
        msg: `${field} lists it, but nothing in this chapter would have fired on it — stale waiver, or a ledger row that has been renamed`
      });
    }

    function orderCheck(e, s, at, via) {
      /* A waiver only counts as USED once we know the row would have fired.
         Testing `allow` first would mark every waiver used and defeat the
         stale-waiver check — which is the whole point of having one. */
      const waive = () => { waived.add(e.name); return true; };
      const suppressed = (kind) =>
        (allow.has(e.name) && waive()) ||
        (kind === 'order' && s.flavour === 'prose' && forward.has(e.name) && waive());

      /* An Edition-1 name for something the fragments carry under an Edition-2
         name. Worth its own row: "does not exist" would send the author
         hunting for a lemma that is sitting right there. */
      if (e.renamedTo) {
        if (suppressed('renamed')) return;
        return report(s, at, {
          severity: 'error', rule: 'renamed', name: e.name, via, entryKind: e.kind,
          introducedIn: e.unit,
          msg: `renamed: cite \`${e.renamedTo}\` instead${e.notes ? ' — ' + e.notes : ''}`
        });
      }
      if (e.banned) {
        if (suppressed('banned')) return;
        return report(s, at, { severity: 'error', rule: 'banned', name: e.name, via, entryKind: e.kind, msg: e.banned });
      }
      const there = idx(e.unit);
      if (there < 0) return;
      if (there > here) {
        if (suppressed('order')) return;
        return report(s, at, {
          severity: 'error', rule: 'order', name: e.name, via, entryKind: e.kind,
          introducedIn: e.unit,
          msg: `${e.kind} \`${e.name}\` is introduced in ${e.unit}, used here in ${unit}`
        });
      }
      if (e.fenced && here > fenceAt) {
        if (suppressed('fence')) return;
        return report(s, at, {
          severity: 'error', rule: 'fence', name: e.name, via, entryKind: e.kind, introducedIn: e.unit,
          msg: `\`${e.name}\` comes from ${e.unit}, which §E.6 declares optional — no later unit may rely on it`
        });
      }
    }

    function existenceCheck(e, s, t) {
      const name = e.name;                       // the ledger's name, not the constructor's
      if (declared.has(name) || e.renamedTo) return;
      const exempt = () =>
        (allow.has(name) && (waived.add(name), true)) ||
        (s.flavour === 'prose' && forward.has(name) && (waived.add(name), true));
      /* an order error already said this, in the ledger's words */
      if (seenHere.has(`order|internal|${name}`)) return;
      const where = lean.decls.get(name);
      if (lean.mode === 'fallback') {
        if (!lean.decls.has(name)) report(s, t.at, {
          severity: 'warn', rule: 'existence', name,
          msg: 'no such declaration in lean/corpus.lean or lean/edition2/*.lean (degraded check: site/lean/e2/ is empty)'
        });
        return;
      }
      if (where === undefined) {
        if (idx(e.unit) > maxFrag) return;         // the fragments do not reach here yet
        /* Some rows are known not to be in a fragment, and why. §D's exhibits
           cannot compile, its ⧗ items are unwritten, and a handful of real
           lemmas are still sitting in Edition-1 content awaiting migration. */
        /* `display` can never compile; `illustration` compiles against its own
           unit's prelude but is deliberately not corpus. Neither belongs in a
           fragment, so neither is missing from one. */
        if (e.status === 'display' || e.status === 'illustration') return;
        if (exempt()) return;
        const soft = { migrate: 'not in a fragment yet — the Lean is real but still lives in Edition-1 content', todo: '§D marks this ⧗: nobody has written it yet' };
        report(s, t.at, {
          severity: e.status in soft ? 'warn' : 'error', rule: 'existence', name,
          msg: e.status in soft ? soft[e.status] : 'cited, but no fragment in site/lean/e2/ declares it'
        });
        return;
      }
      if (idx(where) > here && !exempt()) report(s, t.at, {
        severity: 'error', rule: 'existence', name, introducedIn: where,
        msg: `declared in the Lean only at ${where}, cited here in ${unit}`
      });
    }
  }

  if (!checked) notes.push('NOTHING WAS CHECKED: no content file matched a ledger unit. ' +
    'Edition-2 chapters are named after the ledger (site/content/16-star.js ↔ 16-star); until they ' +
    'exist, run site/tools/e2/ledger.test.mjs, which maps Edition 1 onto the ledger.');

  /* Cheap (79 KB of Lean), so it runs every time. A blind spot nobody is
     assigned to remember is a blind spot that grows. */
  const sw = sweep(opts);
  return {
    findings, notes, lean: { mode: lean.mode, fragments: lean.frags.length },
    sweep: { declared: sw.declared.length, used: sw.used.length, names: [...sw.declared, ...sw.used].map(x => x.name).slice(0, 12) },
    checked, files: files.length, ledger: L.entries.length
  };
}

/* ------------------------------------------------------------------- audit */

/* Is the ledger itself still true? Compares every `internal` row against the
   Lean fragments it claims to come from. Run it after either side moves. */
export function audit(opts = {}) {
  const L = loadLedger(opts.ledger || path.join(HERE, 'ledger.json'));
  const lean = leanUniverse();
  const out = [];
  if (lean.mode !== 'e2') return { mode: lean.mode, rows: [], note: 'site/lean/e2/ is empty — nothing to audit against' };
  const inLedger = new Set(L.entries.filter(e => e.kind === 'internal').map(e => e.name));
  /* `Heap.write` in the ledger covers `def write` inside `namespace Heap` */
  for (const n of [...inLedger]) if (n.includes('.')) inLedger.add(n.split('.').pop());
  for (const e of L.entries) if (e.check === false) inLedger.add(e.name);
  for (const e of L.entries) {
    if (e.kind !== 'internal') continue;
    const where = lean.decls.get(e.name);
    if (where === undefined) out.push({
      name: e.name, ledger: e.unit, lean: null, status: e.status || 'unexplained',
      ...(e.renamedTo ? { renamedTo: e.renamedTo } : {}),
      msg: e.status
        ? `no fragment declares it (${e.status}): ${e.notes || ''}`
        : 'in the ledger, declared in no fragment, and no reason recorded'
    });
    else if (where !== e.unit) out.push({ name: e.name, ledger: e.unit, lean: where, msg: `ledger says ${e.unit}, the Lean says ${where}` });
  }
  for (const [name, where] of lean.decls) {
    if (name.includes('.') || inLedger.has(name) || CORE.has(name)) continue;
    out.push({ name, ledger: null, lean: where, msg: `declared in ${where}, no ledger row` });
  }
  return { mode: lean.mode, rows: out };
}

/* --------------------------------------------------------------------- sweep */

/* The check's own blind spot, made routine.
 *
 * A name with no ledger row is INVISIBLE: the order check has nothing to
 * compare, and the coverage warning only fires on tokens that look like
 * citations — so a lowercase name with no underscore (`absurd`, `trivial`,
 * `ite`) is silently unpoliced. That is how §E.1's `absurd` row went missing
 * for the whole project without a single check failing.
 *
 * This cannot be fixed by making the checker cleverer, because the evidence it
 * would need is exactly what is absent. It can only be fixed by reading the
 * verified Lean and asking, of every name in it, whether the ledger knows.
 * Forty-one units are still to land fragments, so it runs on every invocation
 * and prints its count whether or not anything else fails.
 */
const LEAN_KW = new Set(`
theorem lemma def abbrev instance structure inductive example where by fun with at in
match do let have show from this if then else for open import universe variable section
namespace end attribute protected private noncomputable partial mutual deriving extends
termination_by decreasing_by set_option macro notation infix infixl infixr prefix postfix
class abbrev_def out_param sorry admit calc generalizing using to obtain rcases rintro only
intro exact simp rfl cases refine induction funext unfold subst rwa simpa apply constructor
left right rw trivial_ac
`.trim().split(/\s+/));

export function sweep(opts = {}) {
  const L = loadLedger(opts.ledger || path.join(HERE, 'ledger.json'));
  const rows = new Set();
  for (const e of L.entries) { rows.add(e.name); for (const a of e.aliases || []) rows.add(a); }
  for (const n of [...rows]) if (n.includes('.')) rows.add(n.split('.').pop());
  /* Core syntax is tracked by SHAPE, not by name: `fun` and `by` have no rows
     of their own, they are covered by `fun x => e` and `:= by` via their `re`
     field. Matching on name alone would report every such construct as missing
     and tempt someone into adding a duplicate row that then disagrees with the
     shape row. So a token is covered if a shape row matches the text across it. */
  const covered = (n) => rows.has(n) ||
    (n.includes('.') && rows.has(n.split('.')[0]));      // a constructor of a rowed type
  const coveredByShape = (text, at, len) => {
    for (const e of L.shapes) {
      e.rx.lastIndex = 0;
      let m;
      while ((m = e.rx.exec(text))) {
        if (m.index <= at && at + len <= m.index + m[0].length) return true;
        if (m.index > at + len) break;
        if (e.rx.lastIndex === m.index) e.rx.lastIndex++;
      }
    }
    return false;
  };

  const dir = path.join(SITE, 'lean', 'e2');
  if (!fs.existsSync(dir)) return { mode: 'none', declared: [], used: [] };
  const frags = fs.readdirSync(dir).filter(f => f.endsWith('.lean')).sort();

  /* everything the fragments declare, and everything they bind */
  const decls = new Map();
  const bound = new Set();
  const texts = [];
  for (const f of frags) {
    const unit = f.replace(/\.lean$/, '');
    const clean = strip(fs.readFileSync(path.join(dir, f), 'utf8'));
    texts.push({ unit, clean });
    let ns = [];
    for (const line of clean.split('\n')) {
      const o = line.match(/^\s*namespace\s+([A-Za-z_][\w'.]*)/);
      if (o) { ns.push(o[1]); continue; }
      if (/^\s*end\b/.test(line)) { ns.pop(); continue; }
      for (const m of line.matchAll(DECL)) {
        if (!decls.has(m[2])) decls.set(m[2], unit);
        if (ns.length && !decls.has(ns.join('.') + '.' + m[2])) decls.set(ns.join('.') + '.' + m[2], unit);
      }
    }
    for (const n of localNames([clean])) bound.add(n);
  }

  const declared = [], used = [], seen = new Set();
  for (const [name, unit] of decls) {
    if (covered(name) || name.includes('.')) continue;   // qualified form follows the short one
    declared.push({ name, unit });
  }
  for (const { unit, clean } of texts) {
    for (const t of tokenise(clean)) {
      const n = t.name;
      if (t.afterDot || seen.has(n)) continue;
      if (covered(n) || decls.has(n) || bound.has(n) || LEAN_KW.has(n)) continue;
      /* `s.heap`, `h.elim`, `K.op`: dot notation on a bound term, not a name */
      if (n.includes('.') && (!/^[A-Z]/.test(n) || bound.has(n.split('.')[0]))) continue;
      if (n.length < 3 && !/[A-Z]/.test(n)) continue;
      if (coveredByShape(clean, t.at, n.length)) continue;
      seen.add(n);
      used.push({ name: n, unit });
    }
  }
  declared.sort((a, b) => a.name.localeCompare(b.name));
  used.sort((a, b) => a.name.localeCompare(b.name));
  return { mode: 'e2', fragments: frags.length, declared, used };
}

/* --------------------------------------------------------------------- cli */

const C = { r: '\x1b[31m', y: '\x1b[33m', d: '\x1b[2m', b: '\x1b[1m', x: '\x1b[0m' };

export function report(res, json) {
  if (json) { console.log(JSON.stringify(res, null, 1)); return res.findings.some(f => f.severity === 'error') ? 1 : 0; }
  const errs = res.findings.filter(f => f.severity === 'error');
  const warns = res.findings.filter(f => f.severity === 'warn');
  console.log(`\nledger: ${res.ledger} rows · ${res.checked}/${res.files} file(s) checked · lean universe: ${res.lean.mode} (${res.lean.fragments} fragments)`);
  if (res.sweep) {
    const n = res.sweep.declared + res.sweep.used;
    console.log(n === 0
      ? `sweep:  ${C.d}every name in the verified Lean has a ledger row${C.x}`
      : `sweep:  ${C.y}${n} name(s) in the verified Lean have NO ledger row${C.x} — ${res.sweep.names.join(', ')}${n > 12 ? ' …' : ''}  ${C.d}(node ledger.mjs --sweep)${C.x}`);
  }
  console.log('');
  for (const n of res.notes) console.log(`  ${C.d}${n}${C.x}`);
  if (res.notes.length) console.log('');

  let file = null;
  for (const f of res.findings) {
    if (f.file !== file) { file = f.file; console.log(`${C.b}${file}${C.x}`); }
    const mark = f.severity === 'error' ? `${C.r}✗${C.x}` : `${C.y}!${C.x}`;
    const at = `${f.path}${f.line ? ':' + f.line : ''}`;
    const more = f.count > 1 ? `${C.d} (+${f.count - 1} more)${C.x}` : '';
    console.log(`  ${mark} ${C.d}${(f.flavour || '').padEnd(9)}${C.x} ${at}${more}`);
    console.log(`      ${f.name ? '`' + f.name + '` — ' : ''}${f.msg}`);
  }
  const by = {};
  for (const f of res.findings) by[f.rule] = (by[f.rule] || 0) + 1;
  console.log(`\n${errs.length} error(s), ${warns.length} warning(s)  ${C.d}${JSON.stringify(by)}${C.x}\n`);
  return errs.length ? 1 : 0;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const args = process.argv.slice(2);
  const only = args.filter(a => !a.startsWith('--'))[0];
  if (args.includes('--sweep')) {
    const r = sweep();
    if (args.includes('--json')) { console.log(JSON.stringify(r, null, 1)); process.exit(0); }
    console.log(`\nsweep: ${r.fragments} fragment(s) in site/lean/e2\n`);
    for (const d of r.declared) console.log(`  ${C.r}✗${C.x} ${d.name.padEnd(28)} declared in ${d.unit}, no ledger row`);
    for (const u of r.used) console.log(`  ${C.y}!${C.x} ${u.name.padEnd(28)} used in ${u.unit}, no ledger row and declared nowhere`);
    const n = r.declared.length + r.used.length;
    console.log(n === 0
      ? `\n  ${C.d}every name in the verified Lean has a row. The ledger can police all of it.${C.x}\n`
      : `\n${n} name(s) with no ledger row — each is a name the ledger cannot police\n`);
    process.exit(r.declared.length ? 1 : 0);
  }
  if (args.includes('--audit')) {
    const a = audit();
    if (args.includes('--json')) { console.log(JSON.stringify(a, null, 1)); process.exit(0); }
    console.log(`\nledger vs site/lean/e2 (${a.mode})\n`);
    for (const r of a.rows) console.log(`  ${C.y}!${C.x} ${r.name.padEnd(34)} ${r.msg}`);
    console.log(`\n${a.rows.length} disagreement(s)\n`);
    process.exit(0);
  }
  process.exit(report(run({
    only,
    strictNames: args.includes('--strict-names'),
    noProse: args.includes('--no-prose')
  }), args.includes('--json')));
}
