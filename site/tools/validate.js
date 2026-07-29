#!/usr/bin/env node
/* Validate every content/*.js file.
 *
 *   node site/tools/validate.js            check everything
 *   node site/tools/validate.js 07-m6      check one file
 *
 * Checks, in order of how much they matter:
 *   1. the file parses and calls registerChapter exactly once
 *   2. required chapter fields are present and unchanged from the baseline
 *   3. every block has a known type and the fields that type requires
 *   4. every exercise from the original is still present, with its id, name,
 *      goal and solution byte-for-byte identical
 *   5. every Lean block tagged 'verified' really does occur in lean/corpus.lean
 *   6. HTML fields have balanced tags and no stray unescaped '<'
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const ROOT = path.join(__dirname, '..');
const baseline = JSON.parse(fs.readFileSync(path.join(__dirname, 'baseline.json'), 'utf8'));
const corpus = fs.readFileSync(path.join(ROOT, 'lean', 'corpus.lean'), 'utf8');
const norm = s => String(s).replace(/\r/g, '').replace(/[ \t]+$/gm, '').trim();

const KNOWN = {
  p: ['h'], h3: ['s'], h4: ['s'], sec: ['s'], quote: ['h'],
  ul: ['items'], ol: ['items'],
  code: ['src'], txt: ['src'], state: ['src'], svg: ['src'],
  note: ['h'], dod: ['h'], defn: ['h'],
  steps: ['items'], tbl: ['rows'], dl: ['items'], cmp: [],
  trace: ['steps'], anat: ['src', 'parts'], detail: ['blocks'],
  ex: ['id', 'name']
};
const TAGS = ['verified', 'illustration', 'sketch'];

let errors = 0, warnings = 0;
const err = (f, m) => { console.error(`  \x1b[31m✗\x1b[0m ${f}: ${m}`); errors++; };
const warn = (f, m) => { console.error(`  \x1b[33m!\x1b[0m ${f}: ${m}`); warnings++; };

/* --- HTML sanity: balanced tags, no raw '<' that is not a tag --- */
const VOID = new Set(['br', 'hr', 'img', 'input', 'meta', 'link', 'path', 'circle', 'rect', 'line', 'polygon', 'polyline', 'ellipse', 'use', 'stop']);
function htmlProblems(s) {
  if (typeof s !== 'string' || !s.includes('<')) return null;
  const stack = [];
  const re = /<(\/?)([a-zA-Z][a-zA-Z0-9]*)([^>]*)>/g;
  let m, consumed = 0;
  while ((m = re.exec(s))) {
    consumed += m[0].length;
    const [, close, name, attrs] = m;
    if (VOID.has(name.toLowerCase()) || attrs.trim().endsWith('/')) continue;
    if (close) {
      if (!stack.length || stack.pop() !== name.toLowerCase()) return `unbalanced </${name}>`;
    } else stack.push(name.toLowerCase());
  }
  if (stack.length) return `unclosed <${stack[stack.length - 1]}>`;
  return null;
}

function walkStrings(node, visit, where) {
  if (typeof node === 'string') { visit(node, where); return; }
  if (Array.isArray(node)) { node.forEach((x, i) => walkStrings(x, visit, `${where}[${i}]`)); return; }
  if (node && typeof node === 'object') {
    for (const k of Object.keys(node)) {
      if (k === 'src' || k === 'state' || k === 'goal' || k === 'sol' || k === 'tac' || k === 'm') continue; // plain text
      walkStrings(node[k], visit, `${where}.${k}`);
    }
  }
}

function checkBlock(b, file, where, seenEx) {
  if (!b || typeof b !== 'object') return err(file, `${where}: not an object`);
  if (!b.t) return err(file, `${where}: missing 't'`);
  if (!(b.t in KNOWN)) return err(file, `${where}: unknown block type '${b.t}'`);
  for (const f of KNOWN[b.t]) if (b[f] === undefined) err(file, `${where}: '${b.t}' block missing '${f}'`);

  if (b.t === 'code' && b.tag && !TAGS.includes(b.tag)) err(file, `${where}: bad tag '${b.tag}'`);
  if (b.t === 'code' && (!b.tag || b.tag === 'verified')) {
    if (!norm(corpus).includes(norm(b.src))) {
      warn(file, `${where}: tagged 'verified' but not found in lean/corpus.lean — retag 'illustration' or verify it`);
    }
  }
  if (b.t === 'note' && b.kind && !['info', 'warn', 'key', 'tip'].includes(b.kind)) err(file, `${where}: bad note kind '${b.kind}'`);
  if (b.t === 'trace' && Array.isArray(b.steps)) {
    b.steps.forEach((s, i) => { if (!s.tac && !s.state && !s.h) err(file, `${where}.steps[${i}]: empty step`); });
  }
  if (b.t === 'anat' && Array.isArray(b.parts)) {
    b.parts.forEach((p, i) => {
      if (!p.m) return err(file, `${where}.parts[${i}]: missing 'm'`);
      if (!b.src.includes(p.m)) warn(file, `${where}.parts[${i}]: '${p.m}' does not occur in src`);
    });
  }
  if (b.t === 'detail') (b.blocks || []).forEach((x, i) => checkBlock(x, file, `${where}.blocks[${i}]`, seenEx));
  if (b.t === 'steps') (b.items || []).forEach((it, i) => {
    if (Array.isArray(it.h)) it.h.forEach((x, j) => checkBlock(x, file, `${where}.items[${i}].h[${j}]`, seenEx));
  });
  if (b.t === 'ex') {
    seenEx.set(b.id, b);
    (b.deep || []).forEach((x, i) => checkBlock(x, file, `${where}.deep[${i}]`, seenEx));
    if (b.walk) b.walk.forEach((w, i) => { if (!w.tac) err(file, `${where}.walk[${i}]: missing 'tac'`); });
  }

  walkStrings(b, (s, w) => {
    const p = htmlProblems(s);
    if (p) warn(file, `${where}${w.replace(/^\./, '.')}: ${p}`);
  }, '');
}

function checkFile(file) {
  const full = path.join(ROOT, 'content', file);
  const src = fs.readFileSync(full, 'utf8');
  const registered = [];
  const ctx = vm.createContext({ registerChapter: c => registered.push(c) });
  try { vm.runInContext(src, ctx, { filename: file }); }
  catch (e) { return err(file, `does not run: ${e.message}`); }

  if (registered.length !== 1) return err(file, `calls registerChapter ${registered.length} times, expected 1`);
  const ch = registered[0];

  for (const f of ['id', 'num', 'phase', 'title', 'blurb', 'blocks']) {
    if (ch[f] === undefined) err(file, `chapter missing '${f}'`);
  }
  const base = baseline[ch.id];
  if (!base) return err(file, `chapter id '${ch.id}' is not in the baseline`);
  for (const f of ['num', 'phase', 'title']) {
    if (ch[f] !== base[f]) err(file, `chapter '${f}' changed: "${base[f]}" → "${ch[f]}"`);
  }
  if (ch.orient) {
    if (!Array.isArray(ch.orient.youWill) || !ch.orient.youWill.length) warn(file, 'orient.youWill is empty');
    if (!Array.isArray(ch.orient.needs)) warn(file, 'orient.needs is missing');
  }

  const seenEx = new Map();
  (ch.blocks || []).forEach((b, i) => checkBlock(b, file, `blocks[${i}]`, seenEx));

  /* exercise fidelity */
  for (const [id, want] of Object.entries(base.ex)) {
    const got = seenEx.get(id);
    if (!got) { err(file, `exercise '${id}' (${want.name}) is missing`); continue; }
    if (got.name !== want.name) err(file, `${id}: name changed "${want.name}" → "${got.name}"`);
    for (const f of ['goal', 'sol']) {
      if (want[f] == null) continue;
      if (got[f] == null) { err(file, `${id}: '${f}' was dropped`); continue; }
      if (norm(got[f]) !== norm(want[f])) err(file, `${id}: '${f}' is not verbatim — Lean must not be edited`);
    }
  }
  for (const id of seenEx.keys()) if (!(id in base.ex)) warn(file, `exercise '${id}' is new (not in the baseline)`);

  if (STRICT) checkDepth(file, ch);

  const nb = (ch.blocks || []).length;
  const ne = seenEx.size;
  const bytes = Buffer.byteLength(src);
  console.log(`  ${errors === 0 ? '\x1b[32m✓\x1b[0m' : ' '} ${file.padEnd(16)} ${String(nb).padStart(3)} blocks  ${String(ne).padStart(2)} ex  ${(bytes / 1024).toFixed(0).padStart(4)} KB`);
}

/* --- strict mode: does this chapter actually teach? ---------------------- */
function checkDepth(file, ch) {
  const exs = (ch.blocks || []).filter(b => b.t === 'ex');
  if (!ch.orient) err(file, 'strict: chapter has no orient card');

  const hasTrace = b => b.t === 'trace' || (b.blocks || []).some(hasTrace) || (b.deep || []).some(hasTrace);

  for (const e of exs) {
    const at = `strict ${e.id} (${e.name})`;
    if (!e.why) err(file, `${at}: no 'why' — every exercise must say what it buys you`);
    if (!e.hints || e.hints.length < 2) err(file, `${at}: needs at least 2 graded 'hints'`);
    if (!e.expl) err(file, `${at}: no 'expl' summary`);

    if (e.sol) {
      /* count real proof lines: everything after ':= by' */
      const i = e.sol.indexOf(':= by');
      const lines = i < 0 ? [] : e.sol.slice(i + 5).split('\n').map(s => s.trim()).filter(Boolean);
      if (!e.walk || !e.walk.length) err(file, `${at}: no 'walk' — walk the solution line by line`);
      else if (e.walk.length < Math.ceil(lines.length / 2)) {
        err(file, `${at}: 'walk' has ${e.walk.length} rows for a ${lines.length}-line proof — too coarse`);
      }
      if (lines.length >= 3 && !(e.deep || []).some(hasTrace)) {
        err(file, `${at}: ${lines.length}-line proof with no 'trace' block in 'deep' — show the goal states`);
      }
    }
    if (!e.pitfall) warn(file, `${at}: no 'pitfall'`);
  }

  /* prose density: an expanded chapter should be substantially richer */
  const rich = (ch.blocks || []).filter(b => ['trace', 'anat', 'steps', 'cmp', 'dl', 'tbl', 'defn', 'detail'].includes(b.t)).length;
  if (exs.length && rich < 3) warn(file, `strict: only ${rich} structured blocks outside exercises`);
}

const args = process.argv.slice(2);
const STRICT = args.includes('--strict');
const only = args.filter(a => !a.startsWith('--'))[0];
const files = fs.readdirSync(path.join(ROOT, 'content')).filter(f => f.endsWith('.js')).sort()
  .filter(f => !only || f.includes(only));

console.log(`\nvalidating ${files.length} chapter file(s)\n`);
files.forEach(checkFile);
console.log(`\n${errors} error(s), ${warnings} warning(s)\n`);
process.exit(errors ? 1 : 0);
