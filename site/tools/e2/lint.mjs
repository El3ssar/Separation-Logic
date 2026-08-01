#!/usr/bin/env node
/* Structural lint for Edition-2 chapter files.
 *
 *   node site/tools/e2/lint.mjs              every content/*.js
 *   node site/tools/e2/lint.mjs 16-star      one file
 *   node site/tools/e2/lint.mjs --quiet      errors only
 *
 * Edition 1's validate.js checks each chapter against tools/baseline.json — a
 * frozen record of the first edition. Edition 2 has no baseline yet (it becomes
 * one once the course exists), so this checks the things that are true of a
 * good chapter regardless of edition:
 *
 *   1. the file parses and calls registerChapter exactly once
 *   2. required chapter fields, and id matching the file name
 *   3. every block has a known type and the fields that type requires
 *   4. every exercise carries the full teaching apparatus PEDAGOGY.md demands
 *   5. exercise ids are unique across the whole course
 *   6. Lean tagged 'verified' really occurs in the verified fragments at or
 *      before this unit — the Edition-2 analogue of the corpus fidelity check,
 *      and the thing that stops an author quoting Lean nobody compiled
 *   7. HTML fields have balanced tags
 *
 * It does NOT check that the Lean compiles (site/tools/e2/verify.sh does) or
 * that nothing is used before it is introduced (site/tools/e2/ledger.mjs does).
 */
import fs from 'fs';
import path from 'path';
import vm from 'vm';
import { fileURLToPath } from 'url';

const SITE = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const CONTENT = path.join(SITE, 'content');
const FRAGS = path.join(SITE, 'lean', 'e2');

const args = process.argv.slice(2);
const QUIET = args.includes('--quiet');
const only = args.filter(a => !a.startsWith('--'))[0];

let errors = 0, warnings = 0;
const err = (f, m) => { console.error(`  \x1b[31m✗\x1b[0m ${f}: ${m}`); errors++; };
const warn = (f, m) => { if (!QUIET) console.error(`  \x1b[33m!\x1b[0m ${f}: ${m}`); warnings++; };

/* ---- the sidebar badge ----
   `num` is the UNIT number, not the file prefix. They coincide for the first six
   files and then never again, because the five support pages take a file slot
   and a '§' badge rather than a number. An author who copies the file prefix
   into `num` ships a sidebar that skips 01 and 06 and reads as broken, and
   nothing else would catch it: the plan gives every unit a `file` and a `phase`
   and never mentions `num`. So it is derived here, once, and checked. */
const SUPPORT = new Set(['01-goalstate', '06-errors', '20-compare', '42-tactics', '43-ref']);
const BADGE = (() => {
  const order = JSON.parse(fs.readFileSync(path.join(SITE, 'tools', 'e2', 'ledger.json'), 'utf8')).order;
  const map = {};
  let unit = 0;
  for (const id of order) map[id] = SUPPORT.has(id) ? '§' : String(unit++).padStart(2, '0');
  return map;
})();

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
const norm = s => String(s).replace(/\r/g, '').replace(/[ \t]+$/gm, '').trim();

/* ---- the verified Lean available up to and including a given file ---- */
function fragmentsUpTo(num) {
  if (!fs.existsSync(FRAGS)) return null;
  const files = fs.readdirSync(FRAGS).filter(f => f.endsWith('.lean')).sort();
  const use = files.filter(f => parseInt(f.slice(0, 2), 10) <= num);
  return use.map(f => fs.readFileSync(path.join(FRAGS, f), 'utf8')).join('\n');
}

/* ---- HTML sanity ---- */
const VOID = new Set(['br', 'hr', 'img', 'input', 'meta', 'link', 'path', 'circle', 'rect',
  'line', 'polygon', 'polyline', 'ellipse', 'use', 'stop', 'text', 'g', 'defs', 'marker']);
function htmlProblems(s) {
  if (typeof s !== 'string' || !s.includes('<')) return null;
  const stack = [];
  const re = /<(\/?)([a-zA-Z][a-zA-Z0-9]*)([^>]*)>/g;
  let m;
  while ((m = re.exec(s))) {
    const [, close, name, attrs] = m;
    if (VOID.has(name.toLowerCase()) || attrs.trim().endsWith('/')) continue;
    if (close) { if (!stack.length || stack.pop() !== name.toLowerCase()) return `unbalanced </${name}>`; }
    else stack.push(name.toLowerCase());
  }
  if (stack.length) return `unclosed <${stack[stack.length - 1]}>`;
  return null;
}

const PLAIN = new Set(['src', 'state', 'goal', 'sol', 'tac', 'm']);
function walkStrings(node, visit, where) {
  if (typeof node === 'string') return visit(node, where);
  if (Array.isArray(node)) return node.forEach((x, i) => walkStrings(x, visit, `${where}[${i}]`));
  if (node && typeof node === 'object') {
    for (const k of Object.keys(node)) {
      if (PLAIN.has(k)) continue;
      walkStrings(node[k], visit, `${where}.${k}`);
    }
  }
}

/* ---- exercises: the apparatus PEDAGOGY.md requires ---- */
function checkExercise(e, file, where, ctx) {
  const at = `${where} ${e.id} (${e.name})`;
  /* The Lean an exercise shows must be Lean somebody compiled. An author who
     writes a new exercise adds it to the unit's fragment; one who quotes an
     existing theorem finds it there already. Either way it must be present. */
  if (e.sol && ctx.lean !== null && !norm(ctx.lean).includes(norm(e.sol))) {
    err(file, `${at}: 'sol' does not occur in the verified fragments up to ${ctx.numStr} — compile it with tools/e2/check.sh and add it to lean/e2/${ctx.numStr}-*.lean`);
  }
  if (e.goal && ctx.lean !== null && !norm(ctx.lean).includes(norm(e.goal).replace(/\s*:=\s*by\s*$/, ''))) {
    warn(file, `${at}: 'goal' does not occur verbatim in the verified fragments — check it is the real statement`);
  }
  if (!e.id) return err(file, `${where}: exercise with no id`);
  if (!e.name) err(file, `${at}: no name`);
  if (!e.why) err(file, `${at}: no 'why' — every exercise must say what it buys the reader`);

  /* A design exercise has no Lean by intent and must say so in its own text. */
  const design = !e.goal && !e.sol;
  if (design) {
    if (!/project|design|sketch|no lean|on paper|open-ended/i.test(String(e.why) + String(e.setup || ''))) {
      err(file, `${at}: no goal and no sol, and nothing marks it as a design exercise`);
    }
    if (!e.hints || e.hints.length < 2) err(file, `${at}: a design exercise still needs graded hints`);
    return;
  }

  if (!e.goal) err(file, `${at}: has a solution but no 'goal' — the reader needs a statement to prove`);
  if (!e.sol) err(file, `${at}: has a goal but no 'sol'`);
  if (!e.hints || e.hints.length < 2) err(file, `${at}: needs at least 2 graded hints (nudge → near-giveaway)`);
  if (!e.expl) err(file, `${at}: no 'expl' summary`);
  if (!e.pitfall) warn(file, `${at}: no 'pitfall' — name the mistake a reader will actually make`);

  if (e.sol) {
    const i = e.sol.indexOf(':= by');
    const lines = i < 0 ? [] : e.sol.slice(i + 5).split('\n').map(s => s.trim()).filter(Boolean);
    if (!e.walk || !e.walk.length) {
      if (lines.length) err(file, `${at}: no 'walk' — walk the solution line by line`);
    } else if (e.walk.length < Math.ceil(lines.length / 2)) {
      err(file, `${at}: 'walk' has ${e.walk.length} rows for a ${lines.length}-line proof — too coarse`);
    }
    const hasTrace = b => b && (b.t === 'trace' || (b.blocks || []).some(hasTrace) || (b.deep || []).some(hasTrace));
    if (lines.length >= 3 && !(e.deep || []).some(hasTrace)) {
      err(file, `${at}: ${lines.length}-line proof with no 'trace' in 'deep' — show the goal states`);
    }
  }
  (e.walk || []).forEach((w, i) => { if (!w.tac) err(file, `${at}: walk[${i}] has no 'tac'`); });
}

function checkBlock(b, file, where, ctx) {
  if (!b || typeof b !== 'object') return err(file, `${where}: not an object`);
  if (!b.t) return err(file, `${where}: missing 't'`);
  if (!(b.t in KNOWN)) return err(file, `${where}: unknown block type '${b.t}'`);
  for (const f of KNOWN[b.t]) if (b[f] === undefined) err(file, `${where}: '${b.t}' block missing '${f}'`);

  if (b.t === 'code') {
    if (b.tag && !TAGS.includes(b.tag)) err(file, `${where}: bad tag '${b.tag}'`);
    if ((!b.tag || b.tag === 'verified') && ctx.lean !== null) {
      if (!norm(ctx.lean).includes(norm(b.src))) {
        err(file, `${where}: tagged 'verified' but not found in the verified fragments up to ${ctx.numStr} — retag 'illustration' and check it with tools/e2/check.sh, or add it to the fragment`);
      }
    }
  }
  /* anat and cmp carry Lean too, and their tags are the same truth claim. */
  if (b.t === 'anat' && (!b.tag || b.tag === 'verified') && ctx.lean !== null) {
    if (!norm(ctx.lean).includes(norm(b.src))) {
      err(file, `${where}: anat tagged 'verified' but not in the verified fragments up to ${ctx.numStr}`);
    }
  }
  if (b.t === 'cmp') {
    for (const side of ['left', 'right']) {
      const c = b[side];
      if (c && c.src && (!c.tag || c.tag === 'verified') && ctx.lean !== null) {
        if (!norm(ctx.lean).includes(norm(c.src))) {
          err(file, `${where}.${side}: tagged 'verified' but not in the verified fragments up to ${ctx.numStr}`);
        }
      }
    }
  }
  if (b.t === 'note' && b.kind && !['info', 'warn', 'key', 'tip'].includes(b.kind)) {
    err(file, `${where}: bad note kind '${b.kind}'`);
  }
  if (b.t === 'trace' && Array.isArray(b.steps)) {
    b.steps.forEach((s, i) => { if (!s.tac && !s.state && !s.h) err(file, `${where}.steps[${i}]: empty step`); });
    if (!b.steps.some(s => s.state)) warn(file, `${where}: a trace with no goal states shown`);
  }
  if (b.t === 'anat' && Array.isArray(b.parts)) {
    b.parts.forEach((p, i) => {
      if (!p.m) return err(file, `${where}.parts[${i}]: missing 'm'`);
      if (!b.src.includes(p.m)) err(file, `${where}.parts[${i}]: '${p.m}' does not occur in src`);
    });
  }
  if (b.t === 'detail') (b.blocks || []).forEach((x, i) => checkBlock(x, file, `${where}.blocks[${i}]`, ctx));
  if (b.t === 'steps') (b.items || []).forEach((it, i) => {
    if (Array.isArray(it.h)) it.h.forEach((x, j) => checkBlock(x, file, `${where}.items[${i}].h[${j}]`, ctx));
  });
  if (b.t === 'ex') {
    if (ctx.seenEx.has(b.id)) err(file, `${where}: duplicate exercise id '${b.id}' (also in ${ctx.seenEx.get(b.id)})`);
    else ctx.seenEx.set(b.id, file);
    checkExercise(b, file, where, ctx);
    (b.deep || []).forEach((x, i) => checkBlock(x, file, `${where}.deep[${i}]`, ctx));
  }

  walkStrings(b, (s, w) => {
    const p = htmlProblems(s);
    if (p) err(file, `${where}${w}: ${p}`);
  }, '');
}

function checkFile(file, seenEx) {
  const src = fs.readFileSync(path.join(CONTENT, file), 'utf8');
  const registered = [];
  const ctx0 = vm.createContext({ registerChapter: c => registered.push(c) });
  try { vm.runInContext(src, ctx0, { filename: file }); }
  catch (e) { return err(file, `does not run: ${e.message}`); }

  if (registered.length !== 1) return err(file, `calls registerChapter ${registered.length} times, expected 1`);
  const ch = registered[0];

  for (const f of ['id', 'num', 'phase', 'title', 'blurb', 'blocks']) {
    if (ch[f] === undefined) err(file, `chapter missing '${f}'`);
  }
  const expectId = file.replace(/^\d+-/, '').replace(/\.js$/, '');
  if (ch.id !== expectId) err(file, `chapter id '${ch.id}' does not match its file name (expected '${expectId}')`);

  const fileId = file.replace(/\.js$/, '');
  const badge = BADGE[fileId];
  if (badge === undefined) warn(file, `not in the course order — no sidebar badge could be derived`);
  else if (ch.num !== badge) {
    err(file, `num is '${ch.num}' but this file's sidebar badge is '${badge}'. `
      + `num is the UNIT number, not the file prefix: the five support pages take a file slot and a '§' badge, `
      + `so the two stop coinciding after 06-errors.`);
  }
  if (!ch.orient) err(file, 'no orient card');
  else {
    if (!Array.isArray(ch.orient.youWill) || !ch.orient.youWill.length) err(file, 'orient.youWill is empty');
    if (!Array.isArray(ch.orient.needs)) err(file, 'orient.needs is missing');
    if (!ch.orient.payoff) warn(file, 'orient.payoff is missing');
  }

  const num = parseInt(file.slice(0, 2), 10);
  const ctx = { seenEx, lean: fragmentsUpTo(num), numStr: file.slice(0, 2) };
  (ch.blocks || []).forEach((b, i) => checkBlock(b, file, `blocks[${i}]`, ctx));

  const nb = (ch.blocks || []).length;
  const ne = (ch.blocks || []).filter(b => b.t === 'ex').length;
  const kb = (Buffer.byteLength(src) / 1024).toFixed(0);
  if (!QUIET) console.log(`  ${file.padEnd(24)} ${String(nb).padStart(3)} blocks  ${String(ne).padStart(2)} ex  ${kb.padStart(4)} KB`);
}

const files = fs.existsSync(CONTENT)
  ? fs.readdirSync(CONTENT).filter(f => f.endsWith('.js')).sort().filter(f => !only || f.includes(only))
  : [];

if (!files.length) { console.error('no chapter files found'); process.exit(1); }
if (!fs.existsSync(FRAGS)) console.error('  (no site/lean/e2 fragments yet — skipping the verified-Lean check)\n');

console.log(`\nlinting ${files.length} chapter file(s)\n`);
const seenEx = new Map();
files.forEach(f => checkFile(f, seenEx));
console.log(`\n${errors} error(s), ${warnings} warning(s), ${seenEx.size} exercises\n`);
process.exit(errors ? 1 : 0);
