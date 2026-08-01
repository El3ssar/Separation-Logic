#!/usr/bin/env node
/* Build the Lean context the browser checks a reader's proof against.
 *
 *   node site/tools/e2/gen-contexts.mjs           report only, writes nothing
 *   node site/tools/e2/gen-contexts.mjs --write   write the two files
 *
 * When a reader presses Check, editor.js splices `lean/context.lean` — cut at
 * that exercise's entry in `lean/context-index.json` — in front of whatever they
 * typed, and runs the result through the WASM kernel. So the cut has to fall
 * after everything the course has established and BEFORE that exercise's own
 * solution. Get it wrong in one direction and the reader is missing a lemma the
 * page told them to use; get it wrong in the other and Lean answers "has already
 * been declared" instead of checking their proof.
 *
 * Edition 1 found each cut by searching the corpus for the solution text, with
 * three fallbacks for when that failed. Edition 2 does not have to guess: every
 * fragment carries an explicit
 *
 *     /- ex <id> <name> -/
 *
 * line before the declaration that answers that exercise, written when the
 * corpus was assembled. The marker IS the cut point. That turns a fuzzy search
 * into a lookup, and makes a missing marker a loud error rather than a silently
 * wrong context.
 *
 * The context is the concatenation of site/lean/e2/*.lean in course order, which
 * is the same text tools/e2/verify.sh compiles as one file. If verify.sh passes,
 * every prefix of it that ends at a declaration boundary compiles too.
 */
import fs from 'fs';
import path from 'path';
import vm from 'vm';
import { fileURLToPath } from 'url';

const SITE = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const FRAGS = path.join(SITE, 'lean', 'e2');
const CONTENT = path.join(SITE, 'content');
const WRITE = process.argv.includes('--write');

/* ---- the corpus, in course order, with every marker's offset ---- */
const files = fs.readdirSync(FRAGS).filter(f => f.endsWith('.lean')).sort();
let corpus = '';
const marks = new Map();               // exercise id -> character offset of its cut
const dupes = [];

for (const f of files) {
  const text = fs.readFileSync(path.join(FRAGS, f), 'utf8');
  const base = corpus.length;
  const re = /^[ \t]*\/-[ \t]*ex[ \t]+(\S+)[ \t]+([^-]*?)-\/[ \t]*$/gm;
  let m;
  while ((m = re.exec(text))) {
    const id = m[1];
    if (marks.has(id)) dupes.push(`${id} (again in ${f})`);
    else marks.set(id, base + m.index);
  }
  corpus += text;
  if (!corpus.endsWith('\n')) corpus += '\n';
  corpus += '\n';
}

/* ---- the exercises, from the chapters ---- */
const E1 = /^(00-overview|01-m0|02-m1|03-m2|04-m3|05-m4|06-m5|07-m6|08-m7|09-m8|10-m9|11-m10|12-m11|13-m12|14-m13|15-m14|16-ref)\.js$/;
const chapters = [];
const ctx = vm.createContext({ registerChapter: c => chapters.push(c) });
for (const f of fs.readdirSync(CONTENT).filter(f => f.endsWith('.js') && !E1.test(f)).sort()) {
  vm.runInContext(fs.readFileSync(path.join(CONTENT, f), 'utf8'), ctx, { filename: f });
}

const index = {};
const missing = [];
const design = [];
let exCount = 0;

for (const ch of chapters) {
  for (const b of ch.blocks || []) {
    if (b.t !== 'ex') continue;
    exCount++;
    if (!b.sol) { design.push(`${ch.id}/${b.id}`); continue; }   // design exercise: no Lean
    const cut = marks.get(b.id);
    if (cut === undefined) { missing.push(`${ch.id}/${b.id} (${b.name})`); continue; }
    index[b.id] = cut;
  }
}

/* ---- report ---- */
const kb = (corpus.length / 1024).toFixed(0);
console.log(`\ncontext      ${files.length} fragments, ${kb} KB, ${corpus.split('\n').length} lines`);
console.log(`markers      ${marks.size} in the Lean`);
console.log(`exercises    ${exCount} in ${chapters.length} chapter(s): ${Object.keys(index).length} indexed, ${design.length} design, ${missing.length} unmatched`);

let bad = 0;
if (dupes.length) {
  console.error(`\n  \x1b[31m✗\x1b[0m duplicate ex markers — one exercise cannot have two cuts:`);
  dupes.forEach(d => console.error(`      ${d}`));
  bad += dupes.length;
}
if (missing.length) {
  console.error(`\n  \x1b[31m✗\x1b[0m exercises with a solution but no /- ex … -/ marker in the Lean.`);
  console.error(`      Without a marker the reader gets the WHOLE corpus as context, which contains`);
  console.error(`      the answer, so Lean says "has already been declared" instead of checking them.`);
  console.error(`      Add the marker to site/lean/e2/<unit>.lean just above the declaration.`);
  missing.forEach(x => console.error(`      ${x}`));
  bad += missing.length;
}

/* Every cut must land on a declaration boundary, or the prefix will not compile.
   The marker is a comment on its own line, so the character before it is a
   newline unless the file is malformed. */
for (const [id, cut] of Object.entries(index)) {
  if (cut > 0 && corpus[cut - 1] !== '\n') {
    console.error(`  \x1b[31m✗\x1b[0m ${id}: cut at ${cut} is mid-line, not at a declaration boundary`);
    bad++;
  }
}

/* An exercise's own solution must be absent from its context and present after
   it — the two failure directions, checked rather than assumed. */
let leaks = 0;
for (const ch of chapters) {
  for (const b of ch.blocks || []) {
    if (b.t !== 'ex' || !b.sol || index[b.id] === undefined) continue;
    const head = corpus.slice(0, index[b.id]);
    const name = (b.sol.match(/^\s*(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_.'’]*)/m) || [])[1];
    if (name && new RegExp(`^\\s*(theorem|lemma|def|abbrev)\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b`, 'm').test(head)) {
      console.error(`  \x1b[31m✗\x1b[0m ${b.id}: '${name}' is already declared in its own context — the cut is too late`);
      leaks++;
    }
  }
}
bad += leaks;

if (design.length) console.log(`\n  design exercises (no Lean, nothing to index): ${design.join(', ')}`);

/* ---- --prove: the end-to-end check ----
   Splice each exercise's context with the solution the workbook shows and run
   the real Lean over it. This is the only check that proves the thing the
   reader actually experiences: that typing the shown answer is accepted. It
   subsumes the two failure directions above — a cut that is too late fails with
   "has already been declared", one that is too early fails with an unknown
   identifier — and it catches a solution that stopped compiling because an
   earlier unit changed something under it.

   The WASM harness (tools/check-all-exercises.cjs) is the same check through
   the browser's own entry point and is the one that ships. This one is local
   Lean, runs in about half a second per exercise instead of minutes total, and
   is therefore the one you can afford to run on every unit. */
if (process.argv.includes('--prove')) {
  const { spawnSync } = await import('child_process');
  const os = await import('os');
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'e2ctx'));
  let proved = 0, failed = 0, slowest = 0;
  console.log('\nproving each solution against its own context\n');
  for (const ch of chapters) {
    for (const b of ch.blocks || []) {
      if (b.t !== 'ex' || !b.sol || index[b.id] === undefined) continue;
      const file = path.join(tmp, b.id.replace(/[^\w]/g, '_') + '.lean');
      fs.writeFileSync(file, corpus.slice(0, index[b.id]) + '\n' + b.sol + '\n');
      const t0 = Date.now();
      const r = spawnSync('lean', [file], { encoding: 'utf8' });
      const ms = Date.now() - t0;
      slowest = Math.max(slowest, ms);
      const out = ((r.stdout || '') + (r.stderr || '')).trim();
      if (!out) { proved++; console.log(`  \x1b[32m✓\x1b[0m ${b.id.padEnd(7)} ${String(ms).padStart(5)}ms  ${b.name}`); }
      else {
        failed++; bad++;
        console.log(`  \x1b[31m✗\x1b[0m ${b.id.padEnd(7)} ${b.name}`);
        out.split('\n').slice(0, 4).forEach(l => console.log(`      ${l.replace(file, 'context+solution')}`));
      }
    }
  }
  fs.rmSync(tmp, { recursive: true, force: true });
  console.log(`\n  ${proved} proved, ${failed} failed, slowest ${slowest}ms`);
}

if (WRITE && !bad) {
  fs.writeFileSync(path.join(SITE, 'lean', 'context.lean'), corpus);
  fs.writeFileSync(path.join(SITE, 'lean', 'context-index.json'), JSON.stringify(index, null, 1));
  console.log(`\nwrote lean/context.lean and lean/context-index.json`);
} else if (WRITE) {
  console.error(`\nrefusing to write: fix the ${bad} problem(s) above first`);
} else {
  console.log(`\n(dry run — pass --write to install)`);
}

console.log(`\n${bad} problem(s)\n`);
process.exit(bad ? 1 : 0);
