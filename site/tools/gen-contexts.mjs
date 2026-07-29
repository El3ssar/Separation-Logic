#!/usr/bin/env node
/* Build the Lean context each exercise is checked against.
 *
 *   node site/tools/gen-contexts.mjs
 *
 * An exercise must be elaborated with everything established *before* it — and
 * above all not its own solution, or Lean answers "`singleton_same` has already
 * been declared" instead of checking the reader's proof.
 *
 * The context IS lean/corpus.lean: the file that compiles clean under Lean, in
 * course order. We do not rebuild it from the content blocks — an earlier
 * attempt did, and silently dropped every definition an author had moved into
 * an annotated-code block, producing contexts that did not compile. Taking the
 * verified file and cutting it is both simpler and impossible to get subtly
 * wrong: any prefix ending at a declaration boundary still compiles.
 *
 * Writes:
 *   site/lean/context.lean          a copy of the verified corpus
 *   site/lean/context-index.json    exercise id -> characters of it to use
 */
import fs from 'fs';
import path from 'path';
import vm from 'vm';
import { fileURLToPath } from 'url';

const SITE = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
const corpus = fs.readFileSync(path.join(SITE, 'lean', 'corpus.lean'), 'utf8');

const chapters = [];
const ctx = vm.createContext({ registerChapter: (c) => chapters.push(c) });
for (const f of fs.readdirSync(path.join(SITE, 'content')).filter(f => f.endsWith('.js')).sort()) {
  vm.runInContext(fs.readFileSync(path.join(SITE, 'content', f), 'utf8'), ctx, { filename: f });
}

const norm = (s) => s.replace(/\r/g, '').replace(/[ \t]+$/gm, '').trim();

const index = {};
const missing = [];
let cursor = 0;                 // solutions appear in course order; search forward
let lastCut = 0;

for (const ch of chapters) {
  for (const b of ch.blocks) {
    if (b.t !== 'ex' || !b.sol) continue;

    /* M14 extends the language rather than living inside the corpus, so its
       exercises get the whole of M0–M13. */
    if (ch.id === 'm14') { index[b.id] = corpus.length; continue; }

    const needle = norm(b.sol);
    let at = corpus.indexOf(needle, cursor);
    if (at < 0) at = corpus.indexOf(needle);          // out of order (rare)
    if (at < 0) {
      /* Fall back to the theorem's own opening line, which is enough to locate
         the declaration even if the body was reformatted somewhere. */
      const firstLine = needle.split('\n')[0];
      at = corpus.indexOf(firstLine, cursor);
      if (at < 0) at = corpus.indexOf(firstLine);
    }
    if (at < 0) { missing.push(`${ch.num} ${b.id} ${b.name}`); index[b.id] = lastCut; continue; }

    /* Cut at the start of the comment line that introduces this declaration,
       so the reader's context ends cleanly at a declaration boundary. */
    let cut = corpus.lastIndexOf('\n/-', at);
    cut = cut < 0 ? at : cut + 1;

    index[b.id] = cut;
    lastCut = cut;
    cursor = at + needle.length;
  }
}

fs.writeFileSync(path.join(SITE, 'lean', 'context.lean'), corpus);
fs.writeFileSync(path.join(SITE, 'lean', 'context-index.json'), JSON.stringify(index, null, 1));

console.log(`context.lean        ${(corpus.length / 1024).toFixed(0)} KB, ${corpus.split('\n').length} lines`);
console.log(`context-index.json  ${Object.keys(index).length} exercises`);
if (missing.length) {
  console.log(`\n  \x1b[31m${missing.length} solution(s) not found in the corpus:\x1b[0m`);
  for (const m of missing) console.log('   ' + m);
  process.exit(1);
}
for (const k of ['m0-1', 'm1-1', 'm1-5', 'm4-1', 'm8-1', 'm13-1'].filter(k => k in index)) {
  console.log(`  ${k.padEnd(7)} ${String(index[k]).padStart(6)} chars of context`);
}
