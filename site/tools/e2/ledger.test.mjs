#!/usr/bin/env node
/* Prove the ledger check works, by running it over Edition 1.
 *
 *   node site/tools/e2/ledger.test.mjs            the report
 *   node site/tools/e2/ledger.test.mjs --json
 *   node site/tools/e2/ledger.test.mjs --top      the worst offenders, ranked
 *
 * Edition 2 has no content yet, so the only corpus to test against is the one
 * the ledger exists to repair. The mapping below is THROWAWAY: it pins each
 * Edition-1 chapter to the LAST Edition-2 unit whose material that chapter
 * covers — the most generous reading, so that everything the tool reports is a
 * genuine use-before-introduction rather than an artefact of a tight mapping.
 * It does not belong in ledger.json and must not be used for anything else.
 *
 * Expected outcome: hundreds of errors. Edition 1 front-loads its whole
 * vocabulary into `00-overview.js` and never introduces most of it; that is
 * §G.1's reason for abolishing the chapter, and this tool is what measures it.
 * A clean run here would mean the checker is broken.
 */
import { run, report } from './ledger.mjs';

const MAP = {
  '00-overview': '00-aliasing',        // chapter 1: the reader knows nothing
  '01-m0': '05-update',                // the Lean runway, ends at the update family
  '02-m1': '08-heap-laws',             // heaps and the eleven equations
  '03-m2': '13-splits',                // disjoint / union / PCM / splits
  '04-m3': '15-pointsto',              // assertions, entailment, emp, ↦
  '05-m4': '19-pure',                  // ∗, its laws, associativity, pure
  '06-m5': '24-interpreter',           // language, exec, induction, interpreter
  '07-m6': '25-hoare',                 // triples and the structural rules
  '08-m7': '26-small-footprint',       // the primitive memory rules
  '09-m8': '31-aliasing-closed',       // locality, the frame rule, aliasing closed
  '10-m9': '33-swap',                  // symbolic execution and swap
  '11-m10': '36-lseg',                 // listRep and lseg
  '12-m11': '37-wand',                 // the wand
  '13-m12': '34-wp',                   // wp — Edition 2 moves it before listRep
  '14-m13': '40-variant',              // partial correctness, invariant, variant
  '15-m14': '41-beyond',               // beyond
  '16-ref': '43-ref'
};

/* The other end of the range: each chapter pinned to the FIRST Edition-2 unit
   whose material it opens. `--strict` runs this instead, to show how much of
   the signal is mapping-dependent — the honest question to ask of any tool
   whose answer depends on a table someone wrote by hand. */
const STRICT = {
  '00-overview': '00-aliasing', '01-m0': '02-terms', '02-m1': '07-heap',
  '03-m2': '10-disjoint', '04-m3': '14-assertions', '05-m4': '16-star',
  '06-m5': '21-language', '07-m6': '25-hoare', '08-m7': '26-small-footprint',
  '09-m8': '27-locality', '10-m9': '32-symbolic', '11-m10': '35-listrep',
  '12-m11': '37-wand', '13-m12': '34-wp', '14-m13': '38-partial',
  '15-m14': '41-beyond', '16-ref': '43-ref'
};

const args = process.argv.slice(2);
const res = run({
  map: args.includes('--strict') ? STRICT : MAP,
  noProse: args.includes('--no-prose'),
  only: args.filter(a => !a.startsWith('--'))[0]
});

if (args.includes('--top')) {
  const tally = new Map();
  for (const f of res.findings) {
    if (f.severity !== 'error') continue;
    const k = `${f.rule}\t${f.entryKind || ''}\t${f.name}\t${f.introducedIn || ''}`;
    if (!tally.has(k)) tally.set(k, { files: [], sites: 0 });
    const t = tally.get(k);
    t.files.push(`${f.file}:${f.path}:${f.line}`);
    t.sites += f.count;
  }
  const rows = [...tally].sort((a, b) => b[1].sites - a[1].sites);
  for (const [k, t] of rows) {
    const [rule, kind, name, intro] = k.split('\t');
    console.log(`${String(t.sites).padStart(4)} sites ${String(t.files.length).padStart(3)} ch  ${rule.padEnd(9)} ${kind.padEnd(9)} ${name.padEnd(32)} ${intro.padEnd(18)} ${t.files[0]}`);
  }
  const sites = res.findings.filter(f => f.severity === 'error').reduce((n, f) => n + f.count, 0);
  console.log(`\n${rows.length} distinct violations, ${sites} sites`);
  process.exit(0);
}

process.exit(report(res, args.includes('--json')));
