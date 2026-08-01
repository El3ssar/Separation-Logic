#!/usr/bin/env node
/* Wire the finished second edition into the site.
 *
 *   node site/tools/e2/integrate.mjs            say what would change
 *   node site/tools/e2/integrate.mjs --write    do it
 *   node site/tools/e2/integrate.mjs --write --partial   ... before all 44 exist
 *
 * Authoring deliberately touches only content/, lean/e2/ and the summaries, so
 * that forty-four authors never contend over the same four shared files. This is
 * the step that picks those four up:
 *
 *   index.html     the <script> tags, in course order — the file that decides
 *                  what the sidebar contains and in what sequence
 *   sw.js          the offline shell list; a chapter missing from it is a
 *                  chapter that does not exist when the network is off
 *   app.js         a redirect table from the seventeen Edition-1 chapter ids, so
 *                  a bookmark on #m4 still lands somewhere sensible
 *   lean/          context.lean and context-index.json, the Lean the browser
 *                  splices in front of a reader's proof
 *
 * and removes the Edition-1 chapter files, which live on in git history and on
 * main.
 *
 * Everything here is derived from what is on disk. Nothing is hand-listed, so
 * nothing can drift out of step with the course as it actually stands.
 */
import fs from 'fs';
import path from 'path';
import vm from 'vm';
import { execFileSync } from 'child_process';
import { fileURLToPath } from 'url';

const SITE = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const CONTENT = path.join(SITE, 'content');
const WRITE = process.argv.includes('--write');
const PARTIAL = process.argv.includes('--partial');

const E1 = ['00-overview', '01-m0', '02-m1', '03-m2', '04-m3', '05-m4', '06-m5', '07-m6',
  '08-m7', '09-m8', '10-m9', '11-m10', '12-m11', '13-m12', '14-m13', '15-m14', '16-ref'];
const E1SET = new Set(E1.map(x => x + '.js'));

/* Where an Edition-1 deep link should land. The unit that inherits each old
   chapter's opening material — not a nearest-title match, which would send the
   reader somewhere that merely sounds similar. */
const REDIRECT = {
  overview: 'aliasing', m0: 'update', m1: 'heap', m2: 'disjoint', m3: 'assertions',
  m4: 'star', m5: 'language', m6: 'hoare', m7: 'small-footprint', m8: 'locality',
  m9: 'symbolic', m10: 'listrep', m11: 'wand', m12: 'wp', m13: 'partial',
  m14: 'beyond', ref: 'ref'
};

const files = fs.readdirSync(CONTENT).filter(f => f.endsWith('.js') && !E1SET.has(f)).sort();
const ids = files.map(f => f.replace(/\.js$/, ''));

console.log(`\nedition 2: ${files.length} chapter file(s) on disk`);
if (files.length !== 44 && !PARTIAL) {
  console.error(`\n  refusing: the course is 44 files and ${files.length} are present.`);
  console.error(`  Integrating early leaves index.html listing chapters that do not exist yet.`);
  console.error(`  Pass --partial if that is what you want.\n`);
  process.exit(1);
}

/* Every chapter must load and register, or the site boots into a blank page. */
const chapters = [];
for (const f of files) {
  const got = [];
  try { vm.runInContext(fs.readFileSync(path.join(CONTENT, f), 'utf8'), vm.createContext({ registerChapter: c => got.push(c) }), { filename: f }); }
  catch (e) { console.error(`  ✗ ${f} does not run: ${e.message}`); process.exit(1); }
  if (got.length !== 1) { console.error(`  ✗ ${f} registers ${got.length} chapters`); process.exit(1); }
  chapters.push(got[0]);
}

/* ---- index.html ---- */
const indexPath = path.join(SITE, 'index.html');
let index = fs.readFileSync(indexPath, 'utf8');
const tags = ids.map(id => `<script src="content/${id}.js"></script>`).join('\n');
const before = (index.match(/<script src="content\/[^"]+"><\/script>/g) || []).length;
index = index.replace(/<script src="content\/[^"]+"><\/script>\n?/g, '\x00')
             .replace(/\x00+/, tags + '\n')
             .replace(/\x00/g, '');
console.log(`index.html   ${before} script tags → ${ids.length}`);

/* ---- sw.js ---- */
const swPath = path.join(SITE, 'sw.js');
let sw = fs.readFileSync(swPath, 'utf8');
const shell = [
  './', './index.html', './manifest.webmanifest',
  './assets/base.css', './assets/blocks.css', './assets/editor.css', './assets/responsive.css',
  './assets/app.js', './assets/editor.js', './assets/lean-runtime.js',
  './assets/icon.svg',
  './lean/context.lean', './lean/context-index.json',
  ...ids.map(id => `./content/${id}.js`)
];
const swBody = 'const SHELL_FILES = [\n' + shell.map(u => `  '${u}'`).join(',\n') + '\n];';
const swOld = sw.match(/const SHELL_FILES = \[[\s\S]*?\];/);
if (!swOld) { console.error('  ✗ could not find SHELL_FILES in sw.js'); process.exit(1); }
sw = sw.replace(swOld[0], swBody);
/* The cache name must change, or browsers keep serving the first edition from
   the old cache and the update is invisible to exactly the readers who used it. */
const ver = (sw.match(/const VERSION = 'sl-v(\d+)'/) || [, '6'])[1];
sw = sw.replace(/const VERSION = 'sl-v\d+'/, `const VERSION = 'sl-v${Number(ver) + 1}'`);
console.log(`sw.js        ${shell.length} shell files, cache sl-v${ver} → sl-v${Number(ver) + 1}`);

/* ---- app.js: keep Edition-1 deep links alive ---- */
const appPath = path.join(SITE, 'assets', 'app.js');
let app = fs.readFileSync(appPath, 'utf8');
const missing = Object.values(REDIRECT).filter(v => !ids.includes(v));
if (missing.length && !PARTIAL) { console.error(`  ✗ redirect targets not present: ${missing.join(', ')}`); process.exit(1); }
const redirectBlock = `/* Edition-1 chapter ids, kept alive: #m4 was a permanent link for a year, and
   the second edition renumbered every chapter. Each old id maps to the unit that
   inherits its opening material. */
const REDIRECT = ${JSON.stringify(REDIRECT, null, 2).replace(/"/g, "'").replace(/\n/g, '\n')};
`;
if (app.includes('const REDIRECT =')) {
  app = app.replace(/\/\* Edition-1 chapter ids[\s\S]*?const REDIRECT = \{[\s\S]*?\};\n/, redirectBlock);
  console.log(`app.js       redirect table refreshed (${Object.keys(REDIRECT).length} entries)`);
} else {
  app = app.replace(/(const COURSE = \[\];)/, `$1\n\n${redirectBlock}`);
  app = app.replace(
    /const byHash = COURSE\.findIndex\(c => c\.id === hash\);/,
    'const byHash = COURSE.findIndex(c => c.id === (REDIRECT[hash] || hash));'
  );
  console.log(`app.js       redirect table installed (${Object.keys(REDIRECT).length} entries)`);
}
if (!/REDIRECT\[hash\]/.test(app)) { console.error('  ✗ could not wire REDIRECT into the boot hash lookup'); process.exit(1); }

/* ---- baseline.json: freeze edition 2 the way edition 1 was frozen ---- */
const baseline = {};
for (const ch of chapters) {
  const ex = {};
  const walk = bs => { for (const b of bs || []) { if (b.t === 'ex') ex[b.id] = { name: b.name, goal: b.goal ?? null, sol: b.sol ?? null, hard: !!b.hard }; if (b.t === 'detail') walk(b.blocks); } };
  walk(ch.blocks);
  baseline[ch.id] = { num: ch.num, phase: ch.phase, title: ch.title, ex };
}
const exTotal = Object.values(baseline).reduce((n, c) => n + Object.keys(c.ex).length, 0);
console.log(`baseline     ${Object.keys(baseline).length} chapters, ${exTotal} exercises frozen`);

/* ---- write ---- */
if (!WRITE) {
  console.log(`\nedition-1 files that would be removed: ${E1.length}`);
  console.log(`\n(dry run — pass --write to apply)\n`);
  process.exit(0);
}

fs.writeFileSync(indexPath, index);
fs.writeFileSync(swPath, sw);
fs.writeFileSync(appPath, app);
fs.writeFileSync(path.join(SITE, 'tools', 'baseline.json'), JSON.stringify(baseline, null, 1));

for (const f of E1) {
  const p = path.join(CONTENT, f + '.js');
  if (!fs.existsSync(p)) continue;
  try { execFileSync('git', ['rm', '-q', '--', p], { cwd: SITE }); }
  catch { fs.unlinkSync(p); }
}
console.log(`removed      ${E1.length} edition-1 chapter files`);

execFileSync(process.execPath, [path.join(SITE, 'tools', 'e2', 'gen-contexts.mjs'), '--write'], { stdio: 'inherit' });

console.log(`\nintegrated. Now run, in order:`);
console.log(`  node site/tools/e2/lint.mjs`);
console.log(`  node site/tools/e2/ledger.mjs`);
console.log(`  node site/tools/render-check.js`);
console.log(`  site/tools/e2/verify.sh`);
console.log(`  node site/tools/e2/gen-contexts.mjs --prove`);
console.log(`  node --stack-size=60000 site/tools/check-all-exercises.cjs   (the WASM kernel, slow)`);
console.log(`and then open the site and click something.\n`);
