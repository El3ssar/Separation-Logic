#!/usr/bin/env node
/* Render every chapter headlessly and check the HTML that comes out.
 *
 *   node site/tools/render-check.js
 *
 * This runs the real assets/app.js against the real content files under a
 * minimal DOM stub, so it catches renderer regressions that the validator
 * cannot see: a block type that produces nothing, a field that stringifies to
 * [object Object], a table-of-contents link pointing at an id that is not on
 * the page. Independent of any browser cache.
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const ROOT = path.join(__dirname, '..');

/* ---- the smallest DOM that app.js will accept ---- */
function makeEl(id) {
  const el = {
    id, innerHTML: '', textContent: '', title: '', value: '', open: false,
    style: new Proxy({}, { get: () => '', set: () => true }),
    classList: { add() {}, remove() {}, toggle() { return false; }, contains() { return false; } },
    querySelector: () => null, querySelectorAll: () => [],
    addEventListener() {}, scrollIntoView() {}, focus() {},
    set onclick(f) { this._onclick = f; }, get onclick() { return this._onclick || (() => {}); },
    set oninput(f) {}, set onkeydown(f) {}
  };
  return el;
}

const els = {};
const document = {
  documentElement: { setAttribute() {}, getAttribute: () => 'light' },
  body: { scrollHeight: 1000 },
  getElementById(id) { return (els[id] = els[id] || makeEl(id)); },
  querySelector: () => null,
  querySelectorAll: () => [],
  addEventListener() {},
  get activeElement() { return { tagName: 'BODY' }; },
  get scripts() { return []; },
  set title(v) { this._t = v; }, get title() { return this._t; }
};

const sandbox = {
  document, console,
  scrollTo() {},
  location: { hash: '', replace() {} },
  history: { replaceState() {} },
  navigator: { clipboard: { writeText: async () => {} } },
  localStorage: { getItem: () => null, setItem() {}, removeItem() {} },
  matchMedia: () => ({ matches: false, addEventListener() {} }),
  addEventListener() {},
  setTimeout: () => 0,
  scrollY: 0, innerHeight: 800
};
vm.createContext(sandbox);
/* in a browser window === globalThis; app.js relies on that for registerChapter */
sandbox.window = sandbox;
sandbox.globalThis = sandbox;

/* ---- load the real engine, then the real content ---- */
vm.runInContext(fs.readFileSync(path.join(ROOT, 'assets', 'app.js'), 'utf8'), sandbox, { filename: 'app.js' });
const files = fs.readdirSync(path.join(ROOT, 'content')).filter(f => f.endsWith('.js')).sort();
for (const f of files) {
  vm.runInContext(fs.readFileSync(path.join(ROOT, 'content', f), 'utf8'), sandbox, { filename: f });
}

const COURSE = vm.runInContext('COURSE', sandbox);
let problems = 0;
const bad = (id, m) => { console.error(`  \x1b[31m✗\x1b[0m ${id}: ${m}`); problems++; };

console.log(`\nrendering ${COURSE.length} chapters headlessly\n`);

let totalKb = 0, totalEx = 0, totalTrace = 0;

for (let i = 0; i < COURSE.length; i++) {
  vm.runInContext(`cur = ${i}; renderLesson();`, sandbox);
  const html = els.content.innerHTML;
  const id = COURSE[i].id;

  if (html.length < 2000) bad(id, `rendered only ${html.length} chars`);
  if (html.includes('[object Object]')) bad(id, 'contains [object Object] — a field was stringified wrongly');
  if (/>undefined</.test(html) || /"undefined"/.test(html)) bad(id, 'contains a literal undefined value');
  if (html.includes('NaN')) bad(id, 'contains NaN');

  /* every in-page anchor must exist on the page */
  const ids = new Set([...html.matchAll(/\bid="([^"]+)"/g)].map(m => m[1]));
  for (const m of html.matchAll(/href="#([^"]*)"/g)) {
    if (!m[1]) bad(id, 'table-of-contents link with an empty target');
    else if (!ids.has(m[1])) bad(id, `link to #${m[1]} but no element has that id`);
  }

  /* every exercise must render its checkbox and reveal buttons */
  const exBlocks = COURSE[i].blocks.filter(b => b.t === 'ex');
  const rendered = (html.match(/class="ex[ "]/g) || []).length;
  if (rendered !== exBlocks.length) bad(id, `${exBlocks.length} exercises in data but ${rendered} rendered`);
  for (const e of exBlocks) {
    if (!html.includes(`id="ex-${e.id}"`)) bad(id, `exercise ${e.id} did not render`);
    if (e.sol && !html.includes(`data-rv="${e.id}:sol"`)) bad(id, `exercise ${e.id} has a solution but no Solution button`);
    if (!html.includes(`data-rv="${e.id}:expl"`)) bad(id, `exercise ${e.id} has no "Why it works" panel`);
  }

  /* unclosed divs would break the page layout silently */
  const opens = (html.match(/<div\b/g) || []).length, closes = (html.match(/<\/div>/g) || []).length;
  if (opens !== closes) bad(id, `${opens} <div> vs ${closes} </div> — unbalanced`);

  const kb = Math.round(html.length / 1024);
  const tr = (html.match(/class="trace"/g) || []).length;
  totalKb += kb; totalEx += exBlocks.length; totalTrace += tr;
  console.log(`  ${COURSE[i].num.padEnd(4)} ${String(kb).padStart(4)} KB   ${String(exBlocks.length).padStart(2)} ex   ${String(tr).padStart(3)} traces   ${COURSE[i].title}`);
}

console.log(`\n  total: ${totalKb} KB rendered, ${totalEx} exercises, ${totalTrace} proof-state traces`);
console.log(`\n${problems} problem(s)\n`);
process.exit(problems ? 1 : 0);
