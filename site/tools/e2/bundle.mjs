#!/usr/bin/env node
/* Fold the whole workbook into one self-contained HTML file.
 *
 *   node site/tools/e2/bundle.mjs [out.html]
 *
 * For reading the course somewhere that cannot run a server: a phone, an email
 * attachment, a hosted page. One file, no requests, no service worker, no
 * build. Open it and it works.
 *
 * What it keeps: every chapter, the whole design system, search, the notation
 * drawer, progress, themes, keyboard shortcuts — the site as it is.
 *
 * What it cannot keep is the point of the real thing: the Lean runtime is
 * ~295 MB of WebAssembly and needs cross-origin isolation, so there is no
 * Check button here and no proof gets machine-checked. Exercises still carry
 * their statements, graded hints, solutions, line-by-line walks and goal-state
 * traces, so the teaching survives; the doing does not. The page says so at the
 * top rather than leaving a reader to discover it by pressing something dead.
 *
 * The webfont link goes too, because a hosted artifact's CSP blocks font CDNs
 * and a blocked font is a silent fallback. base.css already names Georgia and
 * the system stacks behind Fraunces and Karla, so removing the link degrades to
 * what it was written to degrade to.
 */
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const SITE = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const OUT = process.argv[2] || path.join(SITE, '..', 'separation-logic-workbook.html');

const read = (...p) => fs.readFileSync(path.join(SITE, ...p), 'utf8');
const esc = s => s.replace(/<\/script>/gi, '<\\/script>');

const shell = read('index.html');

/* The chapters, in the order index.html lists them — that file is the course
   order, so deriving from it means the bundle cannot disagree with the site. */
const chapters = [...shell.matchAll(/<script src="content\/([^"]+)"><\/script>/g)].map(m => m[1]);
if (!chapters.length) { console.error('no chapter scripts found in index.html'); process.exit(1); }

/* Everything between <body> and the first script tag: the rail, topbar, search
   box and notation drawer, exactly as the site has them. */
const body = shell.slice(shell.indexOf('<body>') + 6, shell.indexOf('<script src="assets/lean-runtime.js">'));

const NOTE = `
<div class="pv-note">
  <b>Reading copy.</b> This is the whole course in one file, for reading away from a machine that can
  serve it. The exercises keep their statements, hints, solutions, walkthroughs and real goal states —
  but the Lean runtime is 295&nbsp;MB of WebAssembly and needs a server, so nothing here is checked as
  you type. For that, run <code>python3 site/tools/serve.py</code> and open <code>localhost:8123</code>.
</div>`;

const STYLE = `
/* the reading-copy banner, and the parts of the shell that need a server */
.pv-note{
  margin:0;padding:11px 16px;background:var(--accent-soft);color:var(--accent-ink);
  border-bottom:1px solid var(--line-2);font-family:var(--sans);font-size:13px;line-height:1.5
}
.pv-note b{font-weight:700}
.pv-note code{font-family:var(--mono);font-size:12px;background:var(--card);padding:1px 5px;border-radius:4px}
#leanStatus,.offline{display:none!important}
@media (max-width:760px){.pv-note{font-size:12px;padding:9px 13px}}
`;

const guts = `<title>Separation Logic in Lean 4 — a workbook</title>
<style>
${read('assets', 'base.css')}
${read('assets', 'blocks.css')}
${read('assets', 'editor.css')}
${read('assets', 'responsive.css')}
${STYLE}
</style>
${NOTE}
${body}
<script>
${esc(read('assets', 'app.js'))}
</script>
${chapters.map(c => `<script>\n${esc(read('content', c))}\n</script>`).join('\n')}
<script>window.__boot && window.__boot();</script>
`;

/* --fragment omits the document skeleton, for a host that supplies its own.
   Everything else is identical, so the two cannot drift apart. */
const html = process.argv.includes('--fragment') ? guts : `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
${guts}</html>
`;

fs.writeFileSync(OUT, html);
const kb = (Buffer.byteLength(html) / 1048576).toFixed(1);
console.log(`\n  ${OUT}`);
console.log(`  ${chapters.length} chapters, ${kb} MB, no external requests\n`);
