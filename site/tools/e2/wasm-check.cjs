#!/usr/bin/env node
/* Compile the corpus through the Lean the READER runs.
 *
 *   node --stack-size=60000 site/tools/e2/wasm-check.cjs          the whole corpus
 *   node --stack-size=60000 site/tools/e2/wasm-check.cjs f.lean   any one file
 *
 * WHY THIS EXISTS, AND WHY verify.sh IS NOT ENOUGH.
 *
 * The course is checked with local Lean 4.32.2. The reader's proofs are checked
 * by Lean 4.33-pre compiled to WebAssembly, in a worker in their browser. Those
 * are different compilers, and the local one is MORE PERMISSIVE. A proof can be
 * green on every check in this repository and still be rejected on the page,
 * where the reader has no way to tell whether they or the course is wrong.
 *
 * The difference that bit first — measured, not guessed:
 *
 *   abbrev twice … ; theorem : twice 3 = 6 := rfl     both accept
 *   def double … ; theorem : double 3 = 6 := rfl      local accepts, BROWSER REJECTS
 *   def double … ; … := by simp [double]              both accept
 *   def double … ; … := by unfold double              local accepts, BROWSER leaves it unsolved
 *   @[expose] def double … ; … := rfl                 browser accepts; local WARNS, which
 *                                                     fails verify.sh, so it is not a workaround
 *
 * The browser's Lean tracks master, whose module system does not expose a plain
 * `def`'s body for definitional unfolding. `abbrev` is reducible, so `rfl` still
 * sees through it. In the reader's environment `rfl` will not unfold a `def`;
 * ask with `simp [f]` instead.
 *
 * That single class produced two errors in the corpus and 43 end-to-end failures,
 * because the two bad lines sat in the shared context prefix that every later
 * exercise is spliced onto.
 *
 * This is slower than the other checks — about a minute, nearly all of it loading
 * Lean's environment snapshot — so it is not something to run after every
 * paragraph. Run it when you add Lean, before you hand your unit on, and always
 * before integration. tools/check-all-exercises.cjs is the finer-grained version:
 * it runs each exercise's own solution against its own context through the same
 * kernel, and is the check that ships.
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const { execFileSync } = require('child_process');

const SITE = path.join(__dirname, '..', '..');
const WASM = path.join(SITE, 'lean-wasm');

if (!fs.existsSync(path.join(WASM, 'lean.js'))) {
  console.error('the Lean runtime is not installed — run site/tools/fetch-lean-wasm.sh');
  process.exit(2);
}

/* Either the file named on the command line, or the whole corpus in course
   order. When it is the corpus we keep the fragment boundaries, so an error can
   be reported against the unit that owns it rather than a line in a 2000-line
   file nobody wrote. */
const arg = process.argv[2];
let source, bounds = [];
if (arg) {
  source = fs.readFileSync(arg, 'utf8');
} else {
  source = execFileSync(path.join(SITE, 'tools', 'e2', 'prelude.sh'), ['99', '--incl'], { encoding: 'utf8' });
  /* prelude.sh emits each fragment then a blank line, so a fragment occupies its
     own line count plus one. Counting `split('\n').length` on a file ending in a
     newline overcounts by one, and adding the separator on top of that drifts a
     line per fragment — which is how this first pointed two lines above the real
     error. Count the lines the file actually has, then add exactly one. */
  let line = 1;
  for (const f of fs.readdirSync(path.join(SITE, 'lean', 'e2')).filter(f => f.endsWith('.lean')).sort()) {
    const text = fs.readFileSync(path.join(SITE, 'lean', 'e2', f), 'utf8');
    const n = text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
    bounds.push({ file: f, from: line, to: line + n - 1 });
    line += n + 1;
  }
}
const owner = (ln) => {
  const b = bounds.find(b => ln >= b.from && ln <= b.to);
  return b ? `${b.file}:${ln - b.from + 1}` : `line ${ln}`;
};

const out = [];
let capturing = false;

globalThis.Module = {
  wasmMemory: new WebAssembly.Memory({ initial: (2000 * 1024 * 1024) / 65536, maximum: 32768, shared: true }),
  INITIAL_MEMORY: 2000 * 1024 * 1024,
  noInitialRun: true,
  locateFile: (p) => path.join(WASM, p),
  mainScriptUrlOrBlob: path.join(WASM, 'lean.js'),
  print: (t) => { if (capturing) out.push(t); },
  printErr: (t) => { if (capturing) out.push(t); },
  preRun: [function () {
    const FS = Module.FS;
    Module.ENV['LEAN_PATH'] = '/lib/lean';
    for (const d of ['/lib', '/lib/lean', '/workspace', '/bin']) { try { FS.mkdir(d); } catch (e) {} }
    try { FS.chdir('/workspace'); } catch (e) {}
  }],
  onAbort: (w) => { console.error('ABORT: ' + w); process.exit(3); }
};
process.chdir('/');
process.argv[1] = '/bin/lean';

const mkStr = (s) => { const p = Module.stringToNewUTF8(s); const o = Module._lean_mk_string(p); Module._free(p); return o; };

function compile(code) {
  out.length = 0; capturing = true;
  Module._lean_wasm_compile(mkStr(code), mkStr('/workspace/input.lean'));
  capturing = false;
  const text = out.join('\n');
  const msgs = text.split('\n').map(l => l.trim())
    .filter(l => l[0] === '{' && l.includes('"severity"'))
    .map(l => { try { return JSON.parse(l); } catch (e) { return null; } }).filter(Boolean);
  return {
    /* Printed by every run. Its absence means Lean never reached the end of the
       file, and a silent Lean is byte-identical to a Lean that approved of
       everything — which must never be reported as a pass. */
    alive: /Nat\.succ 0 : Nat/.test(text),
    errors: msgs.filter(m => m.severity === 'error'),
    warnings: msgs.filter(m => m.severity === 'warning' && m.kind !== 'hasSorry'),
    sorry: msgs.some(m => m.kind === 'hasSorry'),
    text
  };
}

globalThis.Module.onRuntimeInitialized = function () {
  Module._lean_initialize_runtime_module();
  Module._lean_initialize();
  Module._lean_io_mark_end_initialization();
  if (Module._lean_init_task_manager) Module._lean_init_task_manager();
  if (Module._lean_enable_initializer_execution) Module._lean_enable_initializer_execution();
  Module._lean_init_search_path();

  const snap = path.join(WASM, 'snapshots', 'init.snap');
  if (fs.existsSync(snap) && Module._lean_wasm_load_snapshot) {
    const FS = Module.FS;
    try { FS.mkdir('/snapshots'); } catch (e) {}
    FS.writeFile('/snapshots/init.snap', new Uint8Array(fs.readFileSync(snap)));
    FS.writeFile('/snapshots/init.snap.deps', new Uint8Array([0x5b, 0x5d]));
    Module._lean_wasm_load_snapshot(mkStr('/snapshots/init.snap'));
  }
  compile('public section\nexample : True := trivial\nend\n#check (Nat.succ 0)\n');

  /* `public section` matches what lean-runtime.js wraps a reader's proof in:
     the WASM build tracks master, where declarations are private by default and
     a public `infix` cannot otherwise see the `def` it names. */
  const head = 'public section\n';
  const r = compile(head + source + '\nend\n#check (Nat.succ 0)\n');
  const shift = head.split('\n').length - 1;

  const what = arg || `the corpus (${bounds.length} fragments, ${source.split('\n').length} lines)`;
  console.log(`\n  ${what}\n  through the Lean the reader runs\n`);

  if (!r.alive) {
    console.error('  the runtime produced no output at all, not even the liveness probe —');
    console.error('  it is not running, and this is not a verdict on the Lean.\n');
    process.exit(3);
  }
  if (r.sorry) console.log('  \x1b[33m!\x1b[0m the corpus contains `sorry`');

  for (const e of r.errors) {
    const ln = e.pos ? e.pos.line - shift : 0;
    console.log(`  \x1b[31m✗\x1b[0m ${owner(ln)}`);
    String(e.data).split('\n').slice(0, 4).forEach(l => console.log(`      ${l}`));
  }
  for (const w of r.warnings.slice(0, 5)) {
    const ln = w.pos ? w.pos.line - shift : 0;
    console.log(`  \x1b[33m!\x1b[0m ${owner(ln)}: ${String(w.data).split('\n')[0]}`);
  }

  const bad = r.errors.length + (r.sorry ? 1 : 0);
  console.log(`\n  ${bad ? bad + ' problem(s)' : 'clean — the reader\'s Lean accepts all of it'}\n`);
  process.exit(bad ? 1 : 0);
};

globalThis.require = require;
globalThis.__filename = '/bin/lean.js';
globalThis.__dirname = '/bin';
vm.runInThisContext(fs.readFileSync(path.join(WASM, 'lean.js'), 'utf8'), { filename: 'lean.js' });
