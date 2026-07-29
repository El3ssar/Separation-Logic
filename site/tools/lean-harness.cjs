#!/usr/bin/env node
/* Drive the Lean WASM runtime exactly the way the browser worker does —
 * lean_wasm_compile against a persistent, already-initialised module — but
 * under Node, where nothing throttles it and the output is easy to read.
 *
 *   node site/tools/lean-harness.cjs
 *
 * Exists because the interesting question is not "does one file compile" (the
 * CLI answers that) but "does the runtime stay alive across many compiles, and
 * does it actually reject bad proofs". A browser tab is a bad place to learn
 * the answer.
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const SITE = path.join(__dirname, '..');
const WASM = path.join(SITE, 'lean-wasm');

const out = [];
let capturing = false;
const keep = (t) => { if (capturing) out.push(t); };

function walk(dir, base = '') {
  const r = [];
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    if (e.name.startsWith('._')) continue;
    const p = path.join(dir, e.name), rel = base ? base + '/' + e.name : e.name;
    if (e.isDirectory()) r.push(...walk(p, rel));
    else if (e.name.endsWith('.olean')) r.push({ name: rel, file: p });
  }
  return r;
}

const PAGE = 65536, MB = Number(process.env.LEAN_MB || 2000);

globalThis.Module = {
  wasmMemory: new WebAssembly.Memory({ initial: (MB * 1024 * 1024) / PAGE, maximum: 32768, shared: true }),
  INITIAL_MEMORY: MB * 1024 * 1024,
  noInitialRun: true,
  locateFile: (p) => path.join(WASM, p),
  /* __filename is the *virtual* /bin/lean.js so Lean finds its sysroot, but the
     pthread sub-workers must load the real file from disk. */
  mainScriptUrlOrBlob: path.join(WASM, 'lean.js'),
  print: keep, printErr: keep,
  preRun: [function () {
    const FS = Module.FS;
    Module.ENV['LEAN_PATH'] = '/lib/lean';
    for (const d of ['/lib', '/lib/lean', '/workspace', '/bin']) { try { FS.mkdir(d); } catch (e) {} }
    const files = walk(path.join(WASM, 'lean-lib'));
    for (const f of files) {
      const full = '/lib/lean/' + f.name;
      let cur = '';
      for (const part of full.substring(0, full.lastIndexOf('/')).split('/').filter(Boolean)) {
        cur += '/' + part; try { FS.mkdir(cur); } catch (e) {}
      }
      FS.writeFile(full, new Uint8Array(fs.readFileSync(f.file)));
    }
    process.stderr.write(`[harness] wrote ${files.length} oleans into MEMFS\n`);
    try { FS.chdir('/workspace'); } catch (e) {}
  }],
  onAbort: (w) => { process.stderr.write('[harness] ABORT: ' + w + '\n'); process.exit(3); }
};

process.chdir('/');
process.argv[1] = '/bin/lean';

const mkStr = (s) => { const p = Module.stringToNewUTF8(s); const o = Module._lean_mk_string(p); Module._free(p); return o; };

function compile(code) {
  out.length = 0; capturing = true;
  const t0 = Date.now();
  const res = Module._lean_wasm_compile(mkStr(code), mkStr('/workspace/input.lean'));
  const tag = Module.getValue(res + 7, 'i8') & 0xff;
  capturing = false;
  return { tag, ms: Date.now() - t0, text: out.join('\n') };
}

globalThis.Module.onRuntimeInitialized = function () {
  Module._lean_initialize_runtime_module();
  Module._lean_initialize();
  Module._lean_io_mark_end_initialization();
  if (Module._lean_init_task_manager) Module._lean_init_task_manager();
  if (Module._lean_enable_initializer_execution) Module._lean_enable_initializer_execution();
  const sp = Module._lean_init_search_path();
  if ((Module.getValue(sp + 7, 'i8') & 0xff) !== 0) { console.error('search path failed'); process.exit(4); }

  /* LEAN_SNAPSHOT=1 seeds the environment from the baked region instead of
     importing Init, which is the difference between a ~100s and a ~10s start. */
  if (process.env.LEAN_SNAPSHOT === '1') {
    const snap = path.join(WASM, 'snapshots', 'init.snap');
    if (!fs.existsSync(snap)) { console.error('no snapshot at ' + snap); process.exit(5); }
    if (!Module._lean_wasm_load_snapshot) { console.error('this build has no lean_wasm_load_snapshot'); process.exit(5); }
    const t0 = Date.now(), FS = Module.FS;
    try { FS.mkdir('/snapshots'); } catch (e) {}
    FS.writeFile('/snapshots/init.snap', new Uint8Array(fs.readFileSync(snap)));
    FS.writeFile('/snapshots/init.snap.deps', new Uint8Array([0x5b, 0x5d]));   // "[]"
    const r = Module._lean_wasm_load_snapshot(mkStr('/snapshots/init.snap'));
    const tag = Module.getValue(r + 7, 'i8') & 0xff;
    const box = Module.getValue(r + 8, 'i32');
    const ret = Module.getValue(box + 8, 'i32');
    process.stderr.write(`[harness] snapshot tag=${tag} ret=${ret} loaded in ${Date.now() - t0}ms\n`);
  }

  const prelude = fs.readFileSync(path.join(SITE, 'lean', 'prelude', 'm1.lean'), 'utf8').replace(/\s*$/, '');
  const wrap = (user) => 'public section\n' + prelude + '\n\n' + user + '\nend\n#check (Nat.succ 0)\n';

  const CASES = [
    ['warmup       ', 'example : True := trivial\n', 'accept'],
    ['correct      ', 'theorem a1 (l : Loc) (v : Val) : Heap.singleton l v l = some v := by\n  simp [Heap.singleton]\n', 'accept'],
    ['bogus name   ', 'theorem a2 : True := by\n  exact nonexistent_lemma\n', 'reject'],
    ['wrong tactic ', 'theorem a3 (l : Loc) (v : Val) : Heap.singleton l v l = some v := by\n  rfl\n', 'reject'],
    ['false claim  ', 'theorem a4 (l : Loc) (v : Val) : Heap.singleton l v l = none := by\n  simp [Heap.singleton]\n', 'reject'],
    ['typo in simp ', 'theorem a5 (l : Loc) (v : Val) : Heap.singleton l v l = some v := by\n  simp [Heap.singletn]\n', 'reject'],
    ['uses prelude ', 'theorem a6 (h : Heap) (l : Loc) (v : Val) : Heap.write h l v l = some v := by\n  exact write_same h l v\n', 'accept'],
    ['correct again', 'theorem a7 (l : Loc) (v : Val) : Heap.singleton l v l = some v := by\n  simp [Heap.singleton]\n', 'accept'],
    ['syntax error ', 'theorem a8 : True := by\n  ((((\n', 'reject'],
    ['sorry        ', 'theorem a10 (l : Loc) (v : Val) : Heap.singleton l v l = some v := by\n  sorry\n', 'sorry'],
    ['still alive  ', 'theorem a9 (l : Loc) (v : Val) : Heap.singleton l v l = some v := by\n  simp [Heap.singleton]\n', 'accept']
  ];

  console.log('\n  case            verdict   probe  errors  ms     expected');
  console.log('  ' + '-'.repeat(62));
  let failures = 0;

  for (const [name, code, expect] of CASES) {
    const r = compile(wrap(code));
    const alive = /Nat\.succ 0 : Nat/.test(r.text);
    /* Parse exactly the way lean-runtime.js does — JSON diagnostic lines. */
    const msgs = r.text.split('\n').map(l => l.trim())
      .filter(l => l[0] === '{' && l.includes('"severity"'))
      .map(l => { try { return JSON.parse(l); } catch (e) { return null; } })
      .filter(Boolean);
    const errs = msgs.filter(m => m.severity === 'error').length;
    const sorry = msgs.some(m => m.kind === 'hasSorry');
    const verdict = !alive ? 'DEAD' : errs > 0 ? 'reject' : sorry ? 'sorry' : 'accept';
    const good = alive && verdict === expect;
    if (!good) failures++;
    console.log(`  ${name}  ${verdict.padEnd(8)} ${(alive ? 'ok' : 'GONE').padEnd(6)} ${String(errs).padEnd(7)} ${String(r.ms).padEnd(6)} ${expect}  ${good ? '' : '  <-- WRONG'}`);
    if (!alive) { console.log('\n  runtime died here; remaining cases skipped\n  last output:\n' + r.text.slice(0, 600)); break; }
  }

  console.log('\n  ' + (failures ? `${failures} case(s) wrong` : 'all cases behaved correctly') + '\n');
  process.exit(failures ? 1 : 0);
};

/* lean.js is evaluated at global scope (its top-level `var Module` must not be
   trapped in a CommonJS wrapper), so the things it expects from Node have to be
   reachable from there. */
globalThis.require = require;
/* These must be the *virtual* install paths, not host paths: Lean derives its
   sysroot (and hence /lib/lean) from argv[0] and __dirname. Pointing them at
   the real directory makes lean_init_search_path fail. */
globalThis.__filename = '/bin/lean.js';
globalThis.__dirname = '/bin';
vm.runInThisContext(fs.readFileSync(path.join(WASM, 'lean.js'), 'utf8'), { filename: 'lean.js' });
