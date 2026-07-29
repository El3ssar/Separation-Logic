#!/usr/bin/env node
/* Prove every exercise in the environment the reader actually gets.
 *
 *   node site/tools/check-all-exercises.cjs          all of them
 *   node site/tools/check-all-exercises.cjs m4       just one chapter
 *
 * For each exercise this splices lean/context.lean (cut at that exercise's
 * index entry, so the official solution is NOT already in scope) together with
 * the solution the workbook shows, and runs it through the same WASM Lean the
 * browser uses, via the same lean_wasm_compile entry point.
 *
 * It is the end-to-end check that matters: it proves the solutions are correct,
 * that each context is self-contained and cut in the right place, and that the
 * interactive checker will accept a reader who types the shown answer.
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const SITE = path.join(__dirname, '..');
const WASM = path.join(SITE, 'lean-wasm');
const only = process.argv[2];

const context = fs.readFileSync(path.join(SITE, 'lean', 'context.lean'), 'utf8');
const index = JSON.parse(fs.readFileSync(path.join(SITE, 'lean', 'context-index.json'), 'utf8'));

/* the exercises, straight out of the content files */
const chapters = [];
const cctx = vm.createContext({ registerChapter: (c) => chapters.push(c) });
for (const f of fs.readdirSync(path.join(SITE, 'content')).filter(f => f.endsWith('.js')).sort()) {
  vm.runInContext(fs.readFileSync(path.join(SITE, 'content', f), 'utf8'), cctx, { filename: f });
}
const EX = [];
for (const ch of chapters) {
  for (const b of ch.blocks) {
    if (b.t === 'ex' && b.sol && index[b.id] !== undefined) {
      if (only && ch.id !== only) continue;
      EX.push({ id: b.id, name: b.name, num: ch.num, sol: b.sol, cut: index[b.id] });
    }
  }
}

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
    (function walk(dir, base) {
      for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
        if (e.name.startsWith('._')) continue;
        const p = path.join(dir, e.name), rel = base ? base + '/' + e.name : e.name;
        if (e.isDirectory()) { try { FS.mkdir('/lib/lean/' + rel); } catch (err) {} walk(p, rel); }
        else if (e.name.endsWith('.olean')) FS.writeFile('/lib/lean/' + rel, new Uint8Array(fs.readFileSync(p)));
      }
    })(path.join(WASM, 'lean-lib'), '');
    try { FS.chdir('/workspace'); } catch (e) {}
  }],
  onAbort: (w) => { console.error('ABORT: ' + w); process.exit(3); }
};
process.chdir('/');
process.argv[1] = '/bin/lean';

const mkStr = (s) => { const p = Module.stringToNewUTF8(s); const o = Module._lean_mk_string(p); Module._free(p); return o; };

function compile(code) {
  out.length = 0; capturing = true;
  const t0 = Date.now();
  Module._lean_wasm_compile(mkStr(code), mkStr('/workspace/input.lean'));
  capturing = false;
  const text = out.join('\n');
  const msgs = text.split('\n').map(l => l.trim())
    .filter(l => l[0] === '{' && l.includes('"severity"'))
    .map(l => { try { return JSON.parse(l); } catch (e) { return null; } }).filter(Boolean);
  return {
    ms: Date.now() - t0,
    alive: /Nat\.succ 0 : Nat/.test(text),
    errors: msgs.filter(m => m.severity === 'error'),
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
  compile('public section\nexample : True := trivial\nend\n#check (Nat.succ 0)\n');   // warm

  console.log(`\n  checking ${EX.length} exercises against their own context\n`);
  let bad = 0, slowest = 0, total = 0;

  for (const e of EX) {
    const src = 'public section\n' + context.slice(0, e.cut) + '\n' + e.sol + '\nend\n#check (Nat.succ 0)\n';
    const r = compile(src);
    total += r.ms; slowest = Math.max(slowest, r.ms);
    const ok = r.alive && r.errors.length === 0 && !r.sorry;
    if (!ok) {
      bad++;
      console.log(`  \x1b[31m✗\x1b[0m ${e.num.padEnd(4)} ${e.id.padEnd(7)} ${e.name}`);
      if (!r.alive) console.log(`      runtime died`);
      for (const m of r.errors.slice(0, 3)) {
        console.log(`      line ${m.pos ? m.pos.line : '?'}: ${String(m.data).split('\n')[0].slice(0, 100)}`);
      }
      if (r.sorry) console.log(`      solution contains sorry`);
    } else {
      console.log(`  \x1b[32m✓\x1b[0m ${e.num.padEnd(4)} ${e.id.padEnd(7)} ${String(r.ms).padStart(5)}ms  ${e.name}`);
    }
  }

  console.log(`\n  ${EX.length - bad}/${EX.length} proved   median-ish ${Math.round(total / EX.length)}ms, slowest ${slowest}ms\n`);
  process.exit(bad ? 1 : 0);
};

globalThis.require = require;
globalThis.__filename = '/bin/lean.js';
globalThis.__dirname = '/bin';
vm.runInThisContext(fs.readFileSync(path.join(WASM, 'lean.js'), 'utf8'), { filename: 'lean.js' });
