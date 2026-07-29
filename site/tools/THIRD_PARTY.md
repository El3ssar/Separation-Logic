# Vendored scripts

These three come from [cauli/lean4-wasm-in-browser](https://github.com/cauli/lean4-wasm-in-browser)
(MIT), which builds and hosts the Lean 4 WebAssembly runtime this workbook uses:

| file | what it does |
|---|---|
| `lean-wasm-node.cjs` | runs the wasm `lean` under Node — used to bake the snapshot |
| `patch-wasm-memory.py` | rewrites the wasm module's declared memory maximum |
| `gen-lib-files.mjs` | lists the `.olean` files for the runtime to load |

`site/lean-wasm/lean-worker.js` also started as that project's
`lean-worker-persistent.worker.js`. It has one local change: a
`load_snapshot_bytes` message that writes the snapshot to MEMFS in a single
`FS.writeFile` instead of streaming it in chunks. The streaming path produced a
region this build would not accept; the single write is what
`tools/lean-harness.cjs` verifies.

Everything else under `tools/` is part of this project.
