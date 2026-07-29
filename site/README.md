# Separation Logic in Lean 4 — a mathematician's workbook

A self-teaching course: build a separation logic from nothing, in Lean 4, with
every proof machine-checked — **including yours**. Each exercise has an editor,
and pressing *Check* runs the real Lean 4 kernel, compiled to WebAssembly, in a
worker on your own machine. Nothing is sent anywhere, and it works offline.

## Running it

It is a static site. There is no build step and no dependencies.

```bash
python3 site/tools/serve.py
```

then open <http://localhost:8123>.

`serve.py` is `http.server` with caching switched off, so an edit to `app.js`
or a chapter shows up on reload instead of hiding behind a stale copy. Plain
`python3 -m http.server 8123 --directory site` works too if you prefer, at the
cost of the occasional hard reload.

The server is required, not optional: the Lean runtime is a pthread build that
needs `SharedArrayBuffer`, which browsers only grant to a **cross-origin
isolated** page. `serve.py` sends the COOP/COEP headers that buy that. Opened
straight off disk from `file://`, the course text still reads fine but Lean
will not start.

## The Lean runtime

Interactive checking needs `site/lean-wasm/` — about 295 MB, so it is not in
git. Fetch it once:

```bash
site/tools/fetch-lean-wasm.sh
```

That downloads Lean 4.33-pre compiled to wasm32, installs Init's `.olean` files
(only Init — this course imports nothing, so Std/Lean/Lake are skipped, saving
~410 MB), and bakes the startup snapshot.

| | |
|---|---|
| cold start | ~11 s |
| each check afterwards | 200 ms – a few seconds |
| installed size | ~295 MB |

The snapshot is what makes the first number small. Without it, every session
spends ~100 s importing Init before it can check anything.

Verify the whole thing end-to-end — all 75 exercise solutions, proved in the
same environment the reader gets, through the same entry point the browser
uses:

```bash
node --stack-size=60000 site/tools/check-all-exercises.cjs
```

## Using it on a phone

Serve from your PC, open the address on the phone over wi-fi, then use the
sidebar's **Save Lean for offline** button. The service worker stores the whole
runtime, and after that the phone needs no network and no server — add it to
the home screen and it opens as an app. The download is deliberately opt-in so
295 MB never arrives on mobile data by surprise.

Typing `∗ ↦ ⊢ -∗` on a phone keyboard is hopeless, so the editor has a symbol
palette, and Lean's own abbreviations work: `\to` `\star` `\mapsto` `\vdash`
`\wand` `\forall` `\1` expand on space.

## Layout

```
site/
  index.html          shell — sidebar, topbar, search, notation drawer, and the
                      <script> tags that load the chapters in order
  assets/
    base.css          the design system
    blocks.css        styles for the block vocabulary
    app.js            the engine: renderer, search index, progress, theme
  content/
    00-overview.js    one file per chapter, each calling registerChapter({...})
    01-m0.js  …  16-ref.js
  lean/
    corpus.lean       M0–M13 as one file: every definition, every proof
    prelude/*.lean    cumulative context up to each chapter
  lean-wasm/          the Lean 4 WebAssembly runtime (not in git — fetch it)
  sw.js               service worker: offline cache + COOP/COEP replay
  manifest.webmanifest
  tools/
    serve.py               static server: isolation headers, no caching
    fetch-lean-wasm.sh     download and install the Lean runtime
    validate.js            schema, Lean fidelity, and teaching-depth checks
    render-check.js        render every chapter headlessly, check the HTML
    check-all-exercises.cjs  prove all 75 solutions through the WASM kernel
    lean-harness.cjs       drive the runtime under Node (correctness/stability)
    gen-contexts.mjs       build the per-exercise Lean contexts
    goalstate.sh           print the real Lean goal state at any point
    baseline.json          the original course, for fidelity comparison
    _src/*.md              the original chapters in readable form
  AUTHORING.md        the block schema — read before editing content
  PEDAGOGY.md         who the reader is and how to write for them
```

## The Lean is checked

`lean/corpus.lean` is every definition and every exercise solution from
milestones M0 through M13, concatenated in course order. It compiles clean:

```bash
cd site/lean && lean corpus.lean      # silence means all 127 theorems went through
```

Lean 4.32.2, no `import`s, no Mathlib, no `sorry`. M14 (optional allocation) and
the Reference chapter contain deliberately schematic code and sit outside the
corpus; blocks there are tagged `sketch` or `illustration` rather than `verified`.

## Editing

Content is data. To change a chapter, edit its file in `content/` — the schema
is in [AUTHORING.md](AUTHORING.md), the house style in [PEDAGOGY.md](PEDAGOGY.md).

```bash
node --check site/content/05-m4.js        # does it parse
node site/tools/validate.js               # schema, ids, Lean fidelity
node site/tools/validate.js --strict      # teaching depth as well
node site/tools/render-check.js           # render it all, check the HTML
node site/tools/gen-contexts.mjs          # rebuild per-exercise Lean contexts
```

Run `gen-contexts.mjs` after changing any exercise: it maps each exercise id to
how much of `lean/corpus.lean` precedes it, cut **before** that exercise's own
solution. Get that wrong and Lean answers "already been declared" instead of
checking the reader's proof.

`render-check.js` runs the real `app.js` against the real content under a
minimal DOM stub. It catches what the validator cannot: a block type that
renders to nothing, a field that stringifies to `[object Object]`, a
table-of-contents link pointing at an id that is not on the page, unbalanced
`<div>`s. No browser and no cache involved, so it never lies to you.

The validator is deliberately strict about two things:

- **Lean is never edited.** Every exercise `goal` and `sol` is compared
  byte-for-byte against `tools/baseline.json`. Anything tagged `verified` must
  really occur in `corpus.lean`.
- **Exercise ids never move.** Reader progress is stored against them, and
  `#m4` in the URL is a permanent link to a chapter.

To add a chapter: write `content/NN-id.js`, add a `<script>` tag to
`index.html`, and add it to `tools/baseline.json`.

## Showing a goal state

The most useful thing you can put in front of a Lean beginner is what the goal
actually looked like. Get it from Lean, never from memory:

```bash
cat > /tmp/s.lean <<'EOF'
theorem demo (h : Heap) (l : Loc) (v : Val) :
    Heap.write h l v l = some v := by
  trace_state
  simp [Heap.write]
EOF
site/tools/goalstate.sh m1 /tmp/s.lean
```

```
h : Heap
l : Loc
v : Val
⊢ h.write l v l = some v
```

Paste that into a `trace` block.

## Keyboard

| key | |
|---|---|
| `/` or `⌘K` | search everything |
| `→` / `j`, `←` / `k` | next / previous chapter |
| `e` | expand every hint, solution and aside on the page |
| `n` | notation drawer |
| `t` | cycle theme |

Progress is stored locally in the browser; `reset` in the sidebar clears it.

---

`../Separation Logic.html` is the original single-file version this site was
built from. It is kept for reference and is no longer maintained.
