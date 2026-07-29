# Separation Logic in Lean 4 — a mathematician's workbook

A self-teaching course: build a separation logic from nothing, in Lean 4, with
every proof machine-checked.

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

Opening `site/index.html` straight off disk mostly works, but some browsers
refuse to run local scripts from `file://`, so the server is the reliable route.

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
  tools/
    serve.py          static server with caching off
    validate.js       schema, Lean fidelity, and teaching-depth checks
    render-check.js   renders every chapter headlessly and checks the HTML
    goalstate.sh      print the real Lean goal state at any point in a proof
    baseline.json     the original course, for fidelity comparison
    _src/*.md         the original chapters in readable form
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
```

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
