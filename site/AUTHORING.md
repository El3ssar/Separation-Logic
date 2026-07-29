# Authoring guide

The site is static. No build step, no bundler, no dependencies. Open
`site/index.html` in a browser and it works — including straight off the disk
with `file://`.

```
site/
  index.html          shell: sidebar, topbar, search box, notation drawer,
                      and the <script> tags that load the chapters (in order)
  assets/
    base.css          the original workbook design system
    blocks.css        styles for the v2 block types
    app.js            the whole engine: renderer, search, progress, theme
  content/
    00-overview.js    one file per chapter; each calls registerChapter({...})
    01-m0.js
    ...
    16-ref.js
  lean/
    corpus.lean       every definition and proof M0–M13, verified as one file
    prelude/*.lean    cumulative context up to each chapter, for testing snippets
```

To add a chapter: write `content/NN-id.js`, add a `<script>` tag to
`index.html` in the right position. That is the whole procedure.

---

## The chapter object

```js
registerChapter({
  id:    'm4',                       // stable; used for the #hash deep link
  num:   'M4',                       // sidebar badge; '§' for non-modules
  phase: 'Phase 1 · Semantic foundations',
  title: 'Separating conjunction',
  blurb: 'One sentence, plain, saying what this chapter is for.',

  orient: {                          // optional but recommended
    youWill: ['html', 'html', ...],  // concrete capabilities, not topics
    needs:   ['html', ...],          // what must already be solid
    payoff:  'html'                  // one sentence: why this matters later
  },

  blocks: [ /* see below */ ]
});
```

`id` and every exercise `id` are **load-bearing**: reader progress is stored
against exercise ids, and `#m4` in the URL jumps to that chapter. Never
renumber them.

---

## Blocks

Every block is `{t: '<type>', ...}`. All `h`, `s`, `title`, `cap` and list-item
fields are **HTML strings** — use `<code>`, `<b>`, `<i>`, `&amp;`, entities, and
so on. Code `src` fields are **plain text**, escaped by the renderer.

### Prose

| block | fields | notes |
|---|---|---|
| `p` | `h` | a paragraph |
| `h3` | `s` | section heading, appears in the in-page TOC |
| `h4` | `s` | small uppercase sub-heading |
| `sec` | `s` | major divider rule, appears in the TOC |
| `ul` / `ol` | `items: [html]` | |
| `quote` | `h` | pull-quote on an accent background |

### Code

| block | fields | notes |
|---|---|---|
| `code` | `src`, `cap?`, `tag?` | Lean, syntax-highlighted |
| `txt` | `src`, `cap?` | schematic / pseudo-notation, not highlighted |
| `state` | `src`, `cap?` | a raw Lean goal display |
| `svg` | `src`, `cap?` | inline `<svg>`; wrap contents in `<g class="dg">` |

`tag` labels the strip above a Lean block and is a **truth claim**:

- `'verified'` (default) — this exact text is in `lean/corpus.lean` and compiles.
- `'illustration'` — a new snippet, compiled against the chapter prelude.
- `'sketch'` — deliberately incomplete or schematic; does not compile alone.

Never tag something `verified` that you did not check.

### Callouts

| block | fields |
|---|---|
| `note` | `kind: 'info'\|'warn'\|'key'\|'tip'`, `title?`, `h` |
| `dod` | `h` — the "definition of done" that closes a chapter |
| `defn` | `term?`, `h`, `cap?` — a formal definition card |

### Structured

**`steps`** — a numbered walkthrough. `h` may be an HTML string *or* an array
of nested blocks, so a step can contain code.

```js
{t:'steps', title:'How the proof goes', items:[
  {k:'Fix a location', h:'<code>funext x</code> reduces …'},
  {k:'Split on x = l',  h:[{t:'p',h:'…'},{t:'code',src:'…'}]}
]}
```

**`tbl`** — `{t:'tbl', head:[html], rows:[[html,...]], cap?}`

**`dl`** — a term list. `{t:'dl', items:[{k:'term', h:'meaning'}]}`

**`cmp`** — two columns side by side, ideal for right-vs-wrong or maths-vs-Lean.

```js
{t:'cmp',
 left: {t:'What a mathematician writes', h:'…', kind:'good'},
 right:{t:'What Lean needs',            h:'…', src:'…'}}
```
`kind` may be `'good'`, `'bad'`, or omitted. `src` adds a code block.

**`trace`** — *the most valuable block in this vocabulary.* It shows the goal
state after each tactic, which is exactly what a Lean beginner cannot see when
reading a proof on a page.

```js
{t:'trace', title:'write_shadow, tactic by tactic',
 start:'⊢ Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂',
 steps:[
   {tac:'funext x',
    state:'x : Loc\n⊢ Heap.write (Heap.write h l v₁) l v₂ x = Heap.write h l v₂ x',
    h:'Both sides are functions, so it is enough to …'},
   {tac:'by_cases hx : x = l',
    state:'case pos\nhx : x = l\n⊢ …',
    h:'…'}
 ],
 done:'No goals.'}
```
`state` is plain text, rendered monospaced with newlines preserved. Write the
state the way Lean actually prints it: hypotheses first, then `⊢ goal`.

**`anat`** — code with its pieces called out one by one.

```js
{t:'anat', src:'theorem foo (h : A) : B := by\n  simp [bar]',
 parts:[
   {m:'(h : A)', h:'A named hypothesis. In Lean a hypothesis is …'},
   {m:'simp [bar]', h:'…'}
 ]}
```
`m` is the literal token, rendered as a chip; keep it short and copy it exactly
from `src`.

**`detail`** — a collapsible aside holding nested blocks. Use for genuine
digressions, not for hiding things the reader needs.

```js
{t:'detail', title:'Why Lean needs DecidableEq here', tag:'aside', open:false,
 blocks:[{t:'p',h:'…'},{t:'code',src:'…'}]}
```

---

## Exercises

```js
{t:'ex',
 id:   'm1-5',            // NEVER change: reader progress is keyed on this
 name: 'write_shadow',    // NEVER change: it is the theorem name
 hard: false,             // true adds a "substantial" badge

 why:   'html — why this exercise exists, what it buys you later',
 setup: 'html — optional: what is in scope, what you may use',
 goal:  'lean statement, verbatim from the original',

 hints: ['html', 'html', ...],   // graded, first nudge to near-giveaway
 hint:  'html',                  // single hint; use hints[] when you can

 sol:     'lean proof, verbatim from the original',
 solNote: 'html — optional remark placed under the solution',

 // --- the "Why it works" panel, in render order ---
 expl:    'html — a short summary paragraph',
 walk:    [{tac:'funext x', h:'html'}, ...],   // line by line through `sol`
 deep:    [ /* any blocks: trace, steps, cmp, code, detail, … */ ],
 pitfall: 'html — the mistake a reader will actually make here',
 variants:'html — what breaks if a hypothesis is dropped or reversed'
}
```

The reader sees three buttons: **Hint**, **Solution**, **Why it works**. The
third one holds `expl`, `walk`, `deep`, `pitfall`, `variants` in that order, so
depth costs the reader nothing until they ask for it.

`goal` and `sol` are **verbatim quotes of verified Lean**. Do not reformat,
rename, re-indent, or "improve" them. Everything you want to say about the
proof goes in the surrounding fields.

---

## House rules

1. **The Lean is fixed.** Definitions, theorem statements, and proofs are
   already machine-checked. Explanations wrap around them; they never edit them.
2. **Explain the Lean, not the mathematics the reader already knows.** The
   audience is a working mathematician. They know what a partial function is.
   They do not know why `simp [Heap.write, hx]` closes a goal, what `<;>` does,
   why `funext` is needed at all, or how to read `case pos`.
3. **Show the goal state.** Whenever a proof has more than two tactics, a
   `trace` block earns its place.
4. **Name the moving part.** "This is where non-aliasing enters" beats "now we
   apply the hypothesis".
5. **Say what would go wrong.** A rule the reader cannot break is a rule they
   have not understood.
6. Keep the prose in the register of the original: direct, unpadded, second
   person, no cheerleading.

---

## Checking your work

```bash
node --check site/content/07-m6.js       # syntax
node site/tools/validate.js              # schema + ids + Lean fidelity
```

To test a Lean snippet you wrote yourself, append it to the matching prelude:

```bash
cat site/lean/prelude/m6.lean my-snippet.lean > /tmp/t.lean && lean /tmp/t.lean
```

Silence means it compiled.
