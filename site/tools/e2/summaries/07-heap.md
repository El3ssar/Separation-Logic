# Unit 05 · `heap` · Memory as a partial function
`site/content/07-heap.js` · 44 blocks (40 non-`ex`), 4 exercises, ~1950 words of main-line
`p`/`note`/`dod` prose (~2970 including the four folds and the exercise panels), 5 traces,
4 `detail` — exactly one before the first exercise. 61 KB source, 93 KB rendered.
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Define memory and its four operations, and replace the definitions immediately by six lookup
equations that are the only interface from here on.

## The hook I left (verbatim, final block; contractual, word for word from §D)
> Six equations, and none of them mentions more than one lookup. What happens when you write twice
> to the same cell, or to two different cells? Those two facts are what the assignment rule and the
> frame rule are made of.

## Introduced
**Tactics: none** — deliberate, and the page now says so, in the paragraph opening the six-equation
section.

**Syntax:** `namespace N … end N`, and that outside it the short name does not resolve ·
`structure … where` with a dependent field (`PHeap`, read-only, in a fold; glossed in one sentence,
per ERRATA §2) · dot-notation **display** and *which* operations meet its condition — `Heap.write`
and `Heap.erase` do, `Heap.singleton` and `Heap.empty` do not. §`goalstate` owns the printing
convention itself; this page adds only the four-way verdict.

**Names:** `Heap.empty`, `Heap.singleton`, `Heap.write`, `Heap.erase`, `singleton_same`,
`singleton_other`, `write_same`, `write_other`, `erase_same`, `erase_other`. Illustration-only, in
no fragment: `upd`, `upd_same`, `writeOwned`, `writeOwned_same`, `PHeap`, `everywhere`.

**Concepts:** partial function properly; domain of definition, named against `defined` · the two
readings of `h l = none` and why the model identifies them · deallocation · immutability ("the heap
after the write" is a term, not an event) · **ownership is imposed by preconditions, not by the
model** (first appearance) · the interface discipline.

**Rejected alternatives, each costed:** a three-tag codomain (prose — the argument is now that the
`unallocated`/`elsewhere` distinction is not a property of a heap at all) · one merged `upd` taking
an `Option` (fold; the unprovable `⊢ o = some v`) · `writeOwned : … → Option Heap` (fold; three
lines become nine) · packaged domain `PHeap`, with the `def`-instead-of-`abbrev`
`Decidable (x = l)` failure · finiteness.

**First uses this page moves earlier than §E predicted:** `absurd` (§E.1 says first use 08) and
`Eq.symm` on a hypothesis, both in the closing domain block. The invariant *introduced ≤ first use*
still holds — both are Unit 02/01 rows — and `ledger.mjs` is 0/0. §E's "first use" column is now
stale for `absurd`; nobody downstream depends on it.

## Exercises — all four single `simp` calls, per §D, and the page says why
- `m1-1` **singleton_same** — split into `simp only` steps; the `rfl` failure beside it.
- `m1-2` **singleton_other** — the residue `⊢ ¬x = l`, plus a compiled `↔` proving `simp` reduces
  the goal to exactly that.
- `m1-3` **write_same / write_other** — the residue `⊢ x = l → some v = h x`, and a `cmp` on why it
  gets one step *less* far: `some v = none` is refutable, `some v = h x` is not. §D objective 4,
  and the unit's real lesson.
- `m1-4` **erase_same / erase_other** — deallocation; `deep` carries
  `Heap.erase Heap.empty 3 = Heap.empty`, the first equation between whole heaps.

## Page order (so a successor can find things)
pick up Unit 04's hook → `abbrev Heap` → the two readings of `none` → `note`: the ambiguity is a
decision → the three-tag alternative refused → **sec Four operations** → the four `def`s →
`namespace` + the `#check write` failure → the display verdict + two real goals → the 2×2 `tbl` and
what it predicts → `Heap.empty l = none := rfl` → **fold: why not one `upd`** → **sec domains** →
`dl` of the four domains → `svg` → immutability + two `rfl` lines → `Heap.write` allocates →
`note`: ownership comes from preconditions → **sec six equations** → **m1-1** → **m1-2** →
**m1-3** → fold: `writeOwned` → **m1-4** → fold: `PHeap` → fold: finiteness → **sec the interface**
→ the four domain theorems proved *through the six laws* → `note`: the discipline → `dod` → hook.

## Not explained (previous summaries say it is known)
The `Option` encoding and the packaged-domain argument in the abstract (`00-aliasing`, whose
summary forbids re-running it — my fold asks only what packaging does to the *operations*) · the
display convention (`01-goalstate`) · `↓reduceIte`, the `simp`-vs-`rw` rule (`05-update`) ·
`Nat.decEq`, blocked reduction, `defined` (used, never re-stated), `some_ne_none`, `absurd`
(`03-compute`) · `funext`, `by_cases`, `<;>` (`04-funext`).

## Provenance
**Every `state` and `trace` step is `tools/e2/check.sh 07 <snippet> --incl` output byte for byte**,
`trace_state` where a mid-proof state was wanted, `snippet:L:C:` dropped, nothing elided. At review
every `code` block was re-extracted from the finished file by script and recompiled: the ten
`illustration`s are silent, the six `sketch`es produce exactly the errors quoted beneath them, and
the two `verified` blocks are fragment text (`lint.mjs`). The `def`-vs-`abbrev` sketch is compiled
by bare `lean`, since it redeclares the model, and its caption says so.

Every claim made in prose about a Lean message was recompiled at review as its own snippet: the
four `simp`-bracket mistakes in `m1-1`'s `pitfall` (bare `simp`; `simp [empty]`; `simp [singleton]`;
`simp [Heap.singleton l v]`), both hypothesis reversals, the `some w` variant reducing to `⊢ False`,
the unused-binder warning on `(hd : defined h l)`, `Unknown identifier \`hne\`` across a declaration
boundary, and the four "and then it stops at" residues in `m1-4`. Rule counts (two rules for
`singleton_same`, three for `singleton_other`) came from `simp?`.

## Deviations from COURSE-PLAN.md
1. **40 non-`ex` blocks against §D's ~28**, at §C's ceiling; main-line prose is *under* budget
   (~1950 words ≈ 3.3 screens against ~4). ERRATA §18. The excess is compiled exhibits.
2. **No `defn` card per operation** (§D asks four). The 2×2 `tbl` and the `dl` of domains do that
   work; a third pass would restate it. Recorded, not fixed.
3. §D moves `PHeap` and the `abbrev`/`def` exhibit here from `00-overview.js`. Both are here, in
   one fold, subordinated to a question this unit owns.
4. §D says the unit sits after "the `funext` lab". Unit 04 (`05-update`) introduces **no** tactics;
   the `funext` unit is 03. The page therefore states the no-new-tactic fact without attributing a
   reason to a mislabelled neighbour.

## Warnings to successors
- **`simp [singleton]` does not say `Unknown identifier`.** It silently resolves to core's
  `Singleton.singleton` and reports `` `simp` made no progress ``; `simp [empty]` and `simp [erase]`
  *do* name the unknown. A dropped namespace fails loudly for three operations and quietly for one.
  ERRATA §7's library collision, hit for real.
- **`Heap.singleton l v l = v` typechecks and is the same theorem** — Lean inserts the `some`
  coercion. An earlier draft of this page claimed a type error; it is not one.
- **An unused *binder* is warned about:** `Variable name \`hd\` is not explicitly referenced.`
- **`by …` in a term-mode slot is booked at `17-star-algebra`**, so `⟨v, by simp […]⟩` fires the
  ledger. Where a witness needs a proof, cite a named theorem — `⟨v, write_same h l v⟩` — or use
  `have hv : … := by …` then `exact ⟨v, hv⟩`.
- **A `cmp` side's `src` renders with a tag strip**, so it must be Lean; goal states go in `h`.
- **Author of `08-heap-laws`:** my closing `note` promises your lab is the *last* place a heap
  operation may be unfolded, and corpus `write_shadow`, `erase_write_same`, `write_singleton`,
  `erase_singleton` all unfold. `write_of_eq` is the one corpus proof citing `write_same` /
  `write_other` by name — your best evidence for the interface. The closing block of *this* page is
  now the other piece of evidence: four domain theorems proved with no definition named.
- **Weakest part, honestly:** four [D 1] exercises whose rung-4 hints are the answer, so the unit
  measures no proof skill — §D's instruction, but it puts everything load-bearing in `m1-3`'s *Why
  it works*. For an exercise with teeth, `Heap.erase Heap.empty 3 = Heap.empty` sits unused in
  `m1-4`'s `deep`, and so do the four domain theorems at the foot of the page.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **The answer to half of `m1-3` was printed three sections before the exercise.** The domain
  section's `code` block contained
  `have hv : Heap.write h l v l = some v := by simp [Heap.write]` — which *is* `write_same`,
  statement and proof — and `simp [Heap.erase] at hv`, which is `erase_same`. Same defect
  `02-terms`' review fixed. The block is gone from there. In its place, at the foot of the page,
  four domain theorems proved **through the six equations** (`singleton_same`, `singleton_other`,
  `write_same`, `erase_same` + `some_ne_none`), naming no definition at all. This costs one block
  and buys the interface note its evidence, which it previously asserted.
- **A `code` block that does not compile was tagged `illustration`.** `#check Heap.write` /
  `#check write` — the second line is the whole exhibit and it errors. Retagged `sketch`, the
  convention every other error-producing block on this page and on `06-errors` already follows.
- **A wrong count.** `m1-3`'s `why` said the pointwise reasoning is done "three units early". The
  assignment rule is Unit 23, eighteen units later; §D Unit 06 objective 4 says *three lines*. The
  sentence now says what it is for: Unit 23's proof is three lines and contains no conditional.
- **A second wrong count.** The `writeOwned` fold said "three lines became ten"; the theorem is
  nine lines.
- **A garbled clause in the `dod`.** "say why the model keeps them apart from nothing" — it means
  the model does *not* separate them. Now matches `orient.youWill`.
- **An assertion where the argument was the point.** The three-tag codomain was refused because
  "neither question has an answer that is stable under adding more memory", which is the conclusion
  and not the reason. The reason — the `unallocated`/`elsewhere` distinction is not a property of a
  heap, because it depends on who else is there — is now on the page.
- **A second paragraph on the dot-notation display**, which `01-goalstate`'s summary explicitly
  asked this unit not to write. Cut to what is new here: which of the four operations meet the
  condition, and which print in full.
- **A re-definition of `defined`.** "Unit 02 already gave you the predicate that names it:
  `defined h l` is `∃ v, h l = some v`" — a `recall that` in all but the words. The name is now
  used without ceremony.
- **An inconsistency between prose and exhibit.** The prose said "three of the four descriptions
  are theorems" while the exhibit proved the `Heap.empty` one and skipped `Heap.singleton`. The
  prose now says which one is not a theorem, and the exhibit proves the other three (four
  statements, since the singleton claim is two-sided).
- **`orient.needs` claimed the three-move shape as an inheritance.** ERRATA §23: that shape is
  spent in Unit 06, not here; `funext` occurs on this page once, in a fold. The bullet now names
  `update_same`/`update_other` and the residue, which is what the unit actually consumes.
- **The contractual "this unit introduces no new tactic" was never said to the reader.** One clause
  now, in the lead-in to the six equations.
- Minor: "on a page where three more operations join `Heap`" → *in a course where* (they join at
  Unit 08, not here); "a second type gets one of its own" → *a namespace of its own*; "Unit 00
  fixed" → *settled*; "one `rfl` short of being free, and here is exactly how short" (which says
  nothing) rewritten; `m1-1`'s "your first proof at the longer type" → *with `Option` in the
  codomain*; `m1-2` hint 4's "which one it is is the subject of"; a `variants` hypothesis named `h`
  on a page where `h` is always a heap, renamed `hx` and recompiled.

## Checks — all green
`node --check` · `lint.mjs` 44 blocks, 0 errors, 2 warnings (multi-theorem `goal` fields, the `x08`
pattern; expected) · `ledger.mjs 07-heap` 0/0, whole-edition 0/0, `--sweep` clean, **no
`ledgerAllow` and no `ledgerForward` needed** · `render-check.js` 0 problems · `verify.sh 07` clean
(225 lines, 54 declarations) · banned-phrase grep and the widened sweep (`obvious`, `worth …-ing`,
`just`, `simply`, `essentially`, `it turns out`, first person plural) clean · every `code` block
re-extracted and recompiled through `check.sh 07 --incl`, every `state` and `trace` re-diffed
against the output. **The Lean fragment was not touched** — all four exercises were already
verified corpus, and every new exhibit is an `illustration`.
