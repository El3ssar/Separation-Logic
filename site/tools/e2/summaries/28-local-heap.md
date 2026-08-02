# Unit 25 · `local-heap` · Locality of `write` and `free`
`site/content/28-local-heap.js` · 44 blocks (42 non-`ex`), 2 exercises, 72 KB source / 96 KB
rendered, ~2000 words of main line, 5 `trace` (3 top-level), 5 `state`, 2 `detail` (1 top-level),
1 `steps`, 1 `tbl`.
**Reviewed and revised — see "What review changed" at the bottom.** One Lean change at review:
`write_union_no_disjointness` **moved above the `/- ex m8-2 -/` marker** in
`site/lean/e2/28-local-heap.lean`, so the reader's editor has the lemma the page shows them before
the exercise. No declaration added, renamed or edited. No ledger row added, no waivers.

## One job
The two hardest pointwise heap arguments in the corpus, done slowly — and the discovery that
`write` and `free` spend the disjointness hypothesis in *opposite halves* of the same proof.

## The hook I left (verbatim, final block)
> Five commands are local. A program is not five commands — it is commands glued together with
> `;;`, and three of `Cmd`'s eight constructors are control flow whose locality nothing has yet
> claimed. Sequencing is where the extra conjunct is finally spent rather than only established:
> the first command hands its disjointness to the second, and without it the second could not be
> run on the big heap at all.

§D's "two of the ten constructors" is wrong (`Exec` has five control-flow constructors, `Cmd`
three) and its "Edition 1 never proved them local" is history in the main text. Both repaired.
**`29-local-compose`: the phrase is now "whose locality nothing has yet claimed"** — the earlier
wording said control flow was something "nothing so far has said a word about", which reads as a
claim that Units 18–20 never mentioned `ite` and `loop`. Opens on `27-locality`'s hook in three
words.

## Introduced
**Syntax (my row):** `.trans`, on `hw.trans hh` inside a `rw` bracket (block 13, immediately after
the `trace` that first shows it).
**Also taught:** `have hl' : h l = _ := hl` — restatement **with an underscore**, since the RHS
names an inaccessible `old✝`. The plain form was spent by `25-hoare`/`27-locality`, so the page no
longer re-derives the mechanism; what is new and what the page argues is (a) the `_`, (b) that
**`rw` and a term-level application disagree about a structure projection**. `show` on a heap
equation.
**Names now usable:** `heapLocal_write`, `heapLocal_free`, `write_union_no_disjointness`.
Illustration-only, no row, collision-checked: `write_breaks_disjointness`, `HeapLocalAnyFrame`,
`heapLocalAnyFrame_write`, `not_heapLocalAnyFrame_free`, `heapLocal_write_short`.
**Concepts:** the two obligations of a locality proof, named before any Lean (`steps`) · a
hypothesis kept for *bookkeeping* versus one an *equation depends on* (2×2 `tbl`) ·
`⊢ none = hFrame x` as the whole content of `heapLocal_free` · exclusive ownership as what makes
`free` framable.
**Rejected alternatives, all compiled:** `heapLocal_write_short` (cites the equation instead of
reproving it) · `show` on the whole conjunction right after the inversion, both states, and its
cost · `left` before the split in the write proof (compiles via `absurd`; a worse description) ·
`HeapLocalAnyFrame`, locality with `hd` deleted — **provable for `write`, refuted for `free`**.

## Exercises
`m8-2` **heapLocal_write** [C 4, hard] — disjointness as bookkeeping; `have hl'`; `refine` then
`show`. `deep` traces the disjointness half and folds the raw twenty-line post-inversion goal.
`m8-3` **heapLocal_free** [C 4, hard] — the case where the two heaps meet.

## Warnings — all compiled
1. **§D's central claim is FALSE and I did not repeat it.** Not "the last pointwise heap reasoning
   in the course": `funext` over a heap returns at `33-swap.lean:22` and `34-wp.lean:48,80`. What is
   true, and what the page says: files `29`–`32` contain no `funext`.
2. **`write_union_no_disjointness` has ZERO downstream citations** (grepped). No promise made. It is
   nonetheless now **above** the `m8-2` marker, because the page proves it before the exercise and
   `heapLocal_write_short` cites it; `gen-contexts --prove` re-run green after the move.
3. **Grepped, re-verified at review:** `heapLocal_write` **3** (`30-frame:21`,
   `31-aliasing-closed:22`, `32-symbolic:86`); `heapLocal_free` **3** (`30-frame:29`,
   `32-symbolic:23,107`).
4. **`rw` and application disagree about a structure projection.** `union_of_some hFrame hl`
   typechecks with the *unrestated* `hl`; `rw [hl] at hx` does not. Easy to state backwards.
5. Deleting the free rule's premise makes its equation false **even for disjoint heaps**
   (`Heap.empty` / `Heap.singleton 0 5`) — not merely unprovable.
6. `heapLocal_free` is not the only corpus proof whose `hd` is load-bearing for an equation
   (`union_comm`, `union_cancel_left` are too) — only of the **five command-locality proofs**.
7. `<i>undefined</i>` in prose trips `render-check.js`'s literal-undefined test.
8. `--sweep`'s 3 unrowed names are pre-existing (`25-hoare` warning 8); at review they are
   `and_assoc_iff`, `and_comm_iff`, `emp_iff_all_none`, none of them mine.
9. **There is no `∪` notation in this course.** `Heap.union` has no infix. The first draft used
   `h ∪ hFrame` inside `<code>` spans in two blocks; both are gone. Do not reintroduce it.
10. `heapLocal_write` is **26** lines and `heapLocal_free` **29** — counted, not estimated, and the
    page says both numbers in three places.

## Not explained
`Exec` and inversion, `✝`, the `.heap`-of-a-literal display, `HeapLocal`, `funext`/`by_cases`, the
union and lookup laws, `refine`, `rcases`, `subst`, `absurd`, `Eq.symm`, `cases h : e with`, and
the *plain* definitional restatement (`25-hoare` owns it).

## Deviations
1. Warning 1, and the hook's arithmetic.
2. **42 non-`ex` blocks against ~24** (ERRATA §18); below every Module 5–6 neighbour. Prose at
   budget (~3.3 screens against ~3).
3. **3 top-level `trace` against 4**, **1 top-level `detail` against 2** — PEDAGOGY §5 allows one
   before the first exercise, so the raw post-inversion goal sits in `m8-2`'s `deep`.
4. `write_union_no_disjointness` is on the main line with its trace: §D objective 3 requires the
   reader to *see* that it needs no hypothesis. `m8-2`'s `setup` says so; the exercise is then the
   disjointness half plus the assembly. `m8-3`'s equation is not pre-empted — the main line shows
   only `⊢ none = hFrame x`.
5. One main-line trace state is **9 lines**, one over §6.1; untrimmed, real, and every line in it
   is a one-line hypothesis. Every other main-line state is ≤ 5.

## Provenance
Every goal display was re-extracted at review and re-derived from `check.sh 28` with `trace_state`
(snippets `t1`–`t4`): the six steps of the `write_union_no_disjointness` trace, the post-inversion
and post-`refine` and post-`show` states, the six steps of `m8-2`'s disjointness trace, the five
states of the `free` equation, and the three states of `m8-3`'s disjointness trace — **all match
byte for byte**. Trimmed displays omit unchanged lines and say so; both long raw states sit in
folds, in full. The four quoted compiler messages were each reproduced by breaking the real proof
(`rw [hl] at hx`; the missing `left`; `write_other` with `l ≠ x`; `exact hx` on `none = hFrame x`),
plus the `rw [write_other …]` failure quoted in `m8-2`'s `walk`. Every `pitfall`/`variants` claim
compiled separately, including the mirrored write equation under `h l = none`, the swapped erase
equation under `hd` + premise, and `left`-before-the-split in the write proof. The three
`illustration`s compile as one file through `check.sh 28 --incl`.
Green at review: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` **0/0** with `frags` clean and no
waivers; `render-check.js` **0**; `verify.sh 28` (1533 lines, 228 decls) **and bare `verify.sh`**
(2327/319); `gen-contexts.mjs --prove` **103/103**; banned-phrase grep **0**.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no new Lean. One declaration reordered inside the
fragment; twenty-odd fields rewritten.

**Contract.**
- `orient.payoff` claimed these are "the **only** evidence that the extra conjunct Unit 24 derived
  is payable at all". Unit 24 pays it three times (`skip`, `assign`, `load`). It is the **first**
  evidence from a command that changes the heap — which is what `m8-2`'s `why` already said, four
  screens down.
- *"Every locality proof in this module pays those two the same way"* — false. `heapLocal_seq`,
  `_ite` and `_loop` (Unit 26) pay neither slot that way. Narrowed to the two proofs on this page,
  with the true forward link (`union_of_some` was all of `heapLocal_load`).
- `youWill` promised `show` on "a fifteen-line goal". The goal after the `refine` is **four** lines
  (thirteen with context). Restated as what it is: a goal printed through five projections.
- The `blurb`'s "that difference is what the frame rule is actually made of" was unsupported by
  anything on the page; replaced with the claim the page does prove.

**Facts that were wrong.**
- *"twenty-eight lines against twenty-five"* for `free` against `write`. They are **29 and 26**,
  and the unit's own two `solNote`s said 26 and "three lines longer".
- `heapLocal_write_short`'s caption said "eleven lines become one"; the proof is **26 lines
  becoming 15**, of which 7 are the disjointness obligation and 1 the equation.
- The counterexample paragraph said the run refutes "the last equation of `HeapLocal`". It refutes
  `HeapLocalAnyFrame`'s. Under `HeapLocal` that equation is true — which is the whole point.
- The `detail` was titled *"Both states, with the whole context"* and its prose promised "both
  states in full"; it holds one. Retitled and rewritten rather than padded with a second copy.
- *"`old✝` appears in `hl` and nowhere in the goal"* — it appears in `hl'` as well.
- *"the two `have`s state the obligations in readable form"* — `hl'` states no obligation.

**Goal states.** Two states in `m8-2`'s `deep` trace omitted `hl`, which the `subst` above them
*changes*, while the step's own convention line promised to show any line a step changes. `hl` is
now printed in both (verified), which also puts the restated and unrestated premises side by side
at the moment the section's lesson pays off. `m8-3`'s trace carried the flat claim "context lines
are omitted throughout **and unchanged**"; same defect, fixed in the wording. The quoted `rewrite`
error now says that Lean's re-printed goal display was left off.

**Reader stumbles.**
- **The lemma the page showed them was not in their editor.** `write_union_no_disjointness` sat at
  the *bottom* of the fragment, after both `/- ex -/` markers, so a reader who followed the page
  and typed `heapLocal_write_short` got `Unknown identifier`. Moved above the `m8-2` marker;
  `verify.sh`, bare `verify.sh` and `--prove` all re-run green. The `deep` now says the citation
  compiles in their editor.
- The `free` trace started mid-proof at `⊢ (h.union hFrame).erase x x = …` with no sentence saying
  where `x` came from or which tactics had already run. One clause added.
- `hex'` was named in main-line prose before the solution that introduces it. Replaced by "a
  `.trans` in each branch".

**Prose.** Four "it is worth …" constructions (PEDAGOGY §4's family) cut to one, then to zero. A
paragraph whose only content was that another paragraph followed ("There is a shorter proof … and
it is worth seeing what the corpus version buys by not being it") replaced by its content. The
bookkeeping-versus-equation distinction was stated three times in the same words (blocks 8, 36 and
the closing `note`); block 36 now points at the `tbl`'s prediction and states the sharper fact —
the equation is *false* without `hd`, not merely unprovable — and the `note` keeps the
generalisation. The caption on `have hl' : h l = _ := hl` re-derived a mechanism `25-hoare` taught;
cut to the sentence that is new here.

## Weakest part, honestly
Both exercises transcribe arguments the page has just worked, and rung 4 hands over the opening
lines. The unit is really measured by whether the reader can *say* which half spends which
hypothesis, and nothing tests that: the `tbl` is asserted, illustrated, never asked for. §D allots
exactly two exercises, both corpus, so a third was not written; if the exercise budget is ever
reopened, the missing one is a [G] asking the reader to state and refute locality for `free` under
a frame that owns the freed cell — `not_heapLocalAnyFrame_free` is already the answer, compiled.
`heapLocal_write_short` shows eleven of `m8-2`'s twenty-six lines are avoidable, which undercuts
the exercise it sits inside. `.trans` is never the difficulty anywhere.
