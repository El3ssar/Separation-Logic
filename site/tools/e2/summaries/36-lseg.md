# Unit 33 · `lseg` · LAB — segments and append
`site/content/36-lseg.js` · 59 blocks (55 non-`ex`), 4 exercises, 91 KB source / 126 KB rendered.
5 `trace` (1 main line, 1 per exercise), 8 `illustration`, 1 `svg`, 2 `cmp`, 1 `note warn`,
5 `detail`, 4 `state`, 1 `txt`, 1 `dod`.
**Lean fragment untouched — by the author and by review.** Every exercise's Lean, including §D's two
⧗ items, was already there. No ledger row, no waiver.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean fragment was edited at
review.** All five traces, all four `state` blocks and all six quoted compiler errors were
re-derived from Lean and diffed against the page (0 unmatched, including every metavariable number);
all eight illustrations were recompiled as one file through local Lean **and** through the reader's
Lean; every falsifiable `pitfall`/`variants` claim was compiled.*

## One job
Define the piece of a list between two addresses, prove that two adjacent pieces make one by an
induction whose inductive step is done entirely in the assertion algebra, and let a proof that will
not close say which clause of the definition was wrong.

## The hook I left (verbatim, final block; §D word for word)
> `lseg` describes a list with its tail removed — a structure with a hole, where the hole is
> described by another assertion. *I have given away part of my data structure, and here is how to
> put it back* is a pattern that recurs constantly, and it has a connective of its own.

Opens on `35-listrep`'s hook in four words ("Take the traversal seriously"). §D's hook for Unit 32
says *neither* piece of a traversal is a complete list, which is loose — the piece in front of `cur`
is one. The opening paragraph now **refines** rather than contradicts it: "Of the two, one is
describable with what you have."

## Introduced
**Tactics: none.** `induction xs with | nil | cons x xs ih` and `++` get their first real use, as
§E predicts. **Notation, syntax: none.**
**Two display forms glossed here, both first occurrences in the whole course** (grepped across all
38 e2 pages): `xs.append ys` — `++` is notation for `List.append`, then the goal-display support
page's `N.f a b` → `a.f b` convention — and the binder printed `x_1`, because `star_exists_left`
does not carry the definition's binder name and Lean's fallback `x` is taken. Both are glossed in
the worked example's `trace`, at their first appearance.
**Names now usable:** `lseg`, `aExists_mono`, `lseg_nil_iff`, `lseg_append`, `lseg_listRep`,
`listRep_null`.
**Illustration-only, in no fragment, collision-checked against all 39 fragments and every e2 page
(zero hits):** `lsegOne`, `lsegNe`, `lsegBare`, `lsegBare_append`, `lseg_append_semantic`. All else
is anonymous `example`.
**Concepts:** list segments · **half-open ownership** — `finish` is owned by neither side, which is
what makes joining possible · monotonicity under a binder · induction on *data* against Unit 20's
induction on a derivation · **a condition in a recursive assertion must be one the recursion
preserves** (`note warn`) · debugging a definition by the theorem you cannot prove, and upgrading
*unprovable* to *false* with a witness · the traversal invariant and its maintenance step.
**Rejected alternatives, all compiled:** closed segments (prose; the junction node is claimed twice
and `∗` cuts into *disjoint* halves) · `start ≠ finish` (`lsegNe`) · no condition (`lsegBare`) ·
**the semantic route to the `cons` case — now shipped as a compiled 13-line proof**
(`lseg_append_semantic`) beside the 18-line context it starts from · `star_assoc_left` first ·
`induction` with everything introduced.

## Exercises
`x66` **aExists_mono / lseg_nil_iff** [D 2] — get under a binder; the heap must not be named `h`.
`m10-4` **lseg_append** [C 4, hard] — the classical theorem; `intro xs` and nothing else; the `nil`
case is the only one touching heaps. `m10-5` **lseg_listRep** [C 3] — the same proof against
`listRep`; the identity of the two proofs is the evidence. `x67` **listRep_null** [G 3] — state it;
`pure` beats `fact`; `cases`, not `induction`.

## Not explained (earlier summaries own them)
`∗`'s slots and `intro` patterns · `⟨…⟩` flattening · `_root_.pure` · `✝` and its superscripts ·
`refine`/`obtain`/`subst`/`absurd`/`cases` · `pure` vs `fact` · `generalizing` · `Sort u` · `⊣⊢` ·
dot notation · `::` binding tighter than `++`.

## Warnings
1. **`lseg_append`'s first tactic line is a no-op.** `star_mono_left _ (entails_refl …)` improves
   the left conjunct to itself; the proof compiles without it, and `lseg_listRep` omits it. Quoted
   verbatim as required; the page says it does nothing and gives that evidence. So §D's "five lines,
   five named Module 3 lemmas" is really **six** argument lines using **four** distinct lemmas —
   `star_exists_left`, `aExists_mono`, `star_assoc_left`, `star_mono_right` — glued by
   `entails_trans`, and only **three** of the four are Module 3's; `aExists_mono` is proved on this
   page. The page states the real counts everywhere, `orient` included.
2. **§D understates the bug.** Under `start ≠ finish`, `lseg_append` is not unprovable but **false**:
   `lsegNe [7] 1 3 ∗ lsegNe [8] 3 1` is satisfiable and `lsegNe [7,8] 1 1` asserts `1 ≠ 1`.
   Compiled. The correct `lseg` *does* admit a cyclic segment — `lseg [7,8] 1 1` demands only
   `1 ≠ 0` — and excluding lassos is `listRep`'s job. The page says so rather than over-claiming.
3. **A third candidate §D omits, and it is needed.** Dropping the conjunct makes `lseg_append`
   *shorter*, so that theorem alone does not justify the clause — `lseg_listRep` does. Both
   refutations compiled. **At review this moved into the main line**: §D promises three candidates,
   and with every `detail` closed only two were being decided (PEDAGOGY §5).
4. `by simp` reduces `1 ≠ 3` to `True` and leaves `fact (fun x => True) σ Heap.empty` open; a `pure`
   slot needs `by simp [fact]`.
5. **Author of `37-wand`:** `lsegOne` and the maintenance step
   `lseg visited p cur ∗ (pure (cur ≠ 0) ∗ node cur x n) ⊢ lseg (visited ++ [x]) p n` are compiled
   on my page and in no fragment. Cite as illustrations or reprove. Same for
   `lseg xs p 0 ⊣⊢ listRep xs p`, whose **both** directions are compiled here (in `m10-5`'s `deep`).
6. ERRATA §28 bites `theorem … : lseg [] p q = pure … := rfl` (accepted locally, refused in the
   browser). One clause in `x66`'s `deep` says so, citing Unit 32.
7. **Metavariable numbers in quoted errors are context-dependent, and every one here was
   reproduced.** `?m.118`/`?m.116` in the `star_assoc_left`-first error appear only if the no-op
   line precedes it; `?m.127` in the `lsegNe` error only if the `nil` branch is written out rather
   than `sorry`ed. A successor who re-derives one of these from a shortened snippet will get
   different numbers and should not "fix" the page.
8. **Weakest part, honestly:** `m10-4`'s inductive step is worked in full above the exercise, as §D
   mandates, so the exercise measures the `nil` case and the `intro xs` discipline. Algebraic
   fluency is measured only by `m10-5`, where it is a transcription. Review did not repair this
   because §D fixes both the exercise set and the worked example's placement.

## Deviations
1. 55 non-`ex` blocks against §D's ~22 (ERRATA §18); 5 `trace` against §D's 2 (PEDAGOGY §7 asks one
   per exercise). 126 KB rendered is mid-pack for Modules 7–8 (88–141 KB).
2. §C.1's "at most one sentence of prose between exercises" is broken between `m10-5` and `x67` by
   the wrong-definition section, which §D mandates and which must follow both theorems.
3. Counts corrected (warning 1); one rejected alternative added (warning 3).

## Provenance
Every `state`/`trace` step is `tools/e2/check.sh 36 <snippet> --incl` output byte for byte,
`trace_state` for mid-proof states, `snippet:L:C:` dropped, in-sentence errors de-line-broken with
backticks round sort names removed. Where a trace shows goal lines only, the title says so and the
omitted context is printed once in an adjacent `state` — and that `state` now carries its real
`case cons` line, so the counts in both trace titles are counts of what Lean printed.

Green: `node --check`; `lint.mjs` **0/0** (59 blocks); `ledger.mjs` **0/0** for this file, sweep 3
(pre-existing) and `frags` clean, no waivers; `render-check.js` **0**; `verify.sh 36` (2045 lines,
282 declarations); `check.sh 36 --incl` on all 8 illustrations as one file **silent**;
`wasm-check.cjs` on prelude-36 `--incl` + all 8 illustrations **clean**; banned grep **0**.

## What review changed
**No Lean fragment, no exercise `id`, `name`, `goal`, `sol` or hint rung, no `trace` or `state`
`src` except one added `case cons` line.** Everything else is prose, plus one new `illustration`
and two cut blocks.

**Facts that were wrong.**
- **"The correct definition refuses the same heap … so the two pieces are segments under it too."**
  A sentence that says the opposite of what it means, in the lasso aside. The correct `lseg`
  *accepts* the heap and nothing false follows, because `lseg [7,8] 1 1` demands only `1 ≠ 0`.
  Rewritten with the reason spelled out.
- **"Unit 07 named the phenomenon: an assertion no state satisfies makes every entailment out of it
  true."** Unit 07 has no entailment relation — Unit 12 is where `aFalse ⊢ P` is proved in one line.
  Re-attributed, and the `cons` clause at address `0` is now named as `aFalse` in disguise.
- **`cap`: "Two lists of arguments, three of them addresses."** `lseg` takes one list and two
  addresses. Now "Three arguments, two of them addresses."
- **"made entirely of lemmas you proved in Units 12 to 17"** — `aExists_mono` is proved on this
  page, in the exercise immediately above. Repaired in the brief and in `orient.youWill`, which also
  said "six lines of Module 3 lemmas" and, in another bullet, "the same five lines" where the page
  says six.
- **"Four of the five names it cites … are about `Heap`."** All five are.
- **"the next two exercises are what do"** justify the non-nullness clause. One does: `m10-5`.
- **"the two clauses have the same three conjuncts in the same order"** (`lseg` cons against
  `listRep` cons) — the third conjunct is the one place they differ, which is the point of `m10-5`.
- **"it costs one character"** / **"one character shorter to prove"** for `fact` against `pure` in
  `x67` — it costs one *component* of a pair.
- **"Both branches of the goal are `pure`s"** — premise and goal, not two branches.
- **"the refutation … by chasing the second node's address out of the union and finding the heap has
  nothing there"** (`m10-4` `variants`, the `aAnd` witness). Recompiled at review: the head node's
  next field can only be `1`, and the second node then needs the cell at address `1`, which the head
  node already owns — the two halves of the conclusion's `∗` are not disjoint. Description fixed.
- **"Unit 14's `no_star_duplication` is exactly the reason"** two closed segments cannot be joined.
  It is the same phenomenon, not the reason; the reason is that `∗` cuts into disjoint halves. Both
  now said, in that order.
- **Trace title "the seven context lines are those of the worked example with the two occurrences of
  `lseg` replaced"** (`m10-5`) — `r` is gone too, and the seventh line is the `n` that
  `aExists_mono` adds. Same repair on the `lsegNe` `state` caption; the worked example's own `state`
  gained its real `case cons` line and its trace title went from five context lines to six.

**Claims that were unbacked and are now compiled.** "It works, and here is what it costs", of the
semantic route, asserted a proof nobody had written. The 13-line `cons` branch is now on the page as
an `illustration` inside the same aside, and the main line quotes the real ratio, 13 against 6. The
converse of `lseg xs p 0 ⊢ listRep xs p` was described in prose as making the two definitions the
same object while only one direction was shown; the second direction is compiled and shipped beside
the first.

**Two things a reader would have stopped at, now glossed.** `xs.append ys` and `x_1` are the first
occurrences of either in the whole course, and the reader who wrote `xs ++ ys` gets both back in the
same goal line with no explanation. One clause each, in the trace step where each first appears.

**Prose cuts.** One `p` announcing the `cmp` that follows it ("Setting them side by side is the
fastest way to see how small the change is") — PEDAGOGY §4's *paragraph whose only content is that
another paragraph follows*, and its factual half ("two clauses differ") was vacuous, since `lseg`
has exactly two clauses. One `p` inside `m10-4`'s `deep` giving the retrospective's first answer in
the retrospective's own words, three blocks before the retrospective asks the question. One
third-person "the reader has already proved it" made second person.

**Not changed, and why.** The 59-block size stands (ERRATA §18). All four exercises keep their
§D-prescribed ids, names, kinds, difficulties and Lean. The no-op first tactic line of `lseg_append`
stays, quoted verbatim, with the page saying it does nothing — PEDAGOGY §9 forbids editing shipped
Lean and the honest note is the alternative. The worked example still sits above `m10-4`, so that
exercise still measures less than it looks (warning 8); §D mandates both.
