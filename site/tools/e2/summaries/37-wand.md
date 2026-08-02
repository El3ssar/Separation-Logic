# Unit 34 · `wand` · Giving a piece away, and getting it back
`site/content/37-wand.js` · 61 blocks (55 non-`ex`), 6 exercises, ~2300 words (≈3.8 screens), 81 KB.
6 `trace` (all in `deep`), 3 `state`, 10 `illustration`, 1 `sketch`, 2 `detail` (none before the
first exercise), 1 each `txt` `svg` `anat` `cmp` `quote` `note key` `note info` `dod`.
**Lean fragment untouched**; §D's seven ⧗ items were already there. No ledger row, no waiver.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean fragment was edited at
review.** All eleven `state`/`trace` states were regenerated with `trace_state` and diffed against
the page (identical, byte for byte, including every metavariable number); all ten `illustration`
blocks were re-extracted by script and recompiled as one file; the `sketch`'s `unsolved goals`
output and all five quoted compiler errors were reproduced by breaking a real proof; every
falsifiable `pitfall`/`variants` claim was compiled.*

## One job
Define `-∗` as the answer to a question the reader already has, prove it right adjoint to `∗`, and
cash the adjunction out as the algebra of a structure with a hole.

## The hook I left (verbatim, final block; §D word for word)
> The assertion language is complete: `emp`, `↦`, `∗`, `-∗`, the classical connectives, recursion.
> The *language* is not — `ite` and `loop` have sat in `Cmd` since Unit 18 and have never been used,
> and the moment they are, a distinction that has been invisible becomes essential.

Opens on `36-lseg`'s hook in four words ("Take the pattern literally"), the hole made concrete as a
node lent out of a `listRep`.

## Introduced
**Tactics: none.** **Syntax:** `infixr:54`, all four parses proved by `example … := rfl`.
**Notation:** `-∗`. **Reading skill:** a `∀` inside an assertion, so `intro` does not stop at the
entailment's three binders; the six- and nine-name `intro` lines are shown split, then joined.
**Names now usable:** `wand`, `wand_intro`, `wand_elim`, `star_wand_adjunction`, `wand_mono`,
`wand_unit`, `hole_intro`, `hole_elim`, `wand_curry`, `wand_uncurry`, `emp_wand_elim`,
`emp_wand_intro`. **Illustration-only, collision-checked against all 39 fragments and every e2
page:** `aImp`, the pointwise lift of `→`; every other snippet is an anonymous `example`.
**Concepts:** adjunction from currying · right adjoint, determined up to `⊣⊢` (compiled, in
`m11-3`'s `deep`) · contravariance · a wand consumes its argument, so it cannot be applied twice to
the same cell · **BI algebra**, in a closed `detail`, each word translated into a proved theorem,
with `wand_elim` named as the **counit** (§D's one remaining "new mathematics" item, added at
review).
**Rejected alternatives, all compiled:** `aImp` — its `aAnd` modus ponens **proved** on the main
line, its `∗` modus ponens refuted, so the diagnosis is "implication across a split", not
"implication" · the cut in the
order the union suggests · `star_mono_right` for `_left` · `disjoint_union_right.mp` on a
left-union · omitting `rw [hu]`, `rw [union_assoc]` · both reversed hypotheses of `wand_mono` ·
`starNoDisj` for `∗` in `wand_intro`/`wand_curry` (survive) and `wand_uncurry` (**breaks**) · the
converse of `wand_unit`.

## Exercises
`m11-1` **wand_intro** [C 2] — currying; the equation slot is `rfl` because the definition put that
union there. `m11-2` **wand_elim** [C 2] — cashing; `rw [hu]` is the content. `m11-3`
**star_wand_adjunction** [C 2] — ⟸ from the two previous lemmas. `m11-4` **wand_mono** [D 2] —
variance. `x68` **wand_unit / hole_intro / hole_elim** [C 2] — the working pattern, two one-line
terms. `x69` **wand_curry / wand_uncurry** [C 3] — the only proof here with heap algebra in it.

## Not explained (earlier summaries own them)
`∗`'s six slots and its `intro` pattern · `⟨…⟩` flattening · `⊢`/`⊣⊢` as folded `def`s ·
`refine`/`obtain`/`subst`/`absurd`/`congrFun` · `pure` vs `fact` · `✝` · proof by composition
(Unit 17) · the `_left`/`_right` naming rule (Unit 16, cited not re-derived).

## Warnings
1. **`check.sh 37` without `--incl` has no `-∗`**: `P -∗ Q` then lexes as `-` and `∗`, giving
   `unexpected token '∗'; expected term`. Not a notation bug.
2. **Three claims corrected on the page.** (a) `union_assoc` plus both bridges are *not* first spent
   together here — `splits_assoc` and `star_assoc_*` already do. (b) Unit 01 does not prove currying;
   it supplies `⟨…⟩` and `.1`/`.2`, and the page compiles the classical `↔` itself. (c)
   `P -∗ (P ∗ R) ⊢ R` is false but **not** at the one-cell heap, where the wand is vacuous *and* the
   conclusion true; the witness is `Heap.singleton 0 5`.
3. **`hole_intro` by hand is three tactics** (`intro`, `refine`, `exact`), and the `exact` is
   `wand_unit`'s proof inlined. The page says three; an earlier version of this summary said four.
4. **Downstream consumers: ZERO for all twelve declarations** (`38-*`…`41-*`, word boundaries). No
   `why` promises a later citation.
5. **Weakest part:** five of six exercises are difficulty 2, and `m11-1`'s and `m11-2`'s first lines
   stand on the main line above them. `x69` alone measures much; §D prescribes the set.
6. **`aForall` already exists** (`17-star-algebra.lean`, unit 15) and `star_forall_left`'s proof
   already `intro`s past an entailment into an assertion's `∀` — but both live in a **closed
   `detail`** on that page, so this page does not lean on them. The `anat` chip therefore claims
   only what is checkable: this is the first assertion in the course quantifying over a heap
   universally. Do not "correct" it to "the first `∀` inside an assertion".

## Deviations
1. 55 non-`ex` blocks against §D's ~28 (ERRATA §18); prose *under* budget.
2. §D asks 2 `trace`; there are 6, one per exercise (PEDAGOGY §7), all in `deep`. `x69`'s shows goal
   lines and new hypotheses only, its 11-line context printed once in an adjacent `state`; the title
   says so (`33-swap`/`35-listrep` precedent).
3. The `note kind:'key'` sits *after* `m11-3`, because it asserts what that exercise's `deep` proves.

## Provenance and checks
Every `state`/`trace` step is `check.sh 37 <snippet> --incl` output byte for byte, `trace_state` for
mid-proof states, `snippet:L:C:` dropped, errors de-line-broken. All nine quoted errors came from
breaking a real proof; seventeen `pitfall`/`variants` snippets compiled separately.

Green: `node --check`; `lint.mjs` **0/0** (61 blocks); `ledger.mjs` **0/0**, sweep 3 (pre-existing)
and `frags` clean, no waivers; `render-check.js` **0**; `verify.sh 37` (2118 lines, 294
declarations); `gen-contexts --prove` **139/139**; `wasm-check.cjs` over prelude-37 `--incl` plus
all ten illustrations **clean**; banned grep **0**; ERRATA §7 `<code>` grep only real citations.

## What review changed
**No Lean fragment, no exercise `id`, `name`, `goal`, `sol`, `walk` step or `trace`/`state` `src`.**
One `illustration` gained a second declaration; everything else is prose, plus one deleted `p`.

**Two internal contradictions.**
- `x69`'s `why` said its two directions were "genuinely different work rather than mirror images of
  one argument"; its own `solNote` three fields later says "the two proofs are mirror images, and
  the mirror is exact". The `solNote` is right — `disjoint_union_left.mp` against
  `disjoint_union_right.mp`, `.mpr` against `.mpr`, `rw [union_assoc]` against `rw [← union_assoc]`.
  The `why` now says the second direction is the first reflected, and says what writing it measures.
  The same field's "the only proof on this page where the heap algebra does real work" also
  contradicted `x68`'s `expl` (`disjoint_symm` and `union_comm` are heap algebra); now "the one
  proof that regroups heaps rather than merely renaming them".
- `x69`'s hint rung 3 said "Six `intro`s". `wand_curry` takes **nine** names, as rung 4 and the
  `walk` both say. Rung 3 now names the shape without the count, which is its job (PEDAGOGY §8).

**A refutation that read as a straw man.** The page defined `aImp`, then refuted
`aImp P Q ∗ P ⊢ Q`, and only a *closed* `detail` at the far end of the unit said that `aImp` is a
perfectly good right adjoint for `aAnd`. A reader stopping at the refutation is entitled to ask
whether implication or the mixing was at fault. `aAnd (aImp P Q) P ⊢ Q` is now compiled in the same
`code` block as the definition (`fun _ _ hpq => hpq.1 hpq.2`), and the paragraph after it pivots on
it: "So nothing is wrong with implication. What has to be tested is implication across a *split*."
PEDAGOGY §5's test — close every aside and the main line still reads — was failing here.

**Two facts wrong in the BI-algebra aside.** (a) It called `aAnd` *and* `aOr` "the classical
monoid"; `aAnd`'s unit is `aTrue` and `aOr` is a second operation, not part of it. (b) It called
assertions "a partially ordered set", when Unit 12 proved entailment is a **preorder** and that
antisymmetry fails — which is why `⊣⊢` exists. Both repaired, the second by saying in one clause
that the object is assertions with `⊣⊢`-equivalent ones identified.

**Machinery the course does not have.** The opening paragraph handed the node to "a subroutine",
twice. `Cmd` has no procedures and the reader knows it (Unit 32 says no program in this course can
even walk a list). Rewritten onto the rules the reader does have: every rule takes one cell and
gives one cell back, so the node leaves the list's description and rejoins it.

**Explained twice.** `m11-4`'s `deep` closed with a `p` re-explaining the doubled turnstile and
`Entails` at precedence 40 — done already in `m11-3`'s trace, one exercise earlier, and the wand's
54 is in the `anat` and proved by `rfl` in the parse block. Cut (61 blocks unchanged; it was nested).

**Padding and dead sentences.** "The failure is diagnostic rather than discouraging" (flourish,
cut). "The first surprise is in the tactic line", which announced a surprise the same sentence then
did not deliver. "The same fact stated forwards:" opening a paragraph that is *not* a restatement —
it is the once-only argument — relabelled as the second consequence. The adjunction paragraph's
closing sentence restated its own previous clause; merged. `cmp` left panel: "there is exactly one
`a` to go round because there is nothing to go round", which parses to nothing; now "a proof is not
a resource; using it does not use it up". "Note where the two conversions have to happen" — PEDAGOGY
§4's `Note that…` row in imperative disguise; rewritten.

**One `orient` bullet made true.** It promised a connective "for which modus ponens is false"; modus
ponens for `aImp` is now proved on the page. It reads "whose modus ponens survives `aAnd` and fails
across a `∗`".

**Checked and left alone.** All six `sol`s, all eleven states, `union_assoc` + both bridges being
spent in exactly this pattern by `splits_assoc` (13-splits) and `star_assoc_left` (18-star-assoc) —
same lemmas, same `.mp`/`.mpr` directions, verified in the fragments — the `_left`/`_right`
attributions (Unit 15 for `star_mono_*`, Unit 16 for `disjoint_union_*`), the 61-block size
(ERRATA §18; prose is under budget), the `note kind:'key'` after `m11-3`, and the exercise set,
which §D fixes.
