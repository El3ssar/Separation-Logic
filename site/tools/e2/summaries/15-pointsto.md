# Unit 13 · `pointsto` · `emp`, `↦`, and exact ownership
`site/content/15-pointsto.js` · 45 blocks (43 non-`ex`), 2 exercises, ~2040 words of main-line prose
(≈3.3 screens — §D's budget is ~3), 4 traces, 1 `detail` (the one allowed before the first
exercise). 48 KB rendered. Fragment extended by one theorem (`x30`); one `ledger.json` row added.
*Reviewed and revised — see "What review changed" at the bottom. The Lean fragment was not touched
at review.*

## One job
Answer Unit 07's question with a definition, and prove the first two theorems that are about
ownership rather than about truth.

## The hook I left (verbatim, final block; word for word from §D)
> `l₁ ↦ v₁` and `l₂ ↦ v₂` each claim to own *all* of the heap they are evaluated at, so
> `aAnd (l₁ ↦ v₁) (l₂ ↦ v₂)` is nearly always false and is never what you mean. Saying “I own this
> cell *and separately* that one” needs a conjunction that divides the heap between its conjuncts.
> There is exactly one way to write it, and Module 2 has already proved everything it needs.

**The hook is compiled, not asserted.** The block above it proves
`aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ aFalse` for `l₁ ≠ l₂`, and `m3-1`'s `deep` proves it for `v₁ ≠ v₂`.
`16-star`'s author inherits a reader who has *seen* classical conjunction fail on two cells.
Opens on `14-assertions`'s hook in its first four words.

## Introduced
**Tactics: none.** `subst` gets its first use on a hypothesis that is only *definitionally* an
equation; `Option.some.inj` (row at `03-compute`) is first **needed** here, as §E.2 predicts.

**Syntax:** `infix:60`, with its two comparisons — 40 (`⊢`) and the 55 `16-star` will take. The `∗`
glyph is **not** used, only the number, so no waiver was needed.  **Notation:** `↦`.

**Names now usable:** `emp`, `pointsTo`, `pointsTo_value_unique`, `pointsTo_not_emp`,
**`emp_iff_all_none`**. Illustration-only, in no fragment: `empPointwise`, `exact_entails_loose`,
`loose_not_entails_exact`.

**Concepts:** **exact ownership, decided** (`note kind:'key'`) · the **first-person reading**
(`quote`), used to predict two entailments before either is proved · an assertion written as an
*equation* on the heap, and what that buys later proofs — `subst`, `rw`, `congrFun` all reach
through the folded `def` · a machine-checked **non-entailment**, its *shape* (choose the store,
choose the heap, supply the premise, refute what comes back — **in the main line**, not in the
fold), and what it is evidence of: an unfinished proof is a fact about you, `¬ (P ⊢ Q)` is a fact
about the logic and is the kind a later proof can cite.

**Rejected alternatives, all compiled:** the pointwise spelling of `emp` (two lines against four on
one small fact; `x30` then proves the two agree, so the cost *is* the argument) · “the domain is
empty”, shown to be that spelling in other clothing · `v₁ = v₂` to the right of `⊢` · **two
strengthenings of `pointsTo_value_unique`'s conclusion** — `aAnd (fact …) emp`, which is false, and
`aAnd (fact …) (l ↦ v₁)`, which is true and is `and_left` with extra steps (both compiled at
review, in prose, no block) · the loose reading as `↦` — `x16`+`x17` repackaged as
`¬ (ptsAtLeast 4 3 ⊢ (4 ↦ 3))`, in the single `detail`.

## Exercises
- `m3-1` **pointsTo_value_unique / pointsTo_not_emp** [C 3] — two traces; `deep` carries the
  `subst`+`congrFun` alternative proof and the `v₁ ≠ v₂` corollary. Both theorems are now motivated
  in the main line before the box.
- `x30` **emp as “nothing anywhere”** [**G** 2] — ⧗ in §F; written, compiled, added to the fragment
  as `emp_iff_all_none`, using ERRATA §22's placeholder-`goal` pattern.

## Deviations from COURSE-PLAN.md
1. **`x30` is [G], not [D].** §D's table says `D`; §F row 54 and §F.1 both say **G** (“eleven design
   [G] exercises… `x30` (M3)”), and M3 has no other. §D is internally inconsistent and §F is the
   specific claim, so [G] it is. Statement revealed at rung 3, per PEDAGOGY §8.
2. **43 non-`ex` blocks against §D's ~22**; prose ~3.3 screens against ~3. ERRATA §18. Below every
   Module-2/3 unit so far (`12-pcm` 58, `14-assertions` 66, `13-splits` 43).
3. §D asks 1 trace; there are 4 (PEDAGOGY §7 — two proofs, `subst`, `x30`).
4. **Objective 5 lands outside the exercise.** No corpus proof here uses `subst`; the main line
   teaches it on a compiled illustration and `m3-1`'s `deep` shows the alternative proof that uses it.

## Warnings to successors
- **Downstream consumers, grepped, not guessed.** `pointsTo_not_emp` is cited **once** in the whole
  corpus — `17-star-algebra.lean:103`, the last line of `star_not_weakening`. `pointsTo_value_unique`
  and `emp_iff_all_none` have **none**. `m3-1`'s `why` claims exactly that one citation; keep it true.
- **`star_not_weakening` (Unit 15) is the frame rule's reason, `no_star_duplication` is not.**
  Both the payoff and `m3-1`'s `why` previously credited the pair; they now credit the first only.
  `16-star.lean` has exactly two non-entailments, `no_star_weakening` and `no_star_duplication`.
- **`⊢ ¬l ↦ v ⊢ emp` is real output** — two turnstiles, no brackets. The page teaches the display
  before the exercise that produces it. Do not "fix" it. `x30`'s trace shows the companion case:
  `⊢ (fun x h => ∀ (l : Loc), h l = none) ⊢ emp`, where a lambda on the **left** of `⊢` keeps its
  brackets because a `fun` body runs as far right as it can.
- **`rfl` proves the premise of `l ↦ v` at `Heap.singleton l v`** inside an exported `theorem`
  (`15-pointsto.lean:19`), unfolding a plain `def`. Both kernels accept it: ERRATA §28 bites on a
  `theorem`'s *stated type*, not on an argument position. Re-checked through `wasm-check.cjs` at
  review (`prelude.sh 15 --incl` piped through it: clean).
- **`funext` sees through `emp`**; `subst`/`rw`/`congrFun` see through `pointsTo`. None needs
  `unfold` or `show`. `x30`'s second branch runs `funext` on a goal displaying as `emp σ h`.
- **`Heap.empty` must be asked for by name.** `rw [hp]` leaves `⊢ Heap.empty l = none` and its
  trailing `rfl` will not close it; `simp [Heap.empty]` does. Twice on this page.
- **`x30`'s left branch tolerates three `intro`s instead of four** (checked): the goal is then
  `∀ (l : Loc), h l = none` and both remaining lines work under the leading `∀`. The walk says so.
- **Weakest part, honestly:** two exercises, and `m3-1`'s rung-4 hint gives the first line of each
  proof. The unit's real content is the *decision*, and no exercise measures it.

## Provenance and checks
Every `state`/`trace` step is `check.sh 15 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (the first error `state` says so), inline
error quotes de-line-broken. All 14 Lean-bearing blocks were re-extracted from the finished file by
script and re-run: 5 `verified` report only `has already been declared`, 8 `illustration`s are
silent, the 1 `sketch` gives exactly the error beneath it. Every `pitfall`/`variants` claim compiled
separately — `rw [h1, h2]`, `exact this`, `exact some_ne_none v this`, the dropped store argument,
the double `subst`, `aFalse` as the first conclusion (refuted), the missing `funext`, both
alternative `x30` statements, `emp ⊣⊢ fun _ h => h 0 = none` (refuted), the dropped conjunct
(`(0 ↦ 3) ⊢ fact (fun _ => (3 : Val) = 4)`, refuted) and the two-address generalisation (proved).

All green after review: `node --check`; `lint.mjs 15-pointsto` **0/0** (45 blocks);
`ledger.mjs 15-pointsto` 0/0 and edition-wide 0/0, sweep and `frags` clean, **no waivers of any
kind**; `render-check.js` 0 problems; `verify.sh 15` (674 lines, 125 declarations);
`wasm-check.cjs` over the corpus through this unit, clean; banned-phrase grep clean.

## What review changed
**No Lean was edited.** All four traces and both `state` blocks were regenerated from scratch with
`trace_state` and diffed against the page: identical byte for byte. Every quoted error message was
reproduced by breaking a real proof. Everything below is prose.

- **A false clause, in the paragraph that justifies `fact`.** The page said the theorem "is not that
  the heap is empty, or that the heap is a singleton — the heap in question is a one-cell heap and
  neither of those is true of it." The second half is true of it. The paragraph also re-defined
  `fact`, which `14-assertions` introduces. Replaced by the two strengthenings actually available,
  both compiled: conjoin `emp` and the theorem is **false**; conjoin `l ↦ v₁` and it is true and is
  `and_left` with extra steps. That is objective 3's "and not something stronger", named.
- **`pointsTo_not_emp` had no main-line home.** One of the unit's two headline theorems, an explicit
  §D objective ("explain why a machine-checked *non*-entailment is worth as much as an entailment")
  and half the `blurb` ("ownership cannot be thrown away") arrived only inside the exercise's `why`.
  A paragraph now stands in front of `m3-1` stating the theorem in the first person, saying what a
  proved negation is evidence of, and naming the one later proof that cites it.
- **A closed `detail` was load-bearing.** The sentence *"an entailment is a function of three
  arguments, so to attack one you choose the store, choose the heap, hand it a proof of the premise,
  and work on what comes back"* — the shape `m3-1`'s second proof needs — sat inside the fold.
  PEDAGOGY §5: closing the fold left a hole. Moved into the main line; the fold's paragraph now says
  only what is local to it.
- **A wrong attribution, twice.** `orient.payoff` and `m3-1`'s `why` both said Unit 14's two
  non-entailments "between them account for why the frame rule has to exist". Only the first of them
  does; the second is about duplication. Both corrected to the first.
- **A sentence duplicated across `orient.payoff` and the body** — "Everything the rest of this course
  owns, it owns through `↦`" / "Everything the rest of this course claims to own, it claims through
  this line." Cut from the body.
- **A `tac` field that was not a tactic.** `x30`'s trace opened with `constructor  ·  intro σ h hp l`
  as one step, which the reader cannot type. Split into two real steps; the new first state is the
  output of `constructor` and is worth having anyway, because it shows the two-turnstile display in
  its bracketed form.
- **The closing paragraph restated the contractual hook that follows it.** Trimmed to the two things
  the hook does not say: that `aAnd` says something *else* rather than something weak, and that the
  single satisfiable case is the one where both conjuncts coincide.

**Not changed, and why.** The two-exercise set stands — §D prescribes it. The 43-block count stands;
see deviation 2. `subst hp` appears in the first illustration two sections before the section that
explains why a folded hypothesis counts as an equation; a second forward pointer there would have
made two in three paragraphs, and at that point the reader has just been told in as many words that
`emp` *is* an equation. The `sorry` separating the two theorems in `m3-1`'s `goal` stands:
`03-compute`, `02-terms` and `11-union` all use the same device for multi-theorem boxes.
