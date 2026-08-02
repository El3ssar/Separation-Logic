# Unit 14 · `star` · Separating conjunction, and what it cannot do
`site/content/16-star.js` · 65 blocks (60 non-`ex`), 5 exercises, ~2650 words of main-line prose
(≈4.4 screens, budget 5), 1 main-line `trace` + 5 in `deep`, 1 `state`, 1 `detail` (last teaching
block; none before the first exercise), 1 `anat`, 1 `svg`, 1 `cmp`, 1 `dl`, 1 `note kind:'warn'`.
**Lean fragment untouched** — all five exercises were `N ✔`. No `ledger.json` row added, no waivers.
*Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review.*

## One job
Define `∗`, install the two mechanical moves, and then — before any law — prove the two failures,
because what makes this a different logic is what it cannot do.

## The hook I left (verbatim, final block; word for word from §D)
> A connective with no projection and no duplication. Whether it has anything at all is the next
> question: does it even have a unit? Is it commutative?

Opens on `15-pointsto`'s hook in its first sentence: the reader writes down what "I own this cell
and separately that one" has to say, and the three requirements become the definition.

## Introduced
**Tactics: none.** `show` is used on a folded `def` to expose six slots; `subst` on an ownership
hypothesis, `congrFun` through a folded `↦`, `obtain`, `refine`, `by_cases`, `funext` all used
freely (all ledgered ≤ 13).

**Syntax:** `infixr:55`, compared against `infix:40` (`⊢`) and `infix:60` (`↦`), with all three
parses proved by `example … := rfl` rather than asserted · **deep destructuring in `intro`** —
`intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩`, three binders and a six-name pattern.

**Notation:** `∗`.

**Names now usable:** `star`, `star_intro`, `star_same_loc_absurd`, `star_pointsTo_same_false`,
`no_star_weakening`, `no_star_duplication`, `starNoDisj`, `starNoDisj_dup`.
Illustration-only, in no fragment: `starNoEq`.

**Concepts:** separating conjunction, and *the heap splits* · why `⊎` on paper is three Lean
conjuncts · the existential cut as the source of the build/consume asymmetry · **weakening**,
**contraction**, **substructural logic**, linearity in resources (`dl`) · refutations cost a witness
and the page says so before the first one · the necessity of the **frame rule**, named before it is
met (concept rows are `check:false`, so no waiver was needed).

**Rejected alternatives, compiled:** the **universal** reading of the cut (`∀ h₁ h₂, disjoint →
h = union → P σ h₁ ∧ Q σ h₂`) — in prose, in the `anat`'s `∃ h₁ h₂` callout; compiled at review as
`starAll`, refuted at the two-cell heap by the cut `(h, Heap.empty)` · `starNoEq` — delete the union equation and
`emp ⊢ starNoEq (0 ↦ 4) (1 ↦ 7)` · `starNoDisj` — delete disjointness and a one-cell heap satisfies
"0 holds 4 and separately 0 holds 7" · the fully nested six-tuple · `rw [hp, hq] at hd` for `subst`
· `absurd … (by simp)` as `x32`'s last line (`star_pointsTo_same_false`, corpus).

## Exercises
- `x31` **star_intro** [D 1] — the construction move; the flat six-slot `⟨…⟩`.
- `x32` **star_same_loc_absurd** [C 2] — the consumption move; first spend of `singleton_disjoint_iff`.
- `x33` **no_star_weakening** [C 4, `hard`] — no weakening; choosing the witness and the address.
- `x34` **no_star_duplication** [C 4, `hard`] — no contraction; the disjointness conjunct is the culprit.
- `x35` **starNoDisj_dup** [C 3] — delete that conjunct and duplication returns in one `exact`.

## Not explained (earlier summaries say it is known)
All of Modules 0–2 and Units 12–13: `⟨…⟩` and its flattening, `.mp`, `subst`, `congrFun`, `show`,
`obtain`, `refine`, `absurd`, `✝`, the goal display, `Heap.union`'s left bias, the lookup laws.

## Deviations from COURSE-PLAN.md
1. **60 non-`ex` blocks against §D's ~30**; prose *under* budget (4.4 screens against 5). ERRATA §18.
2. §D asks 1 trace; there are 6 (1 main line, 5 in `deep`), per PEDAGOGY §7.
3. **The exactness-versus-disjointness argument is main line; only its compiled proof is in the
   `detail`.** §D calls it "the concluding argument of the unit", and PEDAGOGY §5 forbids folding
   one. Closing the fold leaves no hole.
4. `star_not_weakening` is **not** here (ERRATA §6 moved it to `17-star-algebra`) and is not named.

## Warnings to successors
- **Only `no_star_weakening` turns on Unit 07's exactness decision.** Under the loose reading
  (`ptsAtLeast`), `x32`'s non-aliasing theorem and `x34`'s no-contraction refutation **both still
  compile** — each needs disjointness and nothing else — and only `x33` flips from refutation to
  theorem. Both were compiled at review. The pre-review closing paragraph of the `detail` said the
  unit "would have proved `x32` and neither refutation", which is false. **Author of `26-small-footprint`
  and `30-frame`:** credit exactness with the *absence of weakening* only, as `15-pointsto`'s review
  already had to correct once.
- **`aAnd (l ↦ v₁) (l ↦ v₂) ⊢ aFalse` is FALSE for arbitrary values** — take `v₁ = v₂`. Unit 13
  proves it only with the addresses or the values distinct. The `∗` version needs neither
  hypothesis, and `x32`'s `variants` now says so with a compiled refutation of the `aAnd` form. A
  first draft of this page claimed the reverse.
- **`x34`'s counterexample must own something.** `emp ⊢ emp ∗ emp` and `aTrue ⊢ aTrue ∗ aTrue` both
  **compile**. Contraction is not uniformly absent; the theorem is about the quantifier. In the
  `pitfall`.
- **A five-name `intro` pattern is accepted** where six are wanted: flattening stops a level early,
  `hp` silently becomes the union equation and `hq` the remaining conjunction, and the error lands
  four lines later on `hd`. In `x32`'s `pitfall`, with the real message.
- **`x32`'s proof is `two_cells_distinct` (`19-pure.lean:6`) with the trailing ` rfl` removed.**
  `x32`'s `why` claims exactly that; **author of `19-pure`**, keep it true.
- **None of the six theorems has any downstream Lean consumer** (grepped, whole corpus). `x33`'s
  `why` says so and claims only the *argument* at Units 17, 23, 27 and 34.
- **`congrFun h 1` reaches through a folded `↦`** and `subst hp` through a folded `pointsTo`, as
  `09-footprint` and `15-pointsto` found; nothing needs `unfold` or `show` on this page except for
  display.
- **The `svg` uses `class="dg-arr thin"`, whose CSS names `marker-end:url(#ah)`; no file in this
  repo defines `#ah`.** It renders as a plain dashed line, which is what is wanted. Do not "fix" it
  by inventing a marker.
- **Weakest part, honestly:** `x31` is a one-line term whose rung-4 hint is the answer, and `x33`
  and `x34` both have rung-4 hints that give the witness — which is the only hard part of either.
  The unit measures the *recognition* well and the *construction* barely.

## Provenance and checks
Every `state`/`trace` step is `check.sh 16 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped, error quotes de-line-broken. All six
`illustration` blocks were re-extracted by script and compiled as one file (silent); the `sketch`
gives exactly `unexpected end of input; expected ':=', 'where' or '|'`. **Every `pitfall` and
`variants` claim on the page was compiled as its own snippet** — sixteen of them, including all four
quoted error messages.

All green: `node --check`; `lint.mjs 16-star` **0/0** (65 blocks); `ledger.mjs 16-star` 0/0, sweep
and `frags` clean, **no waivers**; `render-check.js` 0 problems; `verify.sh 16` (726 lines, 133
declarations) and bare `verify.sh` (2312 lines, 316); `gen-contexts.mjs --prove` **59/59**, all five
exercises included; **`wasm-check.cjs` over the whole corpus plus this page's six illustrations,
clean**; banned-phrase grep and the widened sweep clean; ERRATA §7's `<code>`-collision grep returns
only real citations (`emp`, `star`, `subst`).

## What review changed
**No Lean was edited.** All eleven `state`/`trace` states were regenerated from scratch with
`trace_state` through `check.sh 16 … --incl` and diffed against the page: **identical byte for
byte**. All six `illustration` blocks were re-extracted by script and recompiled as one file
(silent). Every quoted error message was reproduced by breaking a real proof — the five-entry
tuple, the reversed `hu`, the five-name `intro` pattern (both the `aFalse σ (h₁.union h₂)` goal and
the `subst hq` failure), the `Heap.write` spelling of the witness, address 0's `some 4 = some 4`,
`union_self` without `.symm`, the same tuple against `P ∗ P`, and `simp made no progress` on
`Heap.empty`. Every `pitfall`/`variants` claim was recompiled: `emp ⊢ emp ∗ emp`,
`aTrue ⊢ aTrue ∗ aTrue`, the single-assertion `x34`, both alternative `x34` endings, the `aAnd`
form of `x32`, `x33`'s other conjunct and its `aTrue` conclusion, `x32`'s `rw [hp, hq] at hd`
route, and all four of `x35`'s (`starNothing`, `starNoEq`'s no-duplication, `starNoDisj P P ⊢ P`
refuted). `wasm-check.cjs` over the whole corpus: clean. Everything below is prose.

- **A false claim in the closing `detail`**, and the sharpest defect on the page: "if Unit 07 had
  chosen the loose reading, this unit would have proved `x32` and neither refutation". `x34` still
  goes through under `ptsAtLeast` — compiled — because no-contraction needs disjointness and
  nothing else. The paragraph now says that only `x33` turns on the choice. Its first sentence, a
  verbatim restatement of the main-line paragraph three blocks earlier, is gone.
- **`orient.payoff` credited both refutations with the frame rule's existence.** `15-pointsto`'s
  review corrected exactly this attribution one unit earlier. Split: the first is why the rule must
  exist, the second is why `∗` is a different conjunction at all.
- **The existential cut had no rejected alternative** — PEDAGOGY §7. The universal reading is now
  refuted in the `anat` callout, in one sentence, with the cut that kills it (`(h, Heap.empty)`);
  compiled as `starAll`.
- **"the three jobs come apart into three conjuncts, and every one of them can be pointed at,
  deleted, and priced"** — it is a binder and two conjuncts, and only the two conjuncts are ever
  deleted. Corrected.
- **The opening paragraph's justification of the existential was muddled**: "a different heap will
  come apart differently, and the assertion has to hold for all of them" reads as universal
  quantification over heaps, which is not what is meant.
- **`x31`'s `solNote` miscounted:** "the only theorem about `∗` that succeeds. The five after it are
  refutations." `star_same_loc_absurd` succeeds too, and `starNoDisj_dup` is neither a refutation
  nor about `∗`.
- **The refutation shape was taught twice** — once in the section's own opening paragraph and again
  in the paragraph after it, attributed to `15-pointsto`, which had already taught it in *its* main
  line. One paragraph cut; what remains names what is new (four choices, not one) instead of
  re-teaching the recipe. That is the one block removed: 66 → 65.
- **`x34`'s `why` ended "Edition 1 of this course never said so anywhere."** The reader has never
  heard of Edition 1; this is the only such reference in any Edition-2 content file. Replaced by
  the forward claim §D asks a `why` for.
- **Three meta-sentences announcing the paragraph they open** — "That is the argument in words, and
  it is worth having before the Lean…", "getting it right is worth one paragraph because…", and
  "The equation is what makes the connective a claim about the heap in hand" (restating the
  paragraph before the code block). All rewritten or cut.
- **`x33`'s `why` closed on "and the argument is the course"** — a flourish. Replaced by the
  checkable form: what it supports is an argument rather than a proof term.
- **One overstatement:** `x35`'s `deep` said that with disjointness restored "every entry after it
  is off by one and reports its own mismatch". Lean reports two errors, not three.

**Not changed, and why.** The 65-block size stands; see deviation 1, and the prose is under budget.
All five exercises keep their §D-prescribed ids, names, kinds and difficulties. The rung-4 hints of
`x33` and `x34` still hand over the witness — that is the "weakest part" noted above, and PEDAGOGY
§8 makes rung 4 a near-giveaway by design, so it is the prescribed shape rather than a defect. The
main-line argument for no-contraction goes through `self_disjoint_iff_empty` while the solution
goes through `singleton_disjoint_iff`; the `setup` says so and the `deep` compiles both, so the
mismatch is deliberate. The one-paragraph "Refutations cost more than proofs" section keeps its
`sec` divider: it is a TOC landmark for the two hard exercises that follow.
