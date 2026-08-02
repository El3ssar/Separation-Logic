# Unit 15 · `star-algebra` · LAB — the laws of `∗`
`site/content/17-star-algebra.js` · 59 blocks (53 non-`ex`), 6 exercises, ~2180 words of main-line
prose (≈3.6 screens, budget ~3), 1 main-line `trace` + 8 in `deep`, 4 `state` (3 main line, two of
them inside the `∀`/`∃` fold; 1 in `deep`), 5 `detail` (one before the first exercise, four after),
1 `tbl`, 1 `defn`, 1 `cmp`. **Lean fragment untouched** — all six exercises were `C`/`N ✔`. One
`ledgerForward`; four stale `status: "migrate"` rows cleared.
*Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review.*

## One job
Prove everything routine about `∗` in one sitting, so that Unit 16 can give associativity the room
it needs.

## The hook I left (verbatim, final block; word for word from §D)
> Unit, commutative, monotone, distributive. One law is missing, and it is the one that lets you
> stop thinking about a *tree* of stars and start thinking about a *list* of owned resources. It is
> also the only one whose proof has to manufacture hypotheses — but Unit 11 already did that work.

Opens on `16-star`'s hook in its first three words ("Yes to both").

## Introduced
**Tactics: none.** `rw`, `subst`, `intro` patterns, `rcases`, `refine`, `funext`, `by_cases`,
`obtain`, `constructor`, `absurd`, `congrFun` all used freely (ledgered ≤ 14).

**Syntax / library names owed by the ledger and paid here:** **`trivial`** — one clause, in the
caption of `m4-5`'s `deep` illustration, which is where the page first uses it (its only two *corpus*
uses are `17-star-algebra.lean:72,75`, three sections later) — and **`Bool`** with `false`/`true`
and `cases x with | false => … | true => …` (the `∀`/`∃` fold, `def Pcx : Bool → Assertion`).
`by …` inside a term is **not** introduced here: ERRATA §24 moved that row to `11-union`, so
`star_comm`'s equation slot is used without ceremony and the page says only that the block now holds
two rewrites. `Sort u` (row at `14-assertions`) is first *exercised* here, as §E.2 predicts, and the
`Sort u` error in `m4-6`'s `pitfall` is where the reader sees what it buys.

**Names now usable:** `star_emp_left`, `star_emp_right`, `star_emp_left_intro`,
`star_emp_right_intro`, `star_comm`, `star_mono`, `star_mono_left`, `star_mono_right`,
`star_or_left`, `star_exists_left`, `aForall`, `star_forall_left`, `Pcx`,
`star_forall_right_fails`, `star_emp_left_iff`, `star_emp_right_iff`, `star_comm_iff`,
`star_congr`, `star_not_weakening`. Illustration-only, in no fragment: `oneCellIsBoth`.

**Concepts:** monotonicity of a connective (`defn`, stated for an arbitrary connective `∘` — a
symbol the reader has not met, introduced in the same sentence and used nowhere else) ·
**monotonicity + `⊣⊢` = congruence**, and rewriting *inside* a star · the `.symm` discipline on an
equation slot, and the fact that the **left** unit law cannot teach it · the `∀`/`∃` asymmetry and
its cause, the order of the quantifier and the cut · `∧` as `∀` over `Bool`, so the missing
`star_and_left` and the missing `∀` direction are one fact.

**Rejected alternatives, all compiled:** `subst`+`subst` for `rw [hu, he]` (works; the one
pre-exercise `detail`) · rewrites in the wrong order · `union_empty_*` without `.symm` (left
accepted, right refused) · the cut chosen the wrong way round · `hd` for `disjoint_symm hd` ·
`union_comm hd` before `hu` · `hpq σ h hp` · `⟨star_comm P Q, star_comm P Q⟩` · commutativity
refuted for `starNoDisj` at address 0 · both unit-intro laws under `starNoDisj` · `emp` strengthened
to `0 ↦ 0` in the intro law, refuted · the `∧` distribution pair, both directions.

## Exercises
- `m4-1` **star_emp_left / star_emp_right** [C 2] — first consumption of a star; the mirror is the work.
- `m4-2` **star_emp_left_intro / star_emp_right_intro** [C 2] — choose a forced cut; the `.symm` discipline.
- `m4-3` **star_comm** [C 2] — where `union_comm hd` is spent, twice.
- `m4-5` **star_mono (+ two specialisations)** [D 2] — no heap lemma; derive, do not reprove.
- `m4-6` **star_or_left / star_exists_left** [C 2] — same cut handed back; opens Unit 33's induction.
- `x36` **star_emp_left_iff / star_emp_right_iff / star_comm_iff / star_congr** [D 1] — packaging.

## Not explained (earlier summaries say it is known)
All of Modules 0–2 and Units 12–14: `⟨…⟩` flattening, the six-name `intro` pattern, `∗`'s
definition, `⊢`/`⊣⊢`, `emp` as an equation, `✝`, `Heap.union`'s left bias, `by …` in a term,
`AssertionEquiv` as the name behind `⊣⊢`.

## Deviations from COURSE-PLAN.md
1. **53 non-`ex` blocks against §D's ~24**; prose ~3.6 screens against ~3. ERRATA §18. Below every
   Module-3 unit so far (`14-assertions` 67, `16-star` 61).
2. **§D asks 3 traces; there are 9** (1 main line, 8 in `deep`), per PEDAGOGY §7.
3. **The lab rule "at most one sentence of prose between exercises" is broken three times** —
   before `m4-3`, `m4-5` and `m4-6`, each time by a `sec` plus the law's statement and its one idea.
   Six different laws cannot share one sentence of setup; `13-splits` broke the same rule once.
4. **§D's worked example includes `star_emp_left_intro`, which is half of `m4-2`.** Handled as
   `13-splits` handled `m2-8`: the left form is on the page, the mirror is the exercise. The
   `.symm` `cmp` is in `m4-2`'s `deep`, not the main line, for the same reason — displaying the
   mirror's failing line on the main line gives away the whole answer.
5. `ledgerForward: ['star_swap_middle']` — one named forward reference, in `m4-5`'s `why`, whose
   sentence says in as many words that you cannot read it yet. ERRATA §10's legitimate kind.
6. **The main line displays `star_comm`, `star_mono` (with both specialisations) and both
   distribution laws in full, immediately before the exercises that set them.** §D's worked example
   is only `star_emp_left` + `star_emp_left_intro`. Left standing at review: objectives 2, 3 and 4
   require the page to point at the single `rw` that spends commutativity, at the fact that
   monotonicity names no heap lemma, and at the cut being handed back unchanged — none of which can
   be done with the proof off the page — and `05-update`, `08-heap-laws` and `13-splits` all show an
   exercise's proof on the main line for the same reason. It is nevertheless the honest weakness of
   the unit. See "Weakest part".

## Warnings to successors
- **Downstream counts, grepped over fragments `18-*`…`41-*` with word boundaries, not estimated.**
  `star_emp_left` **3** (`32-symbolic` ×2, `30-frame` ×1) · `star_comm` **5** (`19-pure`,
  `32-symbolic` ×3, `37-wand`) · `star_mono_left` **3** · `star_mono_right` **6** ·
  `star_exists_left` **2** (both `36-lseg`) · **ZERO**: `star_emp_right`, both `_intro` forms,
  `star_mono`, `star_or_left`, all three `_iff`s, `star_congr`, `star_not_weakening`. The page
  states each of these, including the zeros — `x36`'s `why` says outright that none of its four
  theorems is ever cited again. Do not upgrade any of them into a promise.
- **The six-name `intro` pattern opens nine theorems after this unit** — `star_assoc_left`,
  `star_assoc_right`, `two_cells_distinct`, `star_pure_left`, `star_exists_right`, `and_fact_star`,
  `and_fact_star_intro`, `listRep_cons_ne_zero`, `wand_elim` — the last in Unit 34. `m4-1`'s `why`
  says exactly nine; keep it true if you add or remove one.
- **`star_emp_left_intro` is cited exactly once in the corpus, in this unit's own
  `star_not_weakening`** — which is also the corpus's only use of `pointsTo_not_emp`, as
  `15-pointsto`'s summary promised. Both promises are now kept; keep them true.
- **`Heap.union Heap.empty h` reduces and `Heap.union h Heap.empty` does not.** So on the *left*
  unit law the fourth slot accepts `(union_empty_left h).symm`, `union_empty_left h` **and** a bare
  `rfl` — all three compiled. §D's `.symm` lesson is therefore unteachable on the left law, and the
  page says so and teaches it on the mirror. A draft that demonstrates `.symm` on `emp ∗ P` is wrong.
- **Slot numbering.** The star's slots are `⟨h₁, h₂, hd, hu, hp, hq⟩`: disjointness is the **third**,
  the union equation the **fourth**. Two blocks called disjointness the fourth in the first draft;
  both fixed at review. The page is now consistent, and `m4-2`'s and `m4-3`'s pitfalls turn on it.
- **`_` in the third slot of the `intro` pattern prints as `left✝`**, not `hd✝`. Real output;
  in the main-line trace.
- **`aForall`, `star_forall_left`, `star_forall_right_fails`, `Pcx` were still marked
  `status: "migrate"` in `ledger.json` although all four are in the fragment.** Cleared, with a
  note on each row. `--audit` never flagged them, so the staleness was invisible.
- **Two goal states in `deep` run to 11 lines** (`star_congr`'s two `constructor` goals;
  `star_exists_left`'s context). They are behind the "Why it works" button, not on the main line, so
  PEDAGOGY §6.1 is satisfied — but if a reviewer disagrees they are the two to fold.
- **Attribution, checked at review:** the two overlapping heaps whose unions disagree are
  **`12-pcm`'s** (unit 10), as two `rfl` lines; `11-union` (unit 09) owns the left-bias *decision*
  that causes the disagreement; `13-splits` (unit 11) turns the demonstration into `union_not_comm`.
  The first draft credited the counterexample to unit 09.
- **Author of `18-star-assoc`:** `m4-3`'s `variants` promises your unit says associativity
  *survives* deleting the disjointness conjunct (`union_assoc` carries no hypothesis) while
  commutativity does not; the hook promises one theorem in two directions.
- **Author of `19-pure`:** the page promises (i) that `star_swap_middle` is two `entails_trans`
  nested, over four theorem names, two from this page and two from associativity — that is now the
  *only* claim made about your term proofs, because `star_rotate_left` and `star_rotate_right` are
  bare renamings of `star_assoc_*` and use no `entails_trans` at all; (ii) you set the converses of
  `star_or_left` and `star_exists_left` as `x38`, and this page tells the reader the `∃` converse
  holds without showing it, so `x38` is not spoiled; (iii) your unit answers "how do you attach an
  ordinary fact to a `∗`". The retrospective ends on that question.
- **Weakest part, honestly:** `m4-1`, `m4-2` and `x36` each transcribe half their answer from the
  main line, and `m4-3`, `m4-5` and `m4-6` have their whole answer on it (deviation 6); `m4-5`'s
  rung-4 hint gives both specialisations. The unit measures recognition well and construction
  barely — which is what §D's own table (six exercises, difficulty 2, 2, 2, 2, 2, 1) prescribes for
  a lab whose content is a list of easy laws, but a successor writing a lab with harder material
  should not copy this shape.

## Provenance and checks
Every `state` and `trace` field is `check.sh 17 <snippet>` output (`--incl` where the fragment's own
declarations were needed), byte for byte, `trace_state` where a mid-proof state was wanted,
`snippet:L:C:` dropped, in-sentence errors de-line-broken. All 16 Lean-bearing blocks were
re-extracted by script and re-run: the 8 `verified` blocks occur byte for byte in the fragments,
the 7 `illustration`s are silent under `check.sh 17 … --incl`, the 1 `sketch` gives exactly the
error beneath it. **Every `pitfall` and `variants` claim on the page was compiled as its own
snippet.**

All green: `node --check`; `lint.mjs 17-star-algebra` **0/0** (59 blocks); `ledger.mjs
17-star-algebra` 0/0, sweep and `frags` clean, one `ledgerForward`; `render-check.js` 0 problems;
`verify.sh 17` (830 lines, 152 declarations); `gen-contexts.mjs --prove` **67/67**, all six
exercises included; banned-phrase grep clean.

## What review changed
**No Lean was edited, and no exercise `id`, `name`, `goal`, `sol` or hint rung was touched.** All
eleven `state`/`trace` blocks were regenerated from scratch with `trace_state` through
`check.sh 17 … --incl` and diffed against the page: every *step* state was identical byte for byte,
and five `start` fields were not (below). All seven `illustration`s were re-extracted and recompiled
(silent); the `sketch`'s error and all nine quoted error messages were reproduced by breaking a real
proof — including the `?m.22` in `m4-2`'s `pitfall`. Every downstream citation count on the page was
re-grepped over `18-*`…`41-*`; all of them held. Everything below is prose.

- **Five `trace` `start` fields were not what Lean prints** — `m4-5`'s, both of `m4-6`'s and both of
  `x36`'s gave a bare `⊢` line with the binders and hypotheses stripped, while the unit's other four
  traces gave the real thing. `star_or_left`'s also mis-parenthesised (`(aOr P Q) ∗ R` for Lean's
  `aOr P Q ∗ R`) and `star_exists_left`'s over-parenthesised the lambda. All five replaced with
  `trace_state` output.
- **Disjointness was called "the fourth slot" in two places** and the third everywhere else,
  including in two `pitfall`s that turn on the count. Both corrected to third.
- **"the word *so* replaced by two rewrites"** — there are three, and the `trace` three blocks later
  is titled "with the three rewrites separated".
- **"That `intro` takes seven things"**, in the `∀`/`∃` fold, followed by a list of four. Corrected.
- **`trivial` was used two sections before it was introduced.** `m4-5`'s `deep` illustration is
  `star_mono_left Q (fun _ _ _ => trivial)`; the clause explaining `trivial` sat in the `∀`/`∃`
  fold, after it. The clause moved to that illustration's caption; the fold now introduces only
  `Bool` and `cases … with | false | true`.
- **The `.symm` fact was stated three times in near-identical words** — main line, `m4-2`'s `cmp`,
  and `m4-2`'s `variants` all re-derived "union matches on its left argument, so
  `Heap.union Heap.empty h` reduces and `Heap.union h Heap.empty` does not". It is now stated once,
  on the main line; the `cmp` columns say only what each column shows; and `m4-2`'s `variants` was
  rewritten to do what PEDAGOGY §8 asks of the field — drop a *hypothesis* — with two new compiled
  claims: both intro laws survive under `starNoDisj` with five slots, and strengthening `emp` to
  `0 ↦ 0` makes the law false at the first slot, witness `P := emp` at `Heap.empty`.
- **The counterexample to unconditional `union_comm` was credited to unit 09.** It is unit 10's
  (`12-pcm`, two `rfl` lines); unit 09 owns the left bias that causes it. Rewritten to say both.
- **Three overcounted forward claims.** (i) `m4-1`'s `why`: the six-name pattern "is the opening
  line of every remaining proof in this module and of four theorems after it" — it is neither
  (`star_or_right`, `star_pure_right` and unit 17's three term proofs do not open that way), and the
  real count downstream is nine, as far out as Unit 34. (ii) The closing paragraph: "Three of Unit
  17's theorems are built exactly this way, out of nothing but names and `entails_trans`" — only
  `star_swap_middle` uses `entails_trans`; `star_rotate_left`/`_right` are one-name renamings of
  `star_assoc_*`. (iii) `youWill` item 4 asked the reader to "point at the single character where
  the disjointness hypothesis of `union_comm` is spent — twice", which is self-contradictory and
  wrong about the character count; it now asks for both slots.
- **"the slot type-checks against terms"** — Lean type-checks up to definitional equality, which is
  the very reason the *next* paragraph gives for `rfl` working on the left law. Replaced by the
  correct statement: `a = b` and `b = a` are different types, and a slot wants a term of its type.
- **Two meta-sentences announcing their own paragraph** — "What the equivalences buy is the last
  exercise's real content" and "the corpus does so here because the comparison is worth having".
  Cut and rewritten; the second now names what the fold is for.
- **`m4-2`'s `deep` array had its `cmp` and `state` dedented out of alignment** with the `trace`
  above them, which reads as though they were siblings of the exercise rather than entries of
  `deep`. Indentation only; the tree was always correct.

**Not changed, and why.** The 59-block size stands; see deviations 1 and 6, and the block budget is
advisory per ERRATA §18. All six exercises keep their §D-prescribed ids, names, kinds and
difficulties, and their `goal`/`sol` text is the fragment verbatim. The `∀`/`∃` argument stays in a
`detail`: §D's size line names it as the unit's one `detail`, and the main line carries the pointer
that makes closing it lossless. `m4-6`'s `star_or_left` trace shows only the `inl` goal after
`rcases` where Lean prints both, with the step's own sentence saying "the first of two goals" and
the next step showing `inr` in full — an elision, judged clearer than an eighteen-line block. The
`sketch` tag on `m4-2`'s failing `cmp` column follows `16-star`'s precedent for
compiled-and-refused code; the block vocabulary has no better tag.
