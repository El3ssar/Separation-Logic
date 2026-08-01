# Unit 07 · `footprint` · How much do you own?
`site/content/09-footprint.js` · 35 blocks (32 non-`ex`), 3 exercises, ~2230 words of main-line text
(≈3.7 screens), 3 traces, 1 `detail` (after the second exercise). 46 KB.
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Pose, with a compiled counterexample, the question the course turns on — which heaps satisfy
"`l` holds `v`"? — and show the two answers disagree about whether deallocation can be specified.

## The hook I left (verbatim, final block; word for word from §D)
> The exact reading survives the test and the loose one does not, so `l ↦ v` is going to mean *the
> heap is this one cell*. But then an assertion talks about all of the memory it holds, so
> combining two of them means cutting memory in two — and nothing you have can cut a heap.

Opens on `08-heap-laws`'s hook in its first sentence, quoting `erase_singleton` as the thing that
is *almost* a specification of deallocation.

## Introduced
**Tactics: none.** `show` gets its first load-bearing use (row at `03-compute`; §E.1 predicted unit
22), restating `ptsAtLeast l v σ h` as the lookup it definitionally is.

**Notation: none.**

**Names now usable:** `ptsAtLeast`, `ptsExactly`, `twoCells`.

**Syntax glossed here (added at review):** the type-labelled numeral `(4 : Loc)`, in `x16`'s walk
and rung-4 hint — named as the labelling `pp.numericTypes` prints (§`errors`), and stated to be
documentation, since `Loc` is `Nat` and Lean infers it. The word *ascription* is not used anywhere
on the page; `02-terms`'s review records that the reader has not met it.

**Concepts:** the two readings of *l holds v* as two predicates · the bare type
`Store → Heap → Prop`, store bound and discarded, nameless until Unit 12 · **footprint** (`defn`,
posed not decided) · **the four-move refutation idiom** as a `steps` block — assume, *choose the
address*, `congrFun` there, collide `some` against `none` — move two flagged as the one with no
Lean in it · a definition is a choice judged by which theorems survive it · vacuity: `x16` is what
stops `x18` being a refutation of nothing.

**Rejected alternatives, costed:** `rfl` and `simp` both close `x16` — the first only because every
address is a numeral, the second only by unfolding what Unit 06 closed · weaken the postcondition
to "`l` is unallocated": compiled, and the proof never references the precondition (the real unused-
binder warning is on the page) · conjoin "nothing else is allocated": compiled, implies
`ptsExactly`, so it is exactness plus a `∀` every later proof carries.

## Exercises
- `x16` **a two-cell heap satisfies the loose reading** [D 1] — `write_other`, `singleton_same`.
- `x17` **it does not satisfy the exact reading** [C 3] — `congrFun` at a witness; the `deep` shows
  the same proof at address 4, ending `h4 : some 3 = some 3`.
- `x18` **after free, the heap is not empty** [C 3] — the free rule refuted under the loose reading.

## Not explained (previous summaries say it is known)
`funext`, `by_cases`, `<;>`, `congrFun`, `rw`/`rw … at`, `unfold`, `have`, `show`, `some_ne_none`,
`¬P` as `P → False`; the goal display; the six lookup laws, the eleven equations, the interface
discipline; `Option` and constructor distinctness.

## I changed the Lean fragment — all three proofs rewritten
The shipped Lean used constructs booked after this unit: `(by simp)` in term position (§E.2 books
that at `17-star-algebra`, eight units later, twice), and `show t from rfl`, which **has no ledger
row at all**. Replaced by `have hne : … := by simp`, `unfold twoCells`, and
`exact some_ne_none 7 h9` in place of `exact absurd h9 (by simp)`. Same statements, same markers,
310 declarations corpus-wide, all checks re-run.

## Warnings to successors
- **`gen-contexts.mjs`'s marker regex rejects a hyphen in the description** —
  `([^-]*?)-\/`, so `/- ex x16 a two-cell heap … -/` matches nothing and the tool reports the
  exercise as having *no marker*. Renamed to `a two cell heap …`. Never put a hyphen or dash in a
  marker line. Worth an ERRATA entry.
- **`ledger.mjs` does not fire on `↦` in prose.** It appears three times here (`orient.payoff`,
  `x18`'s `why`, the contractual hook), all openly marked forward references; a
  `ledgerForward: ['↦']` was reported as a **stale waiver**, so the notation row is not matched in
  chapter prose. Removed; the page is 0/0 without it. Do not trust the ledger to police notation.
- **`rw [hp]` and `congrFun h 9` both see through a definition** — `hp : ptsExactly l v σ h` is not
  syntactically an `Eq` and both work anyway.
- **`unfold twoCells` is not a breach of the interface rule**, and `x16`'s `solNote` says so:
  `twoCells` names a heap, not one of the four operations. The pattern for any later concrete heap.
- **`(4 : Loc)` in the fragment's three `have` lines is not load-bearing.** All three proofs compile
  with the bare `have hne : 4 ≠ 9 := by simp` (checked). The page said it was load-bearing; it now
  says it is documentation. Left in the Lean so the `sol` fields stay verbatim.
- **`rw [write_other]` with no arguments works**: the goal fixes all four explicit arguments, and
  the disequality comes back as a second goal `case hne ⊢ 4 ≠ 9`. Only `hne` has to be supplied.
- **`rfl` on `ptsAtLeast l v σ h` with variables reports about `σ`, not about the lookup** — "The
  left-hand side `σ` is not definitionally equal to the right-hand side `(Heap.singleton l v).write
  l' w`". It compares the last two arguments of `ptsAtLeast l v` when there is nothing left to
  compute. The page previously claimed `?m.3 = ?m.3`, which Lean 4.32.2 does not print.
- **Weakest part, honestly:** `x16`'s rung-4 hint is most of the answer, and `x17` and `x18` are the
  same seven-line shape twice. No exercise makes the reader *choose* a witness under pressure —
  both statements have exactly one candidate address.

## Deviations from COURSE-PLAN.md
1. 32 non-`ex` blocks against §D's ~24 — inside §C's band, below every preceding unit; prose at
   budget. ERRATA §18.
2. The fragment was rewritten (above). §F marks `x16`–`x18` `N ✔`; the Lean existed and was
   ledger-illegal.
3. §D objective 3 asks for `{l ↦ v} free l {emp}`. The `txt` block writes the triple in words —
   `{ l holds v } free l { memory is empty }` — because `↦`, `emp` and the triple are booked at
   Units 13, 13 and 22.

## Provenance
Every `state` and `trace` step is `check.sh 09 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so). All eleven
`code`/`anat` blocks were re-extracted from the finished file by script and re-run: `verified` ones
report only `has already been declared`, the `illustration`s are silent bar the one quoted warning,
the `sketch`es give exactly the errors printed beneath them. Every `pitfall` and `variants` claim
was compiled separately. Two captioned elisions: the linters' `Note:` tails, and the
unused-simp-argument warnings, named rather than quoted because their strike-through rendering is
unreadable.

**Re-checked at review, independently.** All twelve `code`/`anat` blocks re-extracted by script and
re-run through `check.sh 09 --incl`: six `illustration`s silent bar the quoted `hp` warning, three
`sketch`es giving exactly the errors printed beneath them, three `verified` blocks byte-for-byte in
the fragments. All three `trace` blocks regenerated with `trace_state` and diffed against the page —
identical, including `fun x => 0` and `twoCells.erase 4`. Every `pitfall` and `variants` claim
recompiled, plus the two new ones this review added (`rw [write_other]`'s residual goal; the
falsity of the variable statement with `hne` dropped, witnessed by `l = l' = 0`, `v = 1`, `w = 2`).

## Checks — all green
`node --check` · `lint.mjs` 35 blocks, **0/0** · `ledger.mjs 09-footprint` 0/0 and edition-wide
0/0, `--sweep` clean, **no waivers of any kind** · `render-check.js` 0 problems · `verify.sh 09`
(351 lines, 69 declarations) · `gen-contexts.mjs --prove` **34/34, 0 failed** ·
banned-phrase grep clean, including the widened sweep. Re-run at review; the Lean was not touched.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **A wrong unit number in `orient.needs`:** "Unit 04: `congrFun`". `congrFun` is Unit 03
  (`04-funext`); Unit 04 is `05-update`. The field now reads Unit 03 for `congrFun`/`funext`,
  Unit 02 for `show`/`unfold`/`some_ne_none`, Unit 00 for `¬P` as `P → False`.
- **An error message Lean does not print.** The `deep` `illustration` in `x16` was captioned
  "`rfl` on this statement fails with `?m.3 = ?m.3`". It fails with a message about `σ` — see the
  warning above. Caption replaced by the real text.
- **A false claim about `(4 : Loc)`, twice** (`x16` walk and rung-4 hint): "load-bearing: without it
  `simp` is being asked about two unattached numerals". All three proofs compile without it.
- **A false claim about `write_other`'s arguments** in `x16`'s walk: "nothing in the goal forces
  them". The goal forces all four; `_` works for each. Rewritten around what the goal does *not*
  force — `hne` — and the second goal `rw [write_other]` leaves.
- **A `variants` claim that contradicted the corrected walk:** "Drop `hne` and no proof is left:
  `write_other` does not typecheck without it." It does. The clause now distinguishes the numeral
  statement (the disequality moves to a second goal) from the variable one (which is *false*
  without `hne`, and the witness is given).
- **The closing `note` opened with the hook's own first eleven words**, "The exact reading survives
  the test and the loose one does not" — a sentence restating its successor, and the hook is
  contractual. The note now carries only what nothing else on the page says: the first-person
  register, and the Unit 23 pointer. It also no longer restates the `cmp`'s right column.
- **"the first heap you build yourself"** in `x16`'s `why` — `twoCells` is given on the page, and
  the reader's own first heap was `twoAllocated` in Unit 00. Now "the first lookup in a heap you can
  point at that goes through the interface Unit 06 closed".
- **An over-strong `defn`:** "Under the loose reading it has no footprint at all" — the loose
  reading does fix what is stored at `l`. Now: no *part of memory* is pinned down, because the
  extent is not fixed.
- **Three restatements cut**: "That settles that the question is a real one" (after `x17`); "The
  counterexample is not vacuous, and the distinction matters, because…" (after `x18`); and the
  `x18` `deep` paragraph that re-derived the main line's "no tactic will choose the somewhere for
  you", now one sentence.
- **A forward pointer sharpened:** Unit 13 tells a one-cell heap from `emp` by rewriting with the
  assumed equation, not by `congrFun` (`15-pointsto.lean`: `have : … := by rw [h]`). The page now
  says so, so the reader is not surprised there. Units 14 and 31 were checked against
  `16-star.lean` and `34-wp.lean` and are exactly as described.
- **`ascription` used as an unglossed technical noun**, twice. `02-terms`'s review already recorded
  that the reader has not met the word. Both uses rewritten in plain English.
- **Rung-3/rung-4 drift in `x16`:** rung 3 said "Three tactics and two laws, and nothing else" and
  then named a fourth (`simp`), and rung 4's first line is a fifth (`have`). Rung 3 now names the
  two laws and says to park the disequality with `have`.
- Minor: "Both lines lean on the same fact, in opposite directions" → one on the goal, one on a
  hypothesis, which is what actually differs; `x18`'s walk no longer says the reading at 9 "wants" a
  disequality (only `erase_other` does).
