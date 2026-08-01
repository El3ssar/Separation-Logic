# Unit 06 · `heap-laws` · LAB — equations between heaps
`site/content/08-heap-laws.js` · 46 blocks (40 non-`ex`), 6 exercises, ~1420 words of main-line
prose, 11 traces, 4 `detail` — one before the first exercise. Brief → worked example (the largest
section) → six exercises → retrospective. 94 KB source, 138 KB rendered.
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Close the heap interface — the eleven equations between whole heaps — and leave the reader never
needing to unfold a heap operation again.

## The hook I left (verbatim, final block; word for word from §D)
> Every law so far is about one heap, and `write_comm` had its disequality handed to it. In a real
> program nobody hands it to you. To *derive* such a fact rather than assume it, memory has to be
> splittable — and before we can split a heap we had better decide what it means to hold one.

Opens by answering `07-heap`'s hook in its first sentence.

## Introduced
**Tactics: none**, and the brief says so. `simp only` gets its first load-bearing use
(`erase_write_comm`), as §E.1 books it.

**Names now usable:** `heap_ext`, `write_shadow`, `erase_write_same`, `write_erase_same`,
`erase_erase`, `write_empty`, `write_singleton`, `erase_singleton`, `erase_comm`, `write_comm`,
`erase_write_comm`, `write_of_eq`.

**Vocabulary introduced here (added at review):** **redex** and **beta-reduction**, one clause
each, in `x15`'s `expl`, where the `unfold`-versus-`simp only` failure makes them load-bearing.
Neither word occurs in any earlier Edition-2 unit — they were used unglossed three times before
review. Every use of them on the page now falls after that clause (`x15` `deep`, the `dod`).

**Concepts:** the schema *a second operation at `l` leaves no trace of the first*, instantiated
four ways · **operations on separate parts of memory commute — the germ of the frame rule**,
sharpened to: two operations commute when the parts they touch are separate *or* when they agree
where those parts meet — hence `erase_comm` needs no hypothesis (and its two-line proof is now on
the page), `write_comm` does, and `write_comm` with a single value does not · the layering
discipline (prove it here so Unit 23 is three lines) · the unfolding exception, stated openly in
the one pre-exercise `detail`, **with `Heap.empty` carved out of it** · the
**`congrFun`-at-a-point refutation idiom**, used twice (`m1-7`'s `deep`, `x15`) — §D Unit 07 names
it as a pattern, so Unit 07 should name it, not invent it.

**Rejected alternatives, costed:** three proofs of `write_singleton`, verdict that only the
interface one survives an edit to the definitions · `write_comm`'s one-call proof and what it
conceals · `unfold` versus `simp only` · two other statements of `x15`'s false claim.

## Exercises
- `m1-5` **write_shadow** [C 2] — the schema, first instance; last write wins.
- `m1-6` **erase_write_same** [C 2] — why `Heap.write` must be in the bracket though its value is
  discarded; the residue is `write_other`.
- `m1-7` **write_comm** [C 3] — three regions by hand; the `have` bolded as the only line spending
  `hne`; counterexample, equal-values case and `erase_comm` in `deep`.
- `m1-8` **write_singleton / erase_singleton** [C 2] — Unit 23's write and free rules; why
  `Heap.empty` must be in the bracket.
- `x14` **erase_erase, write_of_eq** [C 3] — a free win, then a heap hypothesis driving the `pos`
  branch; the only corpus proof here that never unfolds.
- `x15` **erase_write_comm, and the claim it is not** [G 3] — `unfold` versus `simp only`; the
  reader states and refutes the unconditional claim.

## Not explained (earlier summaries say it is known)
`funext`, `by_cases`, `<;>`, `if_pos`/`if_neg`, `congrFun`, `Ne.symm`, `rw`, `unfold`, `have`,
`simp only`, `↓reduceIte`; the three-move shape and the `simp`-versus-`rw` rule; namespaces,
dot-notation display, the six lookup laws and the interface rule; the multi-theorem `goal` with a
`sorry` between the two statements (`07-heap`'s `m1-3` convention, and its `setup` explains it).

## What downstream actually consumes — checked against the corpus, not assumed
Grepped every fragment after `08-heap-laws.lean` for all eleven names:

| law | later consumers |
|---|---|
| `write_singleton` | Units 23, 29, 31, 37 |
| `erase_singleton` | Units 23, 31 |
| the other nine, and `heap_ext` | **none, anywhere** |

The page now says this in the closing `note` instead of the false claim it carried before. Do not
re-promise downstream citations for `write_shadow`, `erase_write_same`, `write_erase_same`,
`erase_erase`, `write_empty`, `erase_comm`, `write_comm`, `erase_write_comm` or `write_of_eq`.

`heapLocal_write` (Unit 25) does **not** re-run `write_comm` with disjointness substituted for the
disequality: its heap equation (`write_union_no_disjointness`) needs **no** hypothesis at all, and
the disjointness half is `write_of_eq`'s shape — `have hl' : h l = _ := hl` then `rw [hl'] at hx`.
The page's forward pointers now say that.

## I changed the Lean fragment — read this (unchanged at review)
1. **`write_of_eq` no longer uses `subst`**, which `ledger.json` and §E.1 book at `10-disjoint`,
   two units after this one. `· subst hx; rw [write_same]; exact hl.symm` is now
   `· rw [hx, write_same]` / `exact hl.symm`. A corpus bug, not a preference.
2. **Two `example`s added** — `write_comm`'s counterexample, and `erase_write_comm`'s refutation
   placed immediately after it with no comment between, so `x15`'s two-part `sol` is a contiguous
   substring. §F marks `x15` `N ✔+⧗`.
3. **Never write `/- ex <id> … -/` twice for one id**: `gen-contexts.mjs` treats each as a cut and
   reports `duplicate ex markers`.

**Review touched no Lean.** `verify.sh 08` is 318 lines / 66 declarations; bare `verify.sh` is
2281 lines / 310 declarations, unchanged.

## Deviations from COURSE-PLAN.md
1. **§D's third route, "via `write_of_eq`", does not exist**: `write_of_eq` needs the value written
   to equal the value already held, and `write_singleton` writes a different one. Route three is
   instead *through the interface* — the four lookup laws cited by name, nothing unfolded — which
   is the reuse lesson §D wanted. Plan slip.
2. **§D says "two are commutation laws, one carries a disequality".** There are three and two carry
   one. The page states the true counts and makes it the second retrospective answer.
3. **40 non-`ex` blocks against §D's ~22** (07-heap ran 39 against ~28); prose at budget
   (~1420 words ≈ 2.4 screens), the excess is compiled exhibits.
4. §D objective 3's counterexample sits in `m1-7`'s `deep`, not the main line: PEDAGOGY §11 allows
   one sentence between lab exercises.
5. **§D's "the last place a heap operation may be unfolded" is not literally true of
   `Heap.empty`** — see the warning below. The page states the exception rather than the rule.

## Warnings to successors
- **The unfolding ban does not cover `Heap.empty`, and the corpus proves it.**
  `15-pointsto.lean:22` and `22-exec.lean:44` both write `simp [Heap.empty]`, in Units 13 and 20.
  `Heap.empty` has no conditional and no lookup law, so the bracket only ever takes
  `Heap.empty x` to `none`. The ban covers `Heap.write`, `Heap.erase` and `Heap.singleton`, and
  **no fragment after this one names any of those three in a bracket or an `unfold`** — checked.
- **`unfold Heap.erase Heap.write` leaves a beta-redex whichever order the names are given.** The
  operation appearing as an *argument* is left as `(fun x => …) x`, which `rw [if_pos]` cannot
  match; `simp only` beta-reduces. `write_comm` escapes only because both its operations are writes.
- **`write_comm`'s one-call proof needs `hne` and `hne.symm`**; drop the second and one goal of four
  survives as `⊢ l₂ = l₁ → v₂ = v₁`.
- **`simp [Heap.erase]` after `funext` with no case split** leaves `⊢ x = l → ¬x = l → none = h x`,
  a true goal `simp` will not close.
- **Author of `09-footprint`:** `erase_singleton` is presented as true of the *one-cell* heap and of
  nothing bigger, and `m1-8`'s `solNote` says the gap is your subject.
- **Author of `28-local-heap` (Unit 25):** this page promises you two things and nothing else — that
  your heap equation is `write_comm`'s statement with the second write replaced by a whole frame
  heap and opens the same way, and that your disjointness half is `write_of_eq`'s shape. Both were
  read off your fragment. It does **not** promise that disjointness replaces the disequality in the
  equation; `write_union_no_disjointness` shows it does not.
- **Weakest part, honestly:** `m1-5`, `m1-6` and `m1-8` are the same two-line proof with rung-4
  hints that are the answer, so real difficulty sits in `m1-7`, `x14`, `x15`. `write_erase_same`
  and `write_empty` are never proved by the reader — only tabulated. (`erase_comm` now has its
  proof shown, in `m1-7`'s `deep`, because the page predicts it needs no hypothesis three times.)
  `write_erase_same` is the obvious extra exercise if §D ever allows a seventh.

## Provenance and checks
Every `state` and `trace` step is `check.sh 08 <snippet>` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so). **At review
every one of the fourteen `code` blocks was re-extracted from the finished file by script and
re-run, and every `trace` step and `state` block was regenerated with `trace_state` and diffed
against the page**: five `illustration`s silent, five `sketch`es giving exactly the quoted errors,
four `verified` blocks byte-for-byte in the fragments, six `sol`s silent. Every "this is false"
claim in a `variants` or `pitfall` field was compiled as its own snippet, including the two
`Heap.empty`-instantiated refutations (which need `Heap.empty` in the bracket to close), the
`defined`-weakening of `write_of_eq` with witness `⟨1, singleton_same 0 1⟩`, both `x15`
alternative statements, the dropped-namespace message set, and the `⊢ v₂ = v₁` / `⊢ some v₂ = some
v₁` / `⊢ l₂ = l₁ → v₂ = v₁` / `⊢ x = l → ¬x = l → none = h x` residues.

All green: `node --check`; `lint.mjs 08-heap-laws` 46 blocks, 0 errors, 0 warnings;
`ledger.mjs 08-heap-laws` 0/0 and edition-wide 0/0, **no `ledgerAllow`, no `ledgerForward`**;
`render-check.js` 0 problems; `verify.sh 08` and bare `verify.sh` clean; banned-phrase grep clean,
including the widened sweep (`obvious`, `worth …-ing`, `of course`, `simply`, `just`,
`essentially`, `it turns out`, first person plural).

## What review changed
Recorded so a successor does not reintroduce any of it.

- **A false claim about downstream reuse**, in the closing `note`: "The rest are the equations that
  make the rewriting in Units 29 and 30 go through without anyone thinking about them." Unit 29
  cites `write_singleton` and nothing else; Unit 30 cites none of the eleven. The note now names
  the real consumers, says the other nine are never called by name, and says why they are here
  anyway — an interface is only usable without checking if it was finished before it was needed.
- **A false claim about Unit 25**, in `m1-7`'s `why` and the same `note`: that `heapLocal_write` is
  `write_comm`'s argument "with the disequality replaced by a disjointness hypothesis". Read the
  fragment: the heap equation needs no hypothesis (`write_union_no_disjointness`), and where
  disjointness is spent the move is `write_of_eq`'s. Both rewritten; `x14`'s `why` was already
  right and is untouched.
- **A false claim about Unit 26**, in `m1-6`'s `why`: that `erase_write_same` is "the shape Unit 26
  relies on when it shows that locality composes". `heapLocal_seq` threads the intermediate heap
  through explicitly and has nothing to do with it. Replaced by the true forward pointer: reading a
  stuck `simp` goal as a request for a lookup law is how Unit 25's proofs are written.
- **A claim about the assignment axiom that Unit 23 does not bear out**, in `m1-5`'s `why`:
  `hoare_write` *does* name the old value in its precondition. Rewritten around what is true — the
  old value disappears from the postcondition, and `write_singleton` (this law at `Heap.empty`) is
  what licenses that.
- **An absolute unfolding ban the corpus breaks twice.** "From Unit 07 on, no proof in this course
  unfolds `Heap.write`, `Heap.erase`, `Heap.singleton` or `Heap.empty`" — `15-pointsto` and
  `22-exec` both use `simp [Heap.empty]`. The ban is now over the three operations that have
  conditionals, with a paragraph carving `Heap.empty` out and saying why. Same fix in the third
  retrospective answer.
- **Two wrong counts.** "six of the eleven proofs on this page" put a definition in a bracket — it
  is ten of the eleven, and the sentence also said "on this page" of proofs three of which are only
  tabulated. And "Every one of them is `funext` followed by a case split followed by a decision
  about a conditional" in the first retrospective answer — `write_of_eq` is not, which is the point
  of `x14`.
- **`redex` and `beta-reduce`, used five times and introduced nowhere.** Neither word occurs in any
  earlier Edition-2 unit. The two uses that came *before* `x15` (in `m1-5`'s `deep` and `m1-7`'s
  `walk`) are now plain English; `x15`'s `expl` introduces both words in one clause, at the point
  where the distinction between `unfold` and `simp only` is the exercise.
- **`partial commutative monoid` named in the third retrospective answer** — §E.4 books it at
  Unit 10, four units below this row, and §E's rule is *must not be mentioned*. The sentence
  carrying it also restated, almost verbatim, a main-line sentence eight blocks earlier ("Unit 38
  changes the model outright…"). Cut; the main-line sentence keeps the point.
- **`transports` used as a technical noun** in the first retrospective answer, with nothing said
  about it. Rewritten to the consequence, which is what the argument needs.
- **`disjoint` / `disjointness` used in prose**, which `05-update`'s review had already removed from
  its own page for being Unit 08's word about two heaps. Both occurrences now say "regions of
  memory that do not overlap".
- **A bare assertion that could be a theorem** (PEDAGOGY §7). The page predicts three times that
  `erase_comm` needs no hypothesis and never showed it. Its two-line corpus proof is now a
  `verified` block in `m1-7`'s `deep`, immediately under the prediction, with the caption saying
  the coinciding region closes like the other three.
- **Hint-rung drift in `m1-8`.** Rung 1 gave the pointwise argument instead of restating the goal.
  Rung 1 now states both goals unfolded (verified against `simp only` output); rung 2 carries the
  argument.
- **A reader stall in the schema `txt`.** `‥` appeared in the schema line with nothing saying what
  it stands for; the caption now says.
- **A gap in the schema paragraph.** "the second row read at `Heap.empty` is `erase_singleton`" —
  it is `(Heap.singleton l v).erase l = Heap.empty.erase l`, and the missing step is that erasing
  from the empty heap changes nothing. Supplied.
- **An over-specific promise about Unit 38** ("turns it into a variant of the model in which two
  owners may hold the same cell") — §D Unit 38 lists fractional ownership among things it
  *sketches*. Weakened to what the plan supports.
- **Banned-phrase family:** "worth checking", introduced by this review's own first draft and
  caught by the widened sweep. Rewritten.
