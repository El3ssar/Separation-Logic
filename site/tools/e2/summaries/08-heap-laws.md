# Unit 06 · `heap-laws` · LAB — equations between heaps
`site/content/08-heap-laws.js` · 46 blocks (40 non-`ex`), 6 exercises, ~1090 words of main-line
prose, 10 traces, 4 `detail` — one before the first exercise. Brief → worked example (blocks 3–19,
the largest section) → six exercises → retrospective. 128 KB rendered.

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

**Concepts:** the schema *a second operation at `l` leaves no trace of the first*, instantiated
four ways · **disjoint operations commute — the germ of the frame rule**, sharpened to: two
operations commute when the parts of memory they touch are separate *or* when they agree where
those parts meet — hence `erase_comm` needs no hypothesis, `write_comm` does, and `write_comm` with
a single value does not · the layering discipline (prove it here so Unit 23 is three lines) · the
unfolding exception, stated openly in the one pre-exercise `detail` · the
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
  `hne`; counterexample and equal-values case in `deep`.
- `m1-8` **write_singleton / erase_singleton** [C 2] — Unit 23's write and free rules; why
  `Heap.empty` must be in the bracket.
- `x14` **erase_erase, write_of_eq** [C 3] — a free win, then a heap hypothesis driving the `pos`
  branch; the only corpus proof here that never unfolds.
- `x15` **erase_write_comm, and the claim it is not** [G 3] — `unfold` versus `simp only`; the
  reader states and refutes the unconditional claim.

## Not explained (earlier summaries say it is known)
`funext`, `by_cases`, `<;>`, `if_pos`/`if_neg`, `congrFun`, `Ne.symm`, `rw`, `unfold`, `have`,
`simp only`, `↓reduceIte`; the three-move shape and the `simp`-versus-`rw` rule; namespaces,
dot-notation display, the six lookup laws and the interface rule.

## I changed the Lean fragment — read this
1. **`write_of_eq` no longer uses `subst`**, which `ledger.json` and §E.1 book at `10-disjoint`,
   two units after this one. `· subst hx; rw [write_same]; exact hl.symm` is now
   `· rw [hx, write_same]` / `exact hl.symm`. A corpus bug, not a preference.
2. **Two `example`s added** — `write_comm`'s counterexample, and `erase_write_comm`'s refutation
   placed immediately after it with no comment between, so `x15`'s two-part `sol` is a contiguous
   substring. §F marks `x15` `N ✔+⧗`. Declaration count unchanged (310).
3. **Never write `/- ex <id> … -/` twice for one id**: `gen-contexts.mjs` treats each as a cut and
   reports `duplicate ex markers`.

## Deviations from COURSE-PLAN.md
1. **§D's third route, "via `write_of_eq`", does not exist**: `write_of_eq` needs the value written
   to equal the value already held, and `write_singleton` writes a different one. Route three is
   instead *through the interface* — the four lookup laws cited by name, nothing unfolded — which
   is the reuse lesson §D wanted. Plan slip.
2. **§D says "two are commutation laws, one carries a disequality".** There are three and two carry
   one. The page states the true counts and makes it the second retrospective answer.
3. **40 non-`ex` blocks against §D's ~22** (07-heap ran 39 against ~28); prose at budget, the
   excess is compiled exhibits.
4. §D objective 3's counterexample sits in `m1-7`'s `deep`, not the main line: PEDAGOGY §11 allows
   one sentence between lab exercises.

## Warnings to successors
- **`unfold Heap.erase Heap.write` leaves a beta-redex whichever order the names are given.** The
  operation appearing as an *argument* is left as `(fun x => …) x`, which `rw [if_pos]` cannot
  match; `simp only` beta-reduces. `write_comm` escapes only because both its operations are writes.
- **`write_comm`'s one-call proof needs `hne` and `hne.symm`**; drop the second and one goal of four
  survives as `⊢ l₂ = l₁ → v₂ = v₁`.
- **`simp [Heap.erase]` after `funext` with no case split** leaves `⊢ x = l → ¬x = l → none = h x`,
  a true goal `simp` will not close.
- **Author of `09-footprint`:** `erase_singleton` is presented as true of the *one-cell* heap and of
  nothing bigger, and `m1-8`'s `solNote` says the gap is your subject.
- **Weakest part, honestly:** `m1-5`, `m1-6` and `m1-8` are the same two-line proof with rung-4
  hints that are the answer, so real difficulty sits in `m1-7`, `x14`, `x15`. `write_erase_same`,
  `erase_comm` and `write_empty` are never proved by the reader — only tabulated. `erase_comm`
  (four regions, no hypothesis, and the reason it needs none) is the obvious extra exercise.

## Provenance and checks
Every `state` and `trace` step is `check.sh 08 <snippet>` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so). All thirteen
`code` blocks were re-extracted from the finished file and re-run: five `illustration`s silent,
five `sketch`es giving exactly the quoted errors, three `verified` fragment text; every "this is
false" claim in a `variants` or `pitfall` compiled too. All green: `lint.mjs` 0 errors / 3 warnings
(multi-theorem `goal`, the `07-heap` `m1-3` pattern); `ledger.mjs` 0/0 here and edition-wide,
**no `ledgerAllow`, no `ledgerForward`**; `render-check.js`; `verify.sh` (310 declarations);
`gen-contexts.mjs --prove` 27/27; banned-phrase grep.
