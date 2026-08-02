# Unit 30 · `swap` · LAB/capstone — swap
`site/content/33-swap.js` · 58 blocks (55 non-`ex`), **3 exercises**, 74 KB, ~2200 words of main
line. 32 `p`, 6 `sec`, 4 `code`, 4 `detail` (**none before the first exercise**), 2 each `txt`
`note`, 1 each `ol` `trace` `state` `cmp` `dod`; 5 `trace` and 5 `code` counting `deep` and folds.
**One Lean change: `def swap` moved above the `/- ex m9-4 -/` marker**, so all three exercise
contexts hold it (ERRATA §21 — setup, in no `sol`). No declaration added, renamed or edited. No
ledger row, no waiver.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**;
every goal state, every quoted compiler message and all four illustrations were re-derived from
Lean, and every falsifiable `variants` claim was recompiled.*

## One job
Verify a four-command program with two temporaries, staged into rungs — and show honestly where
dropping to the semantics is an engineering call rather than a defeat.

## The hook I left (verbatim, final block; §D word for word)
> Four intermediate assertions, all chosen by hand and all forced by what the <i>next</i> command
> needed. That is a strong hint they can be computed backwards from the postcondition — and they can.

Opens on `32-symbolic`'s hook by producing the program that needs it. **Never name `wp` or any
Unit 31 internal** — hence "computed backwards" (30-frame warning 5).

## Introduced
**Tactics, syntax, notation: none**, as §D specifies.
**Names now usable:** `swap`, `preserves_load_fact`, `swap_heap`, `swap_spec`.
**Illustration-only, no row, collision-checked against all 39 fragments and every e2 page:**
`preserves_star`, `swap_by_composition`.
**Concepts:** intermediate assertions read **backwards**, each a fact about the *next* command · **the
store side of separation** — distinct variables do not interfere, but nothing splits the store, so
the disequality must be written down where heap disjointness is derived · a `Preserves` obligation
as an *interaction*, killable at either end or at both (three dischargers, tabulated in
retrospective fold 2) · the two routes **measured**, and a rule for choosing that is not length.

## Exercises
`m9-4` **preserves_load_fact** [C 3] — the one new ingredient; the line where `tmp₁ ≠ tmp₂` is spent.
`x61` **swap_heap** [C 4, hard] — three regions over a union; two traces.
`x62` **swap_spec** [C 5, hard] — the capstone; Edition 1's open exercise, closed.

## Warnings — every one compiled or grepped
1. **§D's premise is wrong: the compositional route works.** `swap_by_composition` is on the page,
   compiled, and needs **nothing new** — `preserves_star` (4 lines, say four not three) is a
   convenience, and framing twice discharges the same obligation. Both compiled, both shown.
   **Measured: 40 lines direct (`swap_heap` 17 + `swap_spec` 23) against 41 compositional (37 + 4).**
   §D objective 5 therefore cannot rest on length, and the page says so; it argues instead that the
   compositional proof survives a fifth command and the direct one does not, and that the direct one
   is *readable* where an eight-line entailment chain is not.
2. **`swap_spec` cites nothing from Unit 29, and does not cite `m9-4` either.** `m9-4`'s `why` says
   so. Do not upgrade `preserves_load_fact` into a promise.
3. **At `l₁ = l₂` the specification is *vacuously true*, not false** — nothing satisfies
   `(l ↦ a) ∗ (l ↦ b)` (`two_cells_distinct`, `star_same_loc_absurd`; both routes compiled). Do not
   write "the postcondition is false".
4. **The post-`refine` goal in `swap_spec` prints at 383 lines**, the next at 192, the post-`show`
   goal at 3 — all three re-counted at review off `trace_state` output, exact. Both long displays are
   shown as their **first twelve lines**, truncated where Lean broke, with the omission stated in the
   step's own `h`. The `show` acts on the **192**-line goal, not the 383-line one; the page and
   `youWill` 5 now say 192. Without the `show`, `rw [e1]` fails — *Did not find an occurrence of the
   pattern* — because the store prints as `{ store := σ, heap := … }.store.set tmp₁ a`; the failure
   message reprints the whole target expression (≈397 lines at the compiler's wrapping), so the page
   no longer attaches a number to it.
5. **`subst hx₂` in `swap_heap` rewrites `l₂` to `x`**, so `hne` becomes `l₁ ≠ x` and
   `singleton_other` wants `x ≠ l₁`. `hne.symm` compiles as well as the corpus's `fun h => hne h.symm`.
   This is `x61`'s `pitfall` and hint rung 4 **only** — review removed it from the running argument
   (PEDAGOGY §6.2: Lean friction never in the main line).
6. **`;;` is `infixr`, so `Exec.seq` must nest right.** Left-nesting reports three errors at once —
   and the quoted first error is the one produced by `Exec.seq (Exec.seq load load) (Exec.seq write
   write)`, not by a fully left-combed `Exec.seq (Exec.seq (Exec.seq …) …) …`, which reports two.
   Re-derived at review; do not "simplify" the quoted message.
7. **`Preserves` moves only the store.** The heap argument is fixed, which is *why* the six slots of
   a `∗` survive `preserves_star` untouched. The original justification on the page appealed to
   locality and the frame; it was wrong and is rewritten.
8. **The compositional proof does name a store** — the `σ` bound inside `fun σ => σ tmp₁ = a`, in
   every `have step` and every `(Q := …)`. "Names no heap, store or run" was false against code
   printed six blocks away. Both the `cmp` and the fold's closing `p` now say heap and run only.
9. **"Add a fifth command and the existing four rungs are untouched" is idealised.** Appending a
   command replaces the last rung's postcondition; only if the new assertion is chosen so the
   following rung still fits are all four re-usable verbatim. §D's retrospective answer ("one more
   rung, nothing else") is kept, with that condition stated. Do not restore the unconditional form.

## Not explained
Everything through Unit 29 — in particular `Hoare`'s existential, `Exec` and inversion, `✝`, the six
slots of `∗`, `_root_.pure`'s display, projection bloat, `HeapLocal`/`Preserves`/`HeapOnly`, the four
moves, both load rules, `intro` with a destructuring pattern (Unit 14), named arguments (Unit 22).

## Unit attributions used on the page — all re-checked at review against declaration sites
Unit 04 `update_other` (`05-update`) · Unit 05 `write_same`/`write_other`/`singleton_same`/
`singleton_other` (`07-heap`) · Unit 08 `singleton_disjoint`/`singleton_disjoint_iff`
(`10-disjoint`) · Unit 09 `union_of_some`/`union_of_none` (`11-union`) · Unit 12 **the store is not
what `∗` divides** (`14-assertions`) · Unit 17 `two_cells_distinct` (`19-pure`) · Unit 24
`Preserves`/`HeapOnly`/`not_heapOnly_pure` (`27-locality`) · Unit 27 `hoare_frame` (`30-frame`) ·
Unit 29 the four moves and both load rules (`32-symbolic`).

## Deviations
1. **55 non-`ex` blocks against §D's ~20**, ~3.5 screens against ~2 (ERRATA §18).
2. 1 top-level `trace` against 2; 4 more in `deep`, two of them on `swap_heap` as §D asks.
3. §D's `steps` is a `txt` — the four assertions beside the footprints that force them.
4. Warning 1: §D's "how to choose" paragraph is rewritten around the measurement.
5. **§D's format point 1 cannot be met as written.** It wants the four intermediate assertions
   *given outright as hint rung 1*; there is no compositional exercise for that hint to hang on,
   because §D's own exercise table has `m9-4`/`x61`/`x62` and the shipped `x62` takes the direct
   route. The page instead poses the question, tells the reader to write the four down in words
   first, and then gives them — in words, before any Lean, as §D asks. Anyone adding a
   compositional exercise later should move the `ol` into its rung 1.
6. **§D's format point 2 — "the rungs are separate exercises" — is not met**, for the same reason:
   the exercise ids are load-bearing and the table names three, none of them a rung. Rung one is
   worked in full in the main line; rung two's new ingredient is `m9-4`; the remaining two are only
   in the fold.

## Provenance
Every `state`/`trace` line is `check.sh 33 <snippet> --incl` output with `trace_state`, byte for
byte, `snippet:L:C:` dropped — **regenerated from scratch at review and diffed against the page: 0
unmatched** across all 17 goal displays, from four snippets (rung one ×3, `m9-4` ×5, `swap_heap` ×7,
`swap_spec` ×6 plus the two long-display excerpts). Every quoted error came from breaking a real
proof and was re-derived at review: the frame-on-the-wrong-side `Type mismatch` with `?m.14`; the
`x ≠ y` orientation failure with its *This simp argument is unused: hne* linter line; the
`l₁ ≠ x` / `x ≠ l₁` application mismatch; the left-nested `Exec.seq` triple; the `rw` pattern
failure. **Recompiled at review:** the 4 illustrations as one file; `¬ Preserves (.load 0 0) (pure …)`
in exactly five lines; the four-tactic refutation of `swap_heap` without `hne`; `swap_heap` with the
two writes in the other order and **no hypothesis at all**; `swap_heap` reversed, proof unchanged;
`e1` without `hne` leaving `⊢ tmp₁ = tmp₂ → b = a`; `swap_spec` with all three postcondition edits,
failing at the last line and nowhere else with one `Type mismatch`.
Green at review: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` unit **0/0**, frags clean, sweep 3
(pre-existing); `render-check.js` **0**; `verify.sh 33` (1826/256); banned grep **0**.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no Lean, no `trace`, no `state`. One `p` deleted;
fourteen fields rewritten.

**Facts that were wrong.**
- **"the price of Unit 18's decision to keep the store outside the assertion language"** (the
  `note kind:'key'`). Two errors in one clause: the unit is **12** (`14-assertions` — "why the heap
  divides and the store does not"), and the store is *inside* the assertion language, since `fact`
  reads it. Rewritten to "an assertion is a claim about a store *and* a heap, but only the heap is
  what `∗` divides".
- **The justification of `preserves_star`** — "the heaps are the frame, and the frame is what
  locality already promised nothing would touch". `Preserves` holds the heap argument fixed and
  moves only the store; that, not locality, is why the cut survives. Warning 7.
- **"No heap, store or run is named anywhere in the proof"** and the `cmp`'s "Names no heap, no
  store, no run" — contradicted by the `fun σ => …` in every line of the code above them.
  Warning 8.
- **`youWill` 5 and the display paragraph: "`show` makes a 383-line goal into a three-line one".**
  The `show` acts on the 192-line goal; the 383 → 192 step is the second `refine`. Warning 4. The
  same paragraph claimed the `rw` failure "prints all 383 lines back at you" — it prints the target
  expression, which at the compiler's wrapping is ≈397.
- **"the existing four [rungs] are untouched"**, twice (main line and retrospective fold 3).
  Warning 9. Fold 3's closing count, "none of the compositional proof's forty-one are
  [load-bearing]", rewritten as the comparison it was trying to make.
- **The `cmp`'s "Compares `l₁` with `l₂` once".** `swap_spec` uses `hlne` four times (`hH2`, `hH3`,
  `singleton_disjoint`, `swap_heap`).
- **`m9-4`'s `why` said the theorem is "the place `tmp₁ ≠ tmp₂` is spent"** and then, one sentence
  later, that `x62` does not cite it. Narrowed to "where it is spent **on the compositional route**".
- **`m9-4` hint rung 3's "Five instruments and no others"** — the solution also uses `refine` and
  `exact`. "And no others" cut; the anonymous constructor is now named as being under a `refine`.
- **The `l₁ = l₂` gloss**: "the second write puts `a` back over the `b` the first write left" names
  two values at one address that holds one. Restated as the two writes colliding.
- **"Item 1 records a fact that item 4 consumes"** — item 4 is an assertion; the consumer is the
  fourth *command*.

**Prose.** Three restatements cut, all the §4 pattern. "It is measured below" (restating "has no
right answer until it is measured"). "What is not optional is doing it at all" (restating "the
reshaping has to happen somewhere"). **"Two things do differ, and they point in opposite
directions"** — a paragraph-ending sentence whose only content is that two more paragraphs follow,
which is the banned construction by name; the two paragraphs are already parallel. "you now have
both proofs and can hold your own" replaced by something a reader can act on. One `p` **deleted**
entirely: the paragraph before `x61` giving away `subst`'s effect on `hne` — pure Lean friction in
the running argument (PEDAGOGY §6.2), and already in `x61`'s `pitfall`, hint rung 4 and `walk`. The
paragraph above it enumerated the whole three-region plan of `x61` in order, which is hint rungs 2
and 3; rewritten to give the *reason* the order is forced (each resolved split strips one operation)
without printing the answer. The `state` block quoting the frame mismatch names
`preserves_load_fact` one section before it exists; its `cap` now says so.

## Weakest part, honestly
`m9-4` is ten lines and its rung-4 hint hands over most of them, so the unit is measured by `x61`
and `x62` — and `x62`'s rung 4 gives the run, its one creative step. **No [G]:** nothing asks the
reader to *state* the specification, which a capstone probably should; §D's table left no room. The
compositional proof sits in a fold and is never exercised, so the page's central comparison is read
rather than done — and that is the unit's real gap, not a wording one: deviations 5 and 6 both
follow from it. And `swap_by_composition` is mine, not the corpus's: verifying it in the fragment
means putting `preserves_star` in first, which would want a ledger row.
