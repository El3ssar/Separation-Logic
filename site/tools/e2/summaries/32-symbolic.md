# Unit 29 · `symbolic` · Symbolic execution
`site/content/32-symbolic.js` · 59 blocks (52 non-`ex`), **7 exercises**, 98 KB source / 140 KB
rendered. 31 `p` top-level (37 counting `deep`), 9 `trace` (**all in `deep`**), 9 `code` (6
top-level), 5 `sec`, 2 each `note` `state` `ol`, 1 each `txt` `tbl` `cmp` `anat` `dod`.
**No `detail`.** **Lean fragment untouched.** One `ledger.json` row edited. No waivers.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**;
every goal state, every quoted compiler message and all four illustrations were re-derived from
Lean, and every `variants` claim was recompiled.*

## One job
Establish the working style — split, frame, apply, renormalise — supply the glue lemmas, and verify
two real programs with `Exec` appearing nowhere.

## The hook I left (verbatim, final block; §D word for word)
> Two programs, both two commands long, and one of them took a page. A four-command program will
> need four intermediate assertions, all chosen by hand — and the only thing you have not seen is
> what happens when a *load* has to preserve a fact about a different variable.

Opens on `31-aliasing-closed`'s hook in two words ("Routine means this").

## Introduced
**Tactics, syntax, notation: none**, as §D specifies.
**Names now usable:** `StoreStable`, `storeStable_write`, `storeStable_free`,
`preserves_of_storeStable`, `readAndFree_framed`, `hoare_write_val`, `pure_star_regroup`,
`hoare_load_and`, `and_fact_star`, `and_fact_star_intro`, `copyCell`, `copyCell_spec`,
`exec_seq_assoc`, `moveCell`, `moveCell_spec`.
**Illustration-only, no row, collision-checked against all 39 fragments and all e2 pages:**
`load_not_storeStable`, `pure_star_regroup_derived`, `copyBack`, `copyBack_by_shape`,
`copyBack_by_pure`, `hoare_seq_regroup`, `moveCellRight`, `moveCellRight_spec`.
**Concepts:** the four-move loop as a stated discipline, with the test *if `Exec` appears in one of
your proofs you are missing a lemma* · **store-stability** as a hypothesis on the **command** where
heap-onlyness is one on the **assertion**, with a 5-row `tbl` and a paragraph naming all *three*
cases the two columns produce · `have step : Hoare … := …` as a habit · a rule's **shape** as a
design decision with a countable cost · `;;` associative for runs, not for terms.
**Rejected alternatives, all compiled:** `preserves_of_heapOnly` on a `pure` frame · `hoare_write`
for a `.var` atom · `pure φ ∗ P` for `hoare_write_val`'s precondition · `hoare_load` where
`hoare_load_and` fits · the other middle assertion for `copyCell_spec` · `fact` for `pure` in
`pure_star_regroup` (refuted) · `pure` for `fact` in `and_fact_star` (refuted) · the carried-over
tuple tail in `hoare_load_and`.

## Exercises — SEVEN, not §D's six (deviation 1)
`x57` **storeStable_write / storeStable_free / preserves_of_storeStable** [D 2] — two inversions and
one `rw`. `x58` **readAndFree_framed** [D 2] — Unit 23's defeat redone; `deep` has a `cmp` of the two
verified proofs. `x59` **pure_star_regroup** [C 3] — the bookkeeping entailment. `x60`
**hoare_load_and / and_fact_star / and_fact_star_intro** [C 3] — the composable load rule; `deep`
carries the `copyBack` measurement. `m9-1` **copyCell_spec** [C 4, hard] — the first verification
with all four moves in play. `m9-2` **exec_seq_assoc** [C 3] — nested inversion. `m9-3`
**moveCell_spec** [C 2] — three tactics; the `emp` the freed cell left behind.

## Warnings — every one compiled or grepped
1. **ZERO downstream citations for every declaration in this fragment**, re-grepped at review over
   `33-*`…`41-*` with word boundaries: `StoreStable`, all three `storeStable*`,
   `preserves_of_storeStable`, `hoare_write_val`, `pure_star_regroup`, `hoare_load_and`, both
   `and_fact_star*`, `copyCell*`, `moveCell*`, `exec_seq_assoc`, `readAndFree_framed` — **all zero.**
   `x57`'s `why` says so. **Do not upgrade any of these into a promise.**
2. **§D's claim about the second load rule is too strong.** `hoare_load_and` does **not** shorten
   `copyCell_spec`: the reshaping there is a *commutation of two cells*, and it costs the same from
   either rule — the `aAnd` route needs a swap under `aAnd` that **no lemma in this course
   provides**. Where the shape pays is when the fact and the next command's cell are already
   together: `copyBack` (`x := [l] ; [l] := x`) is two names against four. Both compiled, both in
   `x60`'s `deep`; the page states the limit.
3. **§D objective 2 says store-stability is "strictly stronger" than heap-onlyness. It is not, and
   the page refutes that rather than repeating it.** Neither implies the other; the `tbl`'s last two
   rows show the two gaps, and the paragraph under it now names all three cases — load + `↦` frame
   (left column only), write/free + store fact (right column only), **load + store fact (neither)**.
   That third case is the unit's one open gap and is what the hook points at.
4. **Store-stability is *forced* exactly once** — `readAndFree_framed`'s free step, frame `pure φ`.
   In `copyCell_spec`'s write step and `moveCell_spec`'s free step the frame is a `↦`, so
   `preserves_of_heapOnly _ (heapOnly_pointsTo …)` also compiles (re-verified at review). §D's "two
   *different* `Preserves` helpers" is a choice there, not a necessity; `m9-1`'s `variants` says
   which swap compiles and which cannot.
5. **`pure_star_regroup` is two names:** `entails_trans (star_assoc_right _ _ _) (star_mono_left R
   (star_pure_left φ P))`. `x59`'s `solNote` and `deep` say so. **The three names come from Units 15,
   16 and 17, not two** — `star_assoc_right` is `18-star-assoc`.
6. **`copyCell_spec`'s second `have step` writes `(Atom.var tmp).eval σ` where the goal has
   `σ tmp`.** Same term after one iota step; `exact` accepts silently. The trace prints both and the
   `walk` names it — otherwise a reader thinks the proof is wrong.
7. **`hoare_frame` cuts the star at top level and takes the LEFT conjunct as the footprint.** So the
   wrong middle assertion in `x58` fails *inside the frame*, not at `hoare_seq`.
8. **The bracketing trap:** `copyCell tmp src dst ;; .free src` is `(load ;; write) ;; free`, and
   `;;` is `infixr`, so the natural one-line spelling is the other one. `hoare_seq_regroup`
   (illustration) lifts `exec_seq_assoc` to triples in three lines and makes `moveCellRight_spec`
   one line. **`21-language` already ships `example (a b c : Cmd) : a ;; b ;; c = a ;; (b ;; c) :=
   rfl` captioned "the associativity, proved rather than asserted"**, which collides head-on with
   `m9-2`'s `variants` ("the equality of commands is false"). Both are true — that `rfl`'s two sides
   are one term because the *parser* right-brackets the left one — and `m9-2`'s `variants` now says
   so explicitly. Anyone rewording either page must keep the reconciliation.
9. **`ledger.json`:** `readAndFree_framed`'s stale `status:"migrate"` cleared, note rewritten. The
   file round-trips byte-identically at `indent=1`, so the diff is that one row.
10. **Naming a phantom costs a `ledger.mjs` warning** — "there is no `storeStable_load`" fired.
    Describe an absent theorem, never spell its name.
11. **`30-frame`'s `x54` `variants` promises that "Unit 29 shows what happens to a four-command
    proof when the `emp`s are left standing."** This unit has no four-command program — the longest
    is `moveCell` at three — and the `emp` point is made on `moveCell_spec` instead. Unit 30's
    `swap` is the four-command program. **Inherited defect in `30-frame`, not repairable here
    without inventing a program §D does not ask for.**

## Not explained (earlier summaries own them)
Everything through Unit 28, in particular `Hoare`'s existential, `Exec` and inversion, `✝`,
`HeapLocal`/`Preserves`/`HeapOnly`, the six slots of `∗`, `_root_.pure`'s display, the projection
bloat, `;;`'s right associativity (`21-language`) — and **why Lean cannot guess `Q`**, which
`25-hoare` warning 7 spent there. This unit's contribution is §D objective 6, the *method* for
choosing it.

## Deviations
1. **Seven `ex` blocks.** §F wants one carrying both `m9-2` and `m9-3`; the tooling forbids it (one
   `id` per `ex`, one marker per id, and `lint.mjs` checks `sol` verbatim — the fragment has the
   `m9-3` marker *between* the two theorems). Splitting preserves both load-bearing ids.
   `m9-2` [C 3], `m9-3` [C 2] against the pair's C 3.
2. 52 non-`ex` blocks against ~34 (ERRATA §18: 40 is a summit unit's floor); 140 KB rendered, the
   largest page so far, for seven exercises each with a trace.
3. 9 `trace` against 3, all in `deep`. §D's `txt`, `ol`, `cmp` and `note kind:info` are all present.
4. `x60` is named for three theorems, not §F's two; `and_fact_star_intro` is under the same marker.
5. **No `detail`.** Long displays live in `deep`; no main-line goal state exceeds 8 lines.
6. §D objective 5's "shorten it by choosing a better small rule" is met on `copyBack` — warning 2.
7. §D objective 2's "strictly stronger" is contradicted on the page — warning 3.

## Provenance
**Every `trace`/`state` display is `check.sh 32 <snippet> --incl` output with `trace_state`, byte for
byte, `snippet:L:C:` dropped** (x57 ×6 states, x58 ×3, x59 ×4, x60 ×4, m9-1 ×7, m9-2 ×3, m9-3 ×3).
**Three traces omit binder lines and the first of them says so ("here and below").** Every quoted
error came from breaking a real proof: the `σ`/`σ'` mismatch, `hoare_write` on a variable, `rfl`
before `cases`, the missing `subst he`, the `Eq.refl` slot-count report, `3 provided, but 2
expected`, the right-nesting pair, `don't know how to synthesize implicit argument \`Q\``, and
`x58`'s frame mismatch (metavariable `?m.15` and all).
**Re-derived from scratch at review and diffed against the page: 0 unmatched** across all 30 goal
displays. **Recompiled at review:** the 4 illustrations (each alone, then as one file), both
sketches with their `state` blocks, `StoreStable .skip`, `¬ StoreStable (.assign 0 (.const 5))`,
the reverse of `pure_star_regroup`, `pure`-for-`fact` in `and_fact_star` refuted, both discharger
swaps, the alternative middle assertion for `copyCell_spec` (chain moves to the *precondition* side,
same length), and `moveCell` freeing `dst` (four lines plus one `star_comm`).
Green at review: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` unit **0/0**, frags clean, sweep 3
(pre-existing); `render-check.js` **0**; `verify.sh 32` (1765/252); banned grep **0**.
Edition-wide `lint.mjs` reports only the `m9-1`/`m9-2`/`m9-3` collisions with Edition 1's
`10-m9.js` (ERRATA §9).

## What review changed
No ids, no names, no exercise `goal`/`sol`, no Lean, no block deleted. One `p` added (the proof of
`hoare_write_val`, which arrived on the page as an `anat` with no account of where it came from);
twenty fields rewritten.

**Facts that were wrong.**
- **"the choice is never a judgement call — one of the two columns is empty and the other is a
  name"** (the paragraph under the `tbl`). Flatly contradicted sixteen blocks later, where the page
  says of `copyCell_spec`'s write step "*either* route works". Rewritten to name all three cases,
  which also **delivers `youWill` 3 and the `dod`'s "name a command for which neither does"** —
  previously promised and nowhere supplied — and sets up the hook.
- **`orient.payoff`: the four-move shape "is the shape of every verification in the rest of the
  course"**, and `m9-1`'s `why`: "Everything after this — the capstone next unit — is this shape
  with more steps." **Unit 30's `swap_spec` takes the direct semantic route**, and §D's Unit 30 job
  says so in as many words. Both rewritten; the `txt` caption ("every verification in the rest of
  the course is these") narrowed to this page.
- **"you are held to it for the rest of the course"** about the no-`Exec` rule — Unit 30 breaks it
  deliberately. Clause cut; the rule itself is §D objective 1 and stays.
- **`x60`'s `pitfall` quoted an error the described mistake does not produce.** "Six slots" gives
  `but 5 were provided` preceded by an `Application type mismatch`; the shipped quote (`but 2 were
  provided`) comes from the *five*-slot version, and there is **no** trailing `unsolved goals`
  report. Rewritten around the tuple tail a reader actually carries over, with the real single
  error.
- **`x58`'s `pitfall`: "There is no version of the rule with the frame on the left, and Unit 27 says
  why … at a cost of `disjoint_symm` and `union_comm`."** Unit 27 says the reversed conclusion
  `Hoare (R ∗ P) c (R ∗ Q)` is **true**, at ten lines and four heap-lemma appeals; the
  `disjoint_symm`/`union_comm` pair belongs to a *different* rejected alternative there (the swapped
  cut inside the proof, which then dies). Restated to match `30-frame`.
- **`m9-3`'s `why`: "the first specification in the course whose postcondition owns strictly less
  than its precondition."** False three times over — `hoare_free` is `l ↦ v` → `emp`, and
  `readAndFree_framed`, four exercises earlier on this page, goes from one cell to `pure φ`.
  Rewritten around what `m9-3` actually measures.
- **`x59`'s `why`: "the last time on this page a heap gets named."** `x60`'s two entailments name
  four heaps each. Narrowed to the last time a fact about heaps is *proved*.
- **Three unit attributions.** `StoreStable`'s caption credited Unit 26 for the shape of the
  locality properties (Unit 24 defines them); `pure_star_regroup_derived`'s paragraph credited
  "Unit 15 and Unit 17" for three theorems one of which is Unit 16's; `orient.needs` filed
  `entails_trans` under Units 15–17 (Unit 12).
- **`m9-1`'s `walk` said `pure_star_regroup` was proved "two sections ago".** One section ago —
  ERRATA §27's tell.
- **Two quoted messages were trimmed without saying so:** the `rw` failure in `x59`'s `pitfall`
  dropped `= hP.union hR` from the target expression, and `m9-1`'s `pitfall` rendered Lean's
  backticks around `Q` as single quotes.
- **`youWill` 4 said "four structural rules"** — three rules, four applications.
- **The `dod` omitted objective 7 entirely** (the bracketing repair). Clause added.

**Prose.** One restatement cut: "Everything else on this page is mechanical; `Q` is not" in the
*Split* paragraph, which the `note kind:'key'` two blocks later says better and at length. The
`Preserves` paragraph opened by re-stating Unit 24's definition; rewritten so the same three
sentences are analysis rather than recap. "Everything the plan asked for exists" named a plan a
section and two exercises back — now says which plan. `blurb` said "two programs" where the closing
paragraph counts three. **`m9-2`'s `variants` now reconciles itself with `21-language`'s `rfl`
example** — see warning 8, the one place a reader was liable to stop and conclude the page was
wrong.

## Weakest part, honestly
`x57`, `x58` and `m9-3` are short and their rung-4 hints hand over nearly everything, so the unit is
measured by `m9-1` — where the middle assertion is given at rung 2. **No [G]:** nothing asks the
reader to *state* a specification, which is exactly what Unit 30 will demand. `hoare_write_val` is
handed over rather than proved or set; review added a paragraph on its proof, but a reader who wants
to check it must open the fragment. `and_fact_star_intro` is proved and used by nothing on the page;
it is there because it sits under the marker. And every declaration this unit adds is cited by
nothing downstream (warning 1) — what survives is the working style, which is the one thing the
corpus cannot check.
