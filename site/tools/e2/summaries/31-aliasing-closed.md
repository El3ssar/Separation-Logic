# Unit 28 · `aliasing-closed` · The opening question, closed
`site/content/31-aliasing-closed.js` · 37 blocks (35 non-`ex`), 2 exercises, 51 KB rendered, ~1650
words of main line (≈2.7 screens). 25 `p`, 6 `code`, 3 `trace` (2 in `deep`, 1 in a main-line
`detail`), 2 each `sec` `h3` `note` `detail`, 1 each `anat` `cmp` `tbl` `state` `dod`.
**Lean fragment untouched.** No ledger row, no waiver.
**Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review**;
every goal state, every quoted compiler message and all eight illustrations were re-derived from
Lean, and two new goal displays were added.

## One job
Discharge Unit 00's promissory note with two machine-checked theorems, and state in one page what
the course has established.

## The hook I left (verbatim, final block; §D's wording word for word)
> The logic is sound and its central rule is proved. It is not yet a *method*: every verification so
> far has been two commands long, and each needed hand-chosen intermediate assertions and a chain of
> renormalisation. Making that routine is the next module.

Opens on `30-frame`'s hook in three words ("Here it is.").

## Introduced
**Tactics, syntax, notation: none**, as §D specifies.
**Names now usable:** `classical_conjunction_rule_is_false`, `separated_write_ok`.
**Illustration-only, no row, collision-checked:** `refuted_at_the_postcondition`,
`distinct_addresses_do_not_save_it`, `classical_rule_repaired`,
`the_side_condition_is_in_the_precondition`, `separated_write_one_line`,
`same_value_is_no_counterexample`, `no_heap_satisfies_the_aliased_precondition`,
`preserves_without_heapOnly`.
**Concepts:** the classical rule refuted inside the logic · **two refutations denying different
things** — the postcondition is unsatisfiable at any state (Unit 00's `x02` with the quantifiers
restored) versus the final heap this command produced · the side condition moved from a *rule*'s
hypotheses into a *specification*'s precondition, where it is derived rather than assumed · **the
honest count**: both specifications ask the caller for the same two cells, and the classical one
needs *two additions* on top — the disequality as a hypothesis, and an existential in the
precondition to say the written cell exists at all. Do not restate this as "three hypotheses
against none"; that counts the classical precondition and not the separating one.
**Rejected alternatives, all compiled:** `l₁ ≠ l₂` as the whole repair · the honest
three-hypothesis classical rule (7 lines) · `a = b` as the instance · the one-term `x56` · the
reversed star order · `heapOnly_pointsTo` in `Preserves`' slot.

## Exercises
`x55` **classical_conjunction_rule_is_false** [C 4, hard] — the opening question, refuted; 5-step
trace; a fold with the 27-line post-`cases` state.
`x56` **separated_write_ok** [D 1] — the same specification with `∗`, framed, four lines.

## Warnings — compiled or grepped
1. **`x56` is a strict instance of Unit 27's `write_with_frame`** — `write_with_frame l₂ l₁ b 5 a`
   compiles. The page says so, in `deep`, with the reason to keep the four-line form. Do not let a
   reviewer "simplify" the `sol`.
2. **The refutation does not need `cases hex`** — `h3` and `h5` are two claims about the same `s'`.
   The shipped proof is the longer one on purpose (§D objective 2 says "off the final heap"); the
   short one ships as an `illustration` and the page contrasts what each denies.
3. **The classical rule is false a second time, with no aliasing in it** — not in §D, and the
   strongest content here. `ptsAtLeast l₁ a` never says `l₂` is allocated, so at `l₁=0, l₂=1,
   h = singleton 0 3` the command cannot run and `Hoare`'s existential fails. The sound classical
   rule therefore needs **two additions** to what Unit 00 wrote — `hne : l₁ ≠ l₂` and
   `aExists (fun old => ptsAtLeast l₂ old)` in the precondition. This makes objective 4's sentence
   checkable.
   **`classical_rule_repaired` names its side condition**, so "a side condition it cannot name"
   (§D objective 4, verbatim) is false of the two-cell rule and the page does not say it. What is
   true and what the `note kind:'key'` says: the rule can be repaired one cell at a time but not in
   general, because the cells needing permits are the caller's and the rule has no vocabulary for
   them.
4. `hl` in `| write hl =>` is bound and never used, silently; `| write _ =>` compiles.
   `hall 0 0 3 5 σ h hp` applies straight through the folded `Hoare` — seven arguments, no `show`.
5. **Downstream citations, grepped: ZERO** for both theorems. `x55`'s `why` says so.
6. **The `have base` in `x56` is a restatement and is NOT required** — the one-`exact` form compiles
   (30-frame warning 4, re-confirmed). Said in `solNote`.
7. **`cmp` sides default to `tag:'verified'` and `lint.mjs` checks them like a `code` block.** Mine
   are re-broken statement excerpts, hence `tag:'sketch'`. Not in AUTHORING.md.

## Not explained
Everything through Unit 27, in particular `Hoare`'s existential, `Exec` and inversion, `↦`, `∗`,
`hoare_frame`/`HeapLocal`/`Preserves`/`HeapOnly`, `have` as restatement, `✝`, the projection bloat.

## Deviations
1. **35 non-`ex` blocks against §D's ~18**, ~2.7 screens against ~3. ERRATA §18 makes 40 the *floor*
   for units 24–28; §D makes this one deliberately the shortest. I kept §D's intent. The honest
   expansion, if wanted, is a worked reading of the 27-line state now in a fold.
2. **§D says "nine lines of refutation beside four lines of proof".** The bodies are **eight** and
   four; the page says eight.
3. §D's `tbl` is "of what is and is not established". The table holds the nine established links;
   the three gaps are a `note kind:'warn'` beneath it. Objective 5 is met in full.

## Provenance and checks
Every display is `check.sh 31 <snippet>` output with `trace_state`, position prefix dropped.
**Three omissions, each stated in the adjacent `h`:** the three-line `hall` after the first state,
`h3`/`h5` in the last three steps of `x55`'s trace, and all hypotheses in the two displays of the
`classical_rule_repaired` fold; the `x55` fold carries the full 27-line state. All six quoted errors
came from breaking real proofs. The 8 illustrations compile as one file.

**Re-derived from scratch at review and diffed against the page: 0 unmatched.** The five `x55`
states (`intro`, `obtain`, `cases`, `have`, `rw`), the 27-line post-`cases` fold, the two `x56`
states, and — new at review — the post-`refine` and post-`show` goals in `classical_rule_repaired`
(`case refine_1`; the `refine_2` display was compiled and is described, not shown). Every quoted
compiler message reproduced byte for byte: `singleton_same 0 3` against `Heap.empty`;
`simp [ptsAtLeast] at h3` leaving `h3 : s'.heap 0 = some 3` then `unsolved goals`;
`rw [write_same] at h3` failing on the pattern `Heap.write ?h ?l ?v ?l`; `hoare_write l₂ … 5`;
`heapOnly_pointsTo` in `Preserves`' slot; the swapped-star `Type mismatch`. Also compiled at review:
`| write _ =>` in place of `| write hl =>` (the `walk`'s claim).

Green at review: `node --check`; `lint.mjs 31-aliasing-closed` **0/0**; `ledger.mjs` **0/0**,
`frags` clean, sweep 3 (pre-existing); `render-check.js` **0**; `verify.sh 31` (1655/237);
banned grep 0.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no Lean. Fourteen fields rewritten, one main-line
`detail` added (a two-step `trace` on `classical_rule_repaired`).

**Facts that were wrong.**
- **"three hypotheses against none"** (`cmp` left, the paragraph above it, `youWill` 5, the `dod`,
  and "the honest classical rule needs three hypotheses rather than one"). The count charged the
  classical rule for its precondition and gave the separating one its precondition free. Both ask
  for the same two cells; the classical one adds two things. Rewritten in all five places.
- **`orient.payoff`: "the last unit in which the frame rule is the subject rather than a tool"** —
  it is a tool *on this page*; Unit 27 was where it was the subject. Replaced with what the reader
  actually carries forward (the two-step shape, and Unit 29's four moves).
- **The `refuted_at_the_postcondition` caption said "the witness for the existential is
  discarded"** — the witness `s'` is kept and used; the *run* is what `_` throws away.
- **"Inverting the run produces the premise `Heap.singleton 0 3 1 = some old✝`"** — Lean prints
  `{ store := fun x => 0, heap := Heap.singleton 0 3 }.heap 1 = some old✝`. Reworded so no display
  is claimed.
- **"`write_with_frame` is the same statement with the four data left as variables"** — `x56`'s four
  data are already variables; what Unit 27 generalises is the *fifth*, the written value.
- **"`Exec.write` has one rule"** (`x55`'s `expl`) — `Exec` has one rule whose conclusion is a run
  of `.write`, which is what the `walk` said two fields away.
- **`orient.needs` listed `singleton_other`**, which the page never uses; it uses `write_other`.
- **The `note kind:'key'` said the classical rule "needs a side condition it cannot name"** six
  blocks after the page named it and proved the rule. See warning 3.
- **The concurrency bullet promised that Unit 38 "says which idea on this page it generalises."**
  §D's Unit 38 licenses concurrency from the PCM structure of memory — Unit 10, not this page.
- **The `dod`'s "a counterexample to the repaired rule"** pointed at `classical_rule_repaired`,
  which is true; the counterexample is to the *disequality* repair.

**Prose.** One re-derivation cut: the `n²` argument, which `00-aliasing.js` block 243 already makes
in full and which the same paragraph had just cited. What replaced it advances instead —
`k` facts carried across cost `k` permits written into the rule's statement, which is what the
`note kind:'key'` then says the rule cannot do. `hints[2]` of `x55` called `absurd` a tactic.
`cmp` right said "on the same three lines" beside a four-line left column.

**The one hole filled.** `classical_rule_repaired` is six tactics on the main line with no goal
state anywhere — PEDAGOGY §7. The new fold gives the post-`refine` goal and what `show` does to it,
which is also the only place the `∃`-inside-`aAnd` `intro` pattern is explained.

## Weakest part, honestly
`x56` is one `have` and one `exact` and is provably an instance of a theorem the reader proved last
unit, so it measures nothing. `x55` is the only exercise with teeth and its rung-4 hint hands over
the instance, which is its one creative step. No [G]. The "what is settled" table is a claim about
the whole course that this unit cannot check — every row was traced to a fragment by hand.
