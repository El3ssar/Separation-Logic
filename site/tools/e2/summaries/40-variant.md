# Unit 37 · `variant` · LAB/capstone — a loop that terminates, and owns a cell
`site/content/40-variant.js` · 55 blocks (52 non-`ex`), 3 exercises, 122 KB rendered, ~1740 words of
main-line `p`. 14 `code` (10 `illustration`, 4 `verified`, **no `sketch`**), 6 `detail` (**none
before the first exercise**), 4 `trace`, 3 `state`, 1 each `txt` `anat` `note key` `dod`.
**One Lean change, made by the original author: the `/- ex x73 … -/` marker moved above
`def drainInv`** (warning 5). No declaration added, renamed or edited — including at review. No
ledger row, no waiver.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**,
and no exercise `id`, `name`, `goal`, `sol`, or `trace`/`state` `src` was touched.*

## One job
The variant rule — an invariant indexed by the turns left — and the capstone: a loop that rewrites a
heap cell every turn and stops, verified with an invariant *and* a variant.

## The hook I left (verbatim, final block; §D word for word)
> The development is complete: a logic, a language, a semantics, the frame rule, verified programs,
> recursive predicates, the wand, `wp`, and both loop rules. Two questions are left. Which of it was
> about heaps? And what would it take to walk that linked list?

Opens on `39-invariant`'s hook in eight words ("One natural number, and it does not go in the
program").

## Introduced
**Tactics: none new.** `induction n with | zero | succ n ih` used to *build* a derivation.
**Names now usable:** `hoare_while_variant`, `countdown_spec`, `drainBody`, `drain`, `drainInv`,
`drain_step`, `drain_stop`, `drain_spec`.
**Illustration-only (22 names, collision-checked against all 39 fragments and every e2 page):**
the `earlyI`/`neverTrue` family, `constant_variant_is_no_loop`, `countUp_step_false`,
`alwaysTrue`/`noRun_alwaysTrue`/`preserving_index_is_false`, `storeOnlyInv*`, `flatInv*`, and the
`drainBodyZero`/`drainZero*` family.
**Concepts:** loop **variant** as an index on the invariant · the index as an *upper bound* on
turns, not a count (`note key`) · a total premise is what lets the induction *construct* a run · the
last `show` in the course, opening `counterGuard`, `BExpr.eval` and `decide` at once · an invariant
carrying a store fact **and** an ownership claim.
**Rejected alternatives, all compiled but the first:** a decreasing variant *expression* (needs
strong induction — argued) · a constant family · postcondition `I 0 ∧ ¬b` (**refuted**, after the
stuck `succ.false` goal) · a `PartialHoare` step premise · `I n → I n` as the step premise, i.e.
Unit 36's rule with a total conclusion (**refuted**) · the increment loop · a store-only invariant
(fails at the *run*) · a cell pinned to a fixed value (fails at the *heap equation*) · a body that
jumps to zero **and its repair by re-indexing**. The last three moved into `x73`'s `deep` at review
— see below.

## Exercises
`m13-4` **hoare_while_variant** [C 4, `hard`] · `m13-5` **countdown_spec** [D 2], the worked example
typed · `x73` **drain_spec / drain_step / drain_stop** [**G** 5, `hard`] — the reader writes
`drainInv` and all three theorems.

## Warnings — each compiled or grepped
1. **`have hx' : σ x = n + 1 := hx` is NOT needed in `countdown_spec`**: `simp` beta-reduces a
   bare-lambda hypothesis, and `simp [Store.set, hx]` closes the goal without it. It **is** needed in
   `drain_step`, where the fact sits under `fact`, a plain `def` `simp` will not open — both `simp`s
   then report `This simp argument is unused: hx` and leave `⊢ σ x - 1 = n`. Re-compiled at review.
   Do not state it loosely.
2. **`refine hoare_while_variant ?_ ?_` without `(I := …)` compiles** and the whole proof goes
   through — the postcondition fixes `I` and `b`. Never claim Lean cannot infer it. **`exact … ?_ ?_`
   does not compile** (`don't know how to synthesize placeholder for argument hstep`) — re-compiled.
3. **Both `show`s in `countdown_spec` are optional** (widen the `simp` bracket); in `drain_step` they
   repair 49-line and 40-line displays, which is the only case the page makes for them. The 49 was
   re-counted at review against `trace_state` output: it is exactly 49.
4. **`check.sh 40` without `--incl` has no `hoare_while_variant`.**
5. **The `x73` marker moved above `def drainInv`.** §D and §F.1 make `x73` the module's one [G] and
   say the reader must *invent the invariant*; below the `def` it was setup. `x73` uses ERRATA §22's
   placeholder `goal`, which draws **no** lint warning here because `sol` is present.
6. **§D's `x73` variants line is too strong.** "A program that jumps to zero needs a more general
   rule" is false — `drainZero_spec` verifies it *with this rule*, by indexing on turns remaining
   instead of the counter. The page ships refutation and repair.
7. **`loop_invariant` (Unit 36) gets its first consumer here**, in `noRun_alwaysTrue` — page Lean,
   not a fragment. `39-invariant` recorded zero consumers.
8. **Downstream: zero.** `41-beyond.lean` cites none of the eight names. No `why` promises one.
9. `hoare_while_variant (drain_step x l)` compiles as well as the corpus's eta-expanded lambda.
   `neverTrue` also occurs in Edition-1's `14-m13.js`; no fragment collision.
10. **The capstone's invariant is still partly pre-announced, and not by this page.**
    `39-invariant`'s `x72` `why` says outright: "there the invariant is a store fact and a `↦`
    conjoined, and the step obligation has to rewrite the heap." That is inside an exercise's
    Why-it-works panel two units back and cannot be fixed from here without editing another
    author's unit. Review cut this page's own, much larger leak (below). **Whoever integrates the
    module should decide whether `39-invariant`'s `x72` `why` should say less.**
11. **Weakest part.** `countdown_spec` is worked in full above `m13-5`, so that exercise measures
    typing — §C.1 mandates the worked example and §D makes it the same theorem. `m13-4`'s rung 4
    hands over the `zero` branch. The unit is measured by `x73`.

## Not explained (earlier summaries own them)
`Exec` · `Hoare`/`PartialHoare` and their binders · `bTrue`/`bFalse`, `aAnd` versus `∗` · `refine`,
`obtain`, `subst`, `cases h : e with`, `⟨…⟩` flattening, `✝` · structure eta and projection bloat ·
`fact` versus `pure` · `write_singleton`, `singleton_same` · truncated `Nat` subtraction.

## Deviations
1. 52 non-`ex` blocks against §D's ~20, ~3 screens against ~2 (ERRATA §18); 4 `trace` against 2.
2. §C.1's one-sentence rule between exercises is broken between `m13-4` and `m13-5` by the worked
   example, which §D's format line puts exactly there.
3. Warning 6. 4. §D asks that the `I 0` version be shown unprovable; the page also refutes it.

## Provenance
Every `state`/`trace` step is `check.sh 40 <snippet> --incl` output byte for byte, `trace_state` for
mid-proof states, `snippet:L:C:` dropped (said in the first caption); trimmed displays name what was
dropped, and the two long ones (11 and 49 lines) are counted, not quoted. Every quoted message came
from breaking a real proof.

**Re-derived from scratch at review, all identical to the page:** the `hoare_while_variant` trace
(probe `pA`, `trace_state` at seven points, prelude-40 *without* `--incl` so the corpus name is
free); the `succ.false` `state` of the `I 0` version (`pB`); the `PartialHoare` mismatch `state`
(`pC`); all eight steps of the `countdown_spec` trace and the post-`show` `state` (`pD`, `--incl`);
all five steps of the `drain_step` trace and the 49-line untrimmed display (`pF`). **Fourteen
falsifiable `pitfall`/`variants` claims re-compiled:** index `0` in the guard-false branch (the
`And.intro hI` mismatch, quoted verbatim); bare `cases b.eval σ` (context identical line for line,
only the case tag differs); `refine ⟨⟨σ, h⟩, Exec.loopTrue hbv ?_ ?_, ?_⟩` under a partial premise
(`don't know how to synthesize implicit argument s'`, goal `State`); dropping `hstop` (false, with
`I n := aTrue` against the never-stopping loop — the one `variants` clause the shipped page had not
compiled); the reversed `show` pattern; `singleton_same l n` (7-line expected type, plus the
consequential `unsolved goals`); `refine ⟨_, Exec.assign, ?_⟩` (11 lines, `hx` unused,
`⊢ Atom.eval σ ((Atom.var x).minus (Atom.const 1)) = n`); `subst` before `have` in `drain_step`
(both orders compile); the wide `simp [counterGuard, BExpr.eval, Atom.eval, hx]`; `exact … ?_ ?_`;
`drain_step` without `hx'`; and the reversed-body repair — `.write l (.var x) ;; .assign …` with
`aAnd (fact (fun σ => σ x = n)) (l ↦ (n + 1))`, `Exec.seq`'s arguments swapped and the lookup at
`n + 2`, whose second bullet is indeed one line shorter.

Green at review: `node --check`; `lint.mjs` **0/0** (55 blocks, 3 ex); `ledger.mjs` **0/0**, frags
clean, sweep 3 (pre-existing), no waivers; `render-check.js` **0 problems**; `verify.sh 40` and bare
`verify.sh` (2327 lines, 319 declarations); the 10 illustrations recompiled as one file against
prelude-40 `--incl`, silent; **prelude-40 `--incl` plus all ten through `wasm-check.cjs` — "clean —
the reader's Lean accepts all of it"**; banned-phrase grep **0**.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no `state`/`trace` `src`, no fragment edit. Four
main-line blocks moved into `x73`'s `deep`; sixteen fields rewritten.

**The solution printed above the [G] exercise.** Four main-line blocks sat between the capstone's
program and `x73`: two paragraphs refuting a store-only invariant and a value-pinned one, a compiled
illustration containing `def flatInv … := aAnd (fact (fun σ => σ x = n)) (l ↦ 0)` — the answer with
one character changed — and a paragraph opening "So the invariant has to own the cell and index its
contents by the same number that indexes the store fact… `aAnd`, not `∗`". §D's whole case for `x73`
is that *the reader is given the program and must invent the invariant*, and that was already done
for them. All four are now a closed `detail`, **"Two invariants that fail, and where"**, first in
`x73`'s `deep`, where they read as the confirmation they are; `variants` no longer restates the two
failures and points at the fold instead. The main line now poses the obstacle without answering it:
the body writes to `l`, `Exec.write`'s premise is that `l` is allocated, so a family that never
mentions the heap admits states where the body has no run — and the step obligation is total.
Four smaller leaks of the same answer were softened: the `fact`-wrapper and `hI.1` forward
references in the `countdown_spec` trace, its `walk` and its `deep`, and `m13-5`'s `why`
("this exercise with a heap conjunct added to the invariant"). ERRATA §27, and `39-invariant`'s
repaired defect.

**Three claims that were false.**
- **"the first proof in this course that a program stops."** Every `Hoare` triple in the course
  asserts termination — `25-hoare` separates the three claims explicitly and `clearCell_spec`,
  `swap_spec` and the rest are total. The sentence now says what is true and what `m13-4`'s `why`
  already said: this is the first triple whose program has no fixed number of steps, so the final
  state cannot be named and the derivation has to be built. The brief's "smallest program whose
  stopping is a theorem rather than an accident" was the same claim and is repaired the same way.
- **"a loop entered at zero with this body would never leave."** `counterGuard` is false at zero, so
  `countdown` entered at zero exits immediately. The claim is about a body allowed to run at zero.
- **"the guard, not the arithmetic, is what keeps that state out of the step obligation"** —
  contradicted three blocks earlier by this page's own trace, which discards the guard conjunct
  because `I (n + 1)` already makes the counter positive. It is the *index* that keeps zero out; the
  guard is what makes the **stop** obligation provable, and the paragraph now says so.

**Two counts.** "opening it is two unfoldings at once", against the adjacent caption's "two
definitions and one decision procedure" and two `walk` rows' "three definitions opened at once" —
it is three. "The proof is one induction, ten lines, and **every one of them** either builds a
derivation or hands one back": `intro n` and `induction n with` do neither; three lines do.

**A misdirected pronoun.** "That closing `simp` is where Unit 18's truncated subtraction is spent",
written directly after two blocks about the *other* obligation, whose closing `simp` is
`simp [Atom.eval, hx]`. Now named: `simp [Store.set, hx']`.

**A hint ladder defeated by its own `setup`.** `m13-4`'s `setup` gave the proof: "`intro n`, then
`induction n`, and in the `succ` branch a case split on the guard — the saved-equation form". That
is rung 2 and most of rung 3, before rung 1. It now states what is in scope and what a total
conclusion obliges each branch to produce, and stops.

**Prose.** Two forward pointers in the `anat`'s callouts ("for a reason the next block makes
concrete", "that is the next section") — PEDAGOGY §4's "as we will see" family; the blocks they
point at follow immediately and open on the subject. "two obligations, one `simp` each", twice, of a
six-line and a four-line proof: each *ends* in a single `simp`. "bookkeeping of a kind done since
Unit 25" narrowed to Unit 29, which is the unit that turned it into a discipline.

**Checked and left alone.** All three `sol`s and `goal`s against the fragment; the `anat`; the four
`trace`s and three `state`s, every one re-derived; the `txt` of the rule on paper; the `note key`;
the ten illustrations, recompiled together and through the reader's WASM Lean; the three
retrospective folds — including the linked-list answer, checked against `lseg`'s real signature
(`List Nat → Loc → Loc → Assertion`) and against §D Unit 38 objective 6, which does promise the
one-line `Cmd` change; the `dod`; and the exercise set, which §D fixes.

## Weakest part, honestly
`m13-5`. §C.1 requires a worked example done in full and §D names `countdown_spec` as both the
worked example and the exercise, so the page prints an eight-step trace of the proof and then asks
the reader to type it. Everything the exercise could measure has already been shown, and its `deep`
trace is three steps of the same proof a second time. It is a fluency drill wearing an exercise's
clothes, and the plan requires it. Against that, `m13-4` is a real construction and `x73` — now that
the invariant is no longer handed over on the main line — is a real design exercise: the reader has
the program, the rule, and the knowledge that the family must say something about memory, and
nothing above the exercise says what.
