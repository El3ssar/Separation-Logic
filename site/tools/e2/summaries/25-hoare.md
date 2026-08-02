# Unit 22 · `hoare` · Hoare triples
`site/content/25-hoare.js` · 69 blocks (64 non-`ex`), 5 exercises, 77 KB, ~11.7k tokens of text.
Block census: 37 `p` top-level (47 counting `deep`/`detail`), 12 `code` (7 top-level), 6 `sec`,
5 `trace`, 4 `state`, 3 `note`, 2 `anat`, 2 `txt`, 1 `cmp`, 1 `detail`, 1 `dod`.
**Lean fragment untouched** — by the author and by review; all five exercises were source `C`.
No ledger row added, no waivers.
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Join the two threads in one definition, and prove the structural rules that let the reader stop
unfolding `Exec`.

## The hook I left (verbatim, final block)
> Three structural rules and one axiom, and none of them touches the heap. Consequence never
> inspects the state at all; `skip` hands it back; sequencing passes it along; and assignment
> carries it from precondition to postcondition without looking at a single address. The moment a
> rule does, the question Unit 07 answered becomes operational: *how much* memory does the rule
> mention?

§D says "Three rules"; four are proved, so the count is repaired. §D's second sentence — the part
`26-small-footprint` picks up — is word for word, and that unit's first block ("How much memory
should a rule mention?") lands on it. Opens on `24-interpreter`'s hook in four words ("So write one
down") and never mentions `run`, so a reader who skipped that optional unit loses nothing.

## Introduced
**Tactics: none.** `show` becomes load-bearing, as §E.1 predicts; `have h' : T := e` is first used
as a *definitional restatement*. **Syntax: named arguments `(Q := …)`**, in one sentence at
`assign_twice`, its point of first need.
**Names:** `Hoare`, `PartialHoare`, `subst`, `hoare_consequence`, `hoare_skip`, `hoare_seq`,
`hoare_assign`, `assign_constant`, `assign_twice`. Illustration-only, no row: `SafeAndPartial`,
`substNoHeap`.
**Concepts:** the Hoare triple · **safety as an existential**, its three claims separated (no fault /
termination / postcondition) · total versus partial correctness, and which direction needs
determinism · variance, read off the definition as a function type · **shallow** versus **deep**
embedding, both named; semantic substitution.
**Rejected alternatives, all compiled:** `PartialHoare` as the primary definition, refuted by a
faulting `load` · `SafeAndPartial`, the split form (both directions proved; `Hoare →` needs
`exec_deterministic`) · the deep embedding and its substitution lemma (prose, priced) ·
`substNoHeap` (the heap binder dropped — equal by `rfl`, so nothing is saved) ·
`simp [fact, Store.set]` in place of `show` · a 3-slot bracket for the flat 4-slot one.

## Exercises
`m6-1` **hoare_consequence** [D 2] — pre-/post-composition, variance, the join to Module 3.
`m6-2` **hoare_skip / hoare_seq** [C 2] — one term, one script; the contrast is the lesson.
`m6-3` **hoare_assign** [D 2] — the payoff of semantic `subst`; the backwards reading.
`m6-4` **assign_constant** [C 2] — first `show` in anger, on `fact` applied to two projections.
`m6-5` **assign_twice** [C 3] — first self-chosen middle assertion; the `x ≠ y` you do not need.

## Warnings — all compiled
1. **`⦃ ⦄` cannot carry a command**, contra `21-language`'s handover note: the `notation`
   declaration compiles, the use does not. At `c:1024` the slot takes an atom (`Cmd.assign x e` →
   `unexpected identifier; expected '⦃'`); lower, the closing `⦃` starts a nested triple and the
   parse runs to `:=`. Only a parenthesised command works. **This is now stated in a
   `note kind:'warn'` and nothing more** — review cut the `detail` that showed the three attempts
   (see below). If a later author wants to revive it: write `notation:1024`, never `notation:max`,
   because `max` is fenced by §E.6 and `ledger.mjs` fires on the token — and note that `notation`
   with per-slot precedences (`P:min`, `c:1024`) is **syntax no unit has introduced**; the course
   has only ever declared `infix`/`infixr`.
2. **Downstream counts, grepped and re-grepped at review.** `hoare_skip`, `hoare_assign`,
   `assign_constant`, `assign_twice`: **zero**. `subst` (the transformer): **one**, `34-wp.lean:18`.
   `hoare_consequence`: **6** — `30-frame.lean:30`, `32-symbolic.lean:21,22,79,88,109` — every one
   giving `entails_refl _` for the precondition. `hoare_seq`: **4** —
   `26-small-footprint.lean:39` (term, both arguments applied) and `32-symbolic.lean:20,73,105`,
   **two of those with `(Q := …)`**. `PartialHoare`: `38-partial` and `39-invariant`.
   `exec_deterministic` is spent exactly once in the whole corpus after `23-induction`:
   `38-partial.lean:8`, inside `partialHoare_of_hoare` — which is what this page claims. The `why`
   fields claim this and no more.
3. **Structure eta is spent here**, two units before §E books it: `hoare_seq`'s
   `hex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂` matches `Exec.seq` only by eta.
   **`29-local-compose`: the exhibit is already in `m6-2`'s trace.**
4. **Plan gap.** §E.2 books definitional-restatement `have` at `28-local-heap`; `assign_twice`
   needs it here, because `hx` displays as `fact (fun σ => σ x = 3) σ h` and `simp` matches the
   display — `simp [hx]` reports **`hx` unused** and leaves `⊢ σ x = 3` (recompiled at review). The
   `have` row at `03-compute` keeps the ledger green, so no row moved. **`28-local-heap`: teach
   `.trans`.**
5. **`subst` the tactic still works after `def subst`** (compiled; ERRATA §7). A `note kind:'warn'`
   says only position separates them.
6. `refine hoare_seq ?_ ?_` reports ``don't know how to synthesize implicit argument `Q` `` with
   `context: ⊢ Assertion` — quoted in full; the unit's best motivation for named arguments.
7. **Author of `32-symbolic` (Unit 29), read this.** §D's note on this unit reserves "*why* you
   must supply `Q` — that Lean cannot guess it because it is genuinely a creative choice" for your
   unit. That point is **spent here**, and it had to be: §D's own objective 4 for Unit 22 requires
   the reader to "recognise that *choosing that assertion is the act of verifying a program*", and
   the `don't know how to synthesize` error is the natural motivation for the syntax at its point
   of first need. §D contradicts itself; this page follows the objective. **Your distinctive point
   is your own objective 6 — the *method*: choose the middle assertion by working out what the next
   command's footprint needs, and everything else is mechanical.** Do not re-derive that a choice is
   required; the reader has met the error message and the `⊢ Assertion` context.
8. **Not mine:** `ledger.mjs --sweep` reports `and_assoc_iff`, `and_comm_iff` (`14-assertions`) and
   `emp_iff_all_none` (`15-pointsto`) unrowed. Pre-existing.

## Not explained (earlier summaries say it is known)
Everything in Modules 0–4: the tactic set through `refine`/`obtain`/`subst`/`absurd`/`▸`,
`⟨…⟩` flattening, `✝`, `Exec` and inversion, the Module-3 assertion vocabulary (`aTrue`, `aFalse`,
`aAnd`, `fact`, `emp`, `↦`, `∗`, `⊢`, `entails_refl`, `star_comm`), `Store.set`, `Atom.eval`, `;;`,
`State` and structure eta, the `a.f b` display rule.

## Deviations
1. **64 non-`ex` blocks against §D's ~30** (ERRATA §18); in the band of the neighbours —
   `22-exec` 65, `23-induction` 63, `21-language` 68, `24-interpreter` 86.
2. The hook's count (above).
3. **§D's "the two coincide for the loop-free fragment" is false** — a loop-free command can fault,
   and a faulting one satisfies `PartialHoare` vacuously, which is the page's opening exhibit. The
   page says they differ wherever a run may fail to exist, by faulting *or* by looping. §D's Unit 35
   entry gets this right.
4. **`PartialHoare` is presented first**, `Hoare` second; §D lists them the other way. The failure
   has to be felt before the repair means anything. Fragment order unaffected.
5. **§D's `note kind:warn` on `⦃ ⦄` is one note and no more** — see warning 1.

## Provenance and checks
Every `state`/`trace` step is `check.sh 25 … --incl` output byte for byte, `trace_state` for
mid-proof states, the `snippet:L:C:` prefix dropped (stated in the first goal display the reader
meets, `m6-1`'s `deep`); three steps show only the new hypotheses and say so. **All twelve
Lean-bearing blocks and every `pitfall`/`variants` error message were re-extracted and re-run at
review**, and all matched: the two `hoare_consequence` states, the four `hoare_seq` states, the
three `assign_constant` states, the two `hoare_assign` states, the five `assign_twice` states, the
`don't know how to synthesize` report, the no-`show` `unsolved goals` residue with its unused-simp-
argument linter warning, `hpost σ h hq`, `hpre hp`, `h₂ s₁ hq`, `Exec.seq hex₂ hex₁` with `?m.47`,
the two-error wrong-witness report for `hoare_assign`, `he : aTrue σ h` at the fourth slot,
the accepted `show … = 11` collapsing to `⊢ False`, `simp [hx]` unused, the `.const 4` variant
closing with `simp [hne, hx']`, the `hne` unused-binder warning, and `m6-1`'s reversed-entailment
refutation carried to a contradiction.
The 8 `illustration`s compile silently as one file (only the captioned `hne` warning); there is now
**no `sketch` block and no displayed `sorry`** on the page.
Green: `node --check`; `lint.mjs` **0/0** (69 blocks); `ledger.mjs 25-hoare` **0/0** with `frags`
clean and **no waivers**; `render-check.js` **0 problems**; `gen-contexts.mjs --prove` **94/94**;
`wasm-check.cjs` over prelude-25 plus all illustrations — *"the reader's Lean accepts all of it"*;
banned-phrase grep **0 hits**; ERRATA §7's English-word-in-`<code>` grep returns `emp`, `fact`,
`subst` only, all genuine citations.

## Weakest part, honestly
Three of the five proofs are two or three lines with near-giveaway rung-4 hints, and none is `hard`.
The unit's sharpest idea — total versus partial — is measured by no exercise; `PartialHoare` is
proved about exactly twice, both times in illustrations. `hoare_skip`'s whole proof is given in
prose one block before the exercise asks for it, which is defensible (the difficulty is writing it
in Lean, and PEDAGOGY §8 grades on that) but is the closest the page comes to ERRATA §27's class.

## What review changed
**No Lean fragment was edited. No exercise `id`, `name`, `goal`, `sol` or hint rung was touched.**

- **A false claim about Lean, in `m6-3`'s `deep`.** "The witness can be left to Lean.
  `refine ⟨_, Exec.assign, ?_, hq⟩` compiles as well" — it does not. `hoare_assign`'s postcondition
  is a bare `Q`, so the answer has **three** slots, and the four-slot bracket is rejected with
  ``Invalid `⟨...⟩` notation: The expected type Q {…}.store {…}.heap is not an inductive type``.
  Replaced with `exact ⟨_, Exec.assign, hq⟩`, compiled, along with `refine ⟨_, Exec.assign, ?_⟩`.
- **A forward reference to `hoare_skip`, two blocks before the exercise that proves it** —
  ERRATA §27's class. The `star_comm` illustration was
  `hoare_consequence (entails_refl (P ∗ Q)) (hoare_skip (P ∗ Q)) (star_comm P Q)`. It now takes the
  command and its triple as hypotheses, which is *better* as well as legal: the block's own point is
  that the rule does not inspect the command, and now the Lean says so. Recompiled. `m6-1`'s
  `variants` cited `hoare_skip emp` for the same reason and now names the statement instead.
- **The `⦃ ⦄` `detail` is cut** — four blocks. §D budgets one `note kind:warn` for this and the
  note carries the whole argument standing alone; closing the aside left no hole (PEDAGOGY §5's
  test). It was also the page's only `sketch`, its only displayed `sorry` (§E.1 reserves the
  displayed one for Unit 24's stranded frame proof), the only material on the page that teaches no
  separation logic, and the only place using `notation` with per-slot precedences, which no unit has
  introduced. Three defects and a budget overrun removed by one cut.
- **The `note kind:warn` moved to before `m6-1`**, immediately under the `txt` that draws
  `{ P } c { Q }` on paper — which is where the reader first asks about the brackets, and where the
  round brackets in `Hoare (P) (c) (Q)` first appear. `m6-1`'s `setup` no longer has to point
  forward at it.
- **"Shallow embedding" was never named**, though §D lists it under New mathematics and §E.4 books
  the concept at this unit. The reader got "deep embedding" as the rejected alternative and no name
  for what they have. One clause added at the head of that paragraph, sourcing the decision to
  Unit 12.
- **The two-projection fact was stated four times** — the paragraph under `PartialHoare`, twice in
  the `Hoare` `anat`, and again at the end of `m6-3`'s `deep`. Kept once, at first sight; both
  `anat` parts rewritten to carry something new (what `∀ σ h` assembles, why the projections sit
  unreduced), and the fourth statement cut.
- **An `anat` part that announced the block below it** ("They are separated out below") now says
  what changed between the two definitions, which is not what the `note` below says.
- **A caption that restated the paragraph after it** (the `aTrue` refutation: "nothing is being
  asked of the answer — and the triple is still false, because there is no answer" against "still
  substantial, and still false"). Merged into the paragraph; the caption now says what the proof
  does.
- **An inaccurate caption:** the `PartialHoare` block said its name "is a spoiler which the next two
  pages will earn". It is earned four blocks later, on this page.
- **Three prose fixes to PEDAGOGY §3:** two sentences in the third person about "the reader" and one
  about "a reader" are now second person; "and it is one of the oldest rules in the subject" is cut
  (§2 forbids history in the main text); "and the reason is visible in the definition" is cut (a
  sentence announcing the next paragraph).
- **A duplicated provenance sentence** — the convention was stated both in `m6-1`'s `deep` and in a
  main-line `state` caption. Kept in the `deep`, which is the first goal display the reader meets.
