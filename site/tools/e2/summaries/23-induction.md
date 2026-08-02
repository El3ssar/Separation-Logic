# Unit 20 · `induction` · Structural induction, up to derivations
`site/content/23-induction.js` · 66 blocks (63 non-`ex`), 3 exercises, ~3340 words of main line
(captions, `anat` parts, `tbl` rows, `steps` items, `cmp` columns and `detail` contents counted)
plus ~4710 inside the three exercise panels, 30 goal displays across 18 `state` and 4 `trace`,
12 `code`, 3 `detail`, 2 `cmp`, 2 `note kind:key`, 1 each `anat` `tbl` `steps` `dod`.
**Lean fragment untouched — by the author and by review.**
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Meet `induction` three times on objects of rising difficulty — `Nat`, `List`, a derivation — then
add the one word that makes it strong enough to prove `exec_deterministic`.

## The hook I left (verbatim, final block; §D's wording)
> The relation proves things and computes nothing. You cannot ask it what a program does — only
> offer an answer and ask whether it agrees. Whether that matters is the subject of the next unit,
> and the fact that the next unit is *optional* is itself informative about what a relational
> semantics is for.

Opens on `22-exec`'s hook in its first clause, then shows `cases h₁` stalling in the `seq` branch.

## Introduced
**Tactics:** `induction n with | zero | succ n ih` · `induction xs with | nil | cons x xs ih` ·
`induction h with | ctor … ih` on a derivation · `induction h generalizing y`.
**Syntax / notation:** `List`, `[]`, `::`, `++`, `.length` · `▸`.
**Concepts:** structural induction; the induction hypothesis read off the goal display; `cases`
versus `induction` as one rule, with a compiled failure; generalisation of the hypothesis — **both
by the tactic and by writing the quantifier into the statement**; determinism, and what it licenses
(Unit 35).
**Names now usable:** `allZeros`, `allZeros_length`, `append_nil`, `exec_id`, `exec_deterministic`.
Every illustration and sketch is an `example`: no new name, no ledger row, ERRATA §28 cannot bite.

**Two ledger rows added at review** — `++ (list append)` and `List.length`, both booked at
`23-induction`, both carrying a `notes` saying §E omits them. Neither had a row anywhere, and per
ERRATA §19 an unrowed name is invisible to the checker. `append_nil` and `allZeros_length` need
them, this unit introduces both in prose, and the only other occurrence in the whole verified Lean
is `36-lseg`'s `++`, which is after. `ledger.mjs` is still 0/0 with them in.

## Exercises
`x45` **allZeros_length / append_nil** [D 2] — induction on `Nat` and on `List`; the second shows
`simp` closing a goal *without* the hypothesis.
`x46` **exec_id** [C 3] — ten branches, deliberately pointless proof; read the hypotheses.
`m5-2` **exec_deterministic** [C 4, hard] — `generalizing`, `▸`, guard clash, injectivity step.

## Not explained (previous summaries say it is known)
Induction on `Nat` as mathematics (PEDAGOGY §1 assumes it; I teach the syntax and the escalation) ·
`✝` · `trace_state` (`01-goalstate`) · `cases` as inversion and `cases … with | ctor` · `cases` on a
constructor equality · `rw … at`, `have`, `subst`, `absurd`, `simp`, `rfl`, `intro`.

## Warnings to successors
1. **`append_nil` is hollow and the page says so.** `xs ++ [] = xs` closes by bare `simp`, no
   induction, and the corpus proof's `cons` branch never consults `ih`. I made that the lesson. Do
   not cite it downstream as list-induction practice — `35-listrep`/`36-lseg` are the first real
   ones.
2. **Eight of ten branches of `exec_deterministic` close without `generalizing`.** Only `seq` and
   `loopTrue` fail, two errors each. §D says "the `seq` case fails"; it is two cases, four errors,
   and the `loopTrue` pair is **not** word-for-word identical to the `seq` pair (an earlier draft of
   this page claimed it was; fixed at review).
3. **`| succ n =>` with `ih` omitted is not an error.** Lean makes the hypothesis inaccessible
   (`a✝`); the complaint arrives later as `Unknown identifier ih`. `x45`'s pitfall.
4. **`cases hl'` before `rw [hl] at hl'` is refused** — `Dependent elimination failed: Failed to
   solve equation some v✝ = s✝.2 l✝`. The `rw` is what makes a heap lookup a constructor equation;
   this value-carrying two-step recurs.
5. **`generalizing` on an index is refused:** `Variable s cannot be generalized because the
   induction target depends on it`.
6. **`have hmid := ih₁ h₁'; subst hmid; exact ih₂ h₂'` replaces `▸`** in the `seq` branch, compiled
   and wasm-checked — the escape if a later `▸` guesses wrong. **`revert` has no ledger row and I
   used none**; `42-tactics` should decide whether it deserves one.
7. **`generalizing` occurs exactly once in the entire corpus — here.**
   `grep -rn generalizing site/lean/e2/` returns one line, `23-induction.lean:35`. **Authors of
   `29-local-compose` and `39-invariant`: your `heapLocal_loop_aux` and `loop_invariant` generalise
   by leaving the quantifier in the statement and stopping `intro` short, not by the keyword.** This
   page now says so, names those two proofs as where that form is used, and carries the compiled
   side-by-side in a `detail`. Do not describe your proofs as "the determinism proof with the states
   renamed" — they are not, and review deleted the sentences on this page that said they were.
8. **Nothing downstream reproduces this page's shape** (induct on one derivation, invert a second in
   every branch). `38-partial` *uses* `exec_deterministic` as a lemma
   (`site/lean/e2/38-partial.lean:8`); `24-interpreter`'s `run_complete` is the only other
   ten-branch induction over `Exec`, and it is optional.

## Deviations
1. **63 non-`ex` blocks against §D's ~26** (ERRATA §18); level with `16-star`, below `22-exec`'s 65.
2. **§D's `cmp` on `ih₁` with/without `generalizing` is retained in substance, not verbatim.**
   Edition 1 puts a 13-line context in the left column, which PEDAGOGY §6.1 forbids in the main
   line. The `cmp` shows the two `ih` lines, extracted; the adjacent `detail` carries both full
   contexts, regenerated from Lean.
3. **§D's third shape is "compositional"; mine is "compositional, or has a rival"**, because
   `loopFalse` has no sub-run and is in that group only because two rules conclude a `loop` run.
4. **§D objective 6 wants `have`+`subst` "when `▸` refuses".** No case here refuses; the long form
   is compiled and justified otherwise, and no refusal is claimed.
5. **§D asks for a `trace` of the `seq` case of `exec_deterministic`. There is none, deliberately.**
   Both `seq` contexts run to 13 lines, over PEDAGOGY §6.1's eight-line limit; they are in the
   `detail`, with the two `ih` lines extracted into the main-line `cmp`. The four `trace`s are:
   `allZeros_length`'s step branch (`x45`), `exec_id`'s `seq` (`x46`), and `load` and the guard
   clash (`m5-2`) — §D's `load` and guard-clash traces, both present.
6. **One main-line goal state is nine lines**, one over §6.1: the `seq` branch of `exec_id`. It is
   the middle member of a trio (`seq`/`iteTrue`/`loopFalse`) whose whole point is the count of
   induction hypotheses, and folding one of the three away would leave the paragraph above it
   pointing at nothing. Left in the open, and recorded here rather than repaired.

## Provenance and checks
Every `state` and `trace` step is `check.sh 23 <snippet> --incl` output byte for byte,
`trace_state` for mid-proof states, position prefix dropped (said in the first `state` caption).
**Re-extracted and re-run at review, all 30 displays, all matching**: the `zero`/`succ`/`cons`
goals; the post-`simp [allZeros]` residue; the `cases n` and `cases h₁` leftovers; all ten `exec_id`
branch goals (three quoted in the main line, `loopTrue` under `x46`); the nine
`Alternative … has not been provided` lines; the four errors from the un-generalised proof; both
`seq.seq` contexts with and without `generalizing`; the three-step `load` trace; the
`Dependent elimination failed` refusal; the two-step guard clash.
The 5 `illustration`s compile silently as one file; the 5 `sketch`es give exactly the errors printed
beneath them; **every `pitfall` and `variants` claim was recompiled separately at review** — the
`a✝` hypothesis and its `Unknown identifier ih`, `` `simp` made no progress `` under `simp [ih]`,
the `cases xs` survival of `append_nil`, `[] ++ xs = xs := rfl`, the false-statement `rfl` failure
under `case zero`, `Too many variable names provided at alternative seq: 5 provided, but 4 expected`
and the `load` twin with its trailing `` Unknown identifier `hl'` ``, the bare-`cases` context with
`h₁✝ h₂✝` new and `h₁✝¹ h₂✝¹` pushed up, the `generalizing s` refusal, the reversed guard rewrite,
`cases h₂; rfl` in place of the named `write` branch, and the ▸-deleted mismatch.

Green: `node --check`; `lint.mjs` **0/0** (66 blocks); `ledger.mjs 23-induction` **0/0**, sweep
(3 pre-existing names, none mine) and `frags` clean, **no waivers**; `render-check.js` 0 problems;
`verify.sh 23` (1071 lines, 185 declarations) and bare `verify.sh` (2322 lines, 318 declarations);
`gen-contexts.mjs --prove` **80/80**; **`wasm-check.cjs` over the prelude through 23, and over that
plus all five illustrations — "the reader's Lean accepts all of it"**; banned-phrase grep zero.

## Weakest part, honestly
`x45` is two four-line proofs whose rung-4 hints are the answer, and half of it is a theorem `simp`
proves alone; `x46` proves nothing by construction. The unit is measured by `m5-2` alone. The `▸`
treatment is one paragraph plus a compiled alternative — the thinnest thing here a later unit leans
on. And the `Nat`/`List` half is honest scaffolding rather than mathematics: it exists so that the
derivation case has one new thing in it instead of three, and a reader who already writes Lean will
find it slow.

## What review changed
**No Lean fragment was edited. No exercise `id`, `name`, `goal`, `sol` or hint rung was touched.**

- **The unit's stated payoff was false, in three places, and is repaired.** `orient.payoff` and
  `m5-2`'s `why` both said that induction on a derivation *with a generalised hypothesis* is what
  proves locality in Unit 26 and the loop rule in Unit 36, and that "both of those proofs are this
  one with the states renamed". Checked against the fragments: `generalizing` appears **once** in
  the entire corpus, on this page; `heapLocal_loop_aux` (`29-local-compose`) and `loop_invariant`
  (`39-invariant`) generalise by writing the quantifier into the statement and stopping `intro`
  short, and their branch shape is `intro heq; cases heq` refutation, not "invert the second
  derivation". Both fields now claim what is true — that those two proofs are inductions over a
  derivation whose hypothesis had to be strengthened first, by a different device — and no longer
  promise a shape the reader will not find. This is `22-exec`'s defect class exactly.
- **The rejected alternative for the unit's central design decision was missing**, which PEDAGOGY
  §7 and §12 require. Added: one main-line paragraph naming the alternative, and a `detail`
  carrying the whole proof written with `∀ {s₂ : State}, Exec c s s₂ → s₁ = s₂` in the statement
  and ten `intro`s instead of `generalizing` — compiled with `check.sh 23 --incl` and cleared
  through `wasm-check.cjs`. It also closes the loop opened by the repaired payoff: the reader is
  now shown the form the two loop proofs actually take, and told what makes the trade turn.
- **`orient.youWill` had `cases` and `induction` the wrong way round** — "Say what `cases n` gives
  you that `induction n` does not". It gives you nothing that `induction` does not, which is the
  unit's own `note kind:key`. Inverted.
- **A verbatim duplicate trace was cut.** "The succ branch, in two moves" in the main line and
  "The step branch of `allZeros_length`, split in two" in `x45`'s `deep` had identical `start`,
  identical steps, identical states and near-identical commentary. The main-line one is now a
  single `state` block showing the residue — a two-tactic proof does not meet PEDAGOGY §7's
  "longer than two tactics" bar for a `trace` anyway — and `x45`'s `deep` keeps the full trace with
  its second step rewritten so it no longer restates the caption above it.
- **An overclaim contradicted by the page three blocks earlier.** "Its value is the ten goal
  states, and every one of them says the same thing: *you may assume the theorem for the pieces*" —
  six of the ten carry no induction hypothesis at all, which the `loopFalse` state and the `tbl`
  both say. Now: four carry hypotheses, six carry none, and why.
- **A `sketch` was tagged `illustration`.** The `have`/`subst` `seq` branch is four lines lifted out
  of a proof and cannot compile alone. Retagged, and its caption now says so — and says that the
  full proof with that branch substituted does compile, which was checked.
- **A false claim about an error message.** "The pair repeats word for word in `loopTrue`" — it
  does not; the names and the types differ. Recompiled and the caption now says what `loopTrue`
  actually reports.
- **Two counts were wrong.** `append_nil` was said to be "here for its two goal states" and one is
  shown; `m5-2`'s `solNote` said "twenty-five lines" of a twenty-seven-line solution.
- **One banned-phrase grep hit** ("just as dead") and one ungrammatical opener ("Something to prove
  about needs to exist first") repaired.
