# Unit 26 · `local-compose` · Locality composes
`site/content/29-local-compose.js` · 63 blocks (60 non-`ex`), 3 exercises, 92 KB, ~3030 words of
main-line paragraph prose. 29 `p`, 9 `code`, 7 `state`, 5 `sec`, 2 `detail`, 2 `steps`, 2 `trace`,
1 each `anat` `tbl` `note` `dod`; folds and `deep` add 13 `p`, 3 `trace`, 3 `state`, 2 `code`,
2 `detail`.
**Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review**;
one new illustration added (`heapLocal_seq_unnamed`), compiled locally and through
`wasm-check.cjs`. Lean fragment untouched. No ledger row added, no waivers.

## One job
Prove locality closed under `;;`, `ite` and `loop` — and show the sequencing proof failing under
Unit 24's weak definition, stranded on the exact conjunct Unit 24 invented.

## The hook I left (verbatim, final block; §D's wording)
> Every command is local. That is a fact about the language. Turning it into a fact about triples is
> one theorem, eight lines, and every one of them is a step of the informal argument.

Checked: `hoare_frame` is **8 lines** after `:= by`. Opens on `28-local-heap`'s hook in two words.

## Introduced
**Tactics/syntax: none new.** First used in earnest: `rename_i` (§E row "first use 26"), **structure
eta** (row "eta first matters in `heapLocal_seq`"), the **constant-command / index-equation
induction idiom** (row booked here).
**Names now usable:** `heapLocal_seq`, `heapLocal_ite`, `heapLocal_loop_aux`, `heapLocal_loop`.
Page-only, no row, collision-checked: `heapLocalWeak_seq_stuck`, `guardAllocated`,
`heapLocal_loop_aux_flat`, `loopBad`, `heapLocal_seq_unnamed`.
**Concepts:** compositional locality · the conjunct *spent* rather than established · closure
property versus calculation · why `induction` needs a variable index and `cases` does not.
**Rejected alternatives, all compiled:** `HeapLocalWeak` for seq (stranded on
`⊢ sMid.heap.disjoint hFrame`) · `Exec.seq hr₁ hr₂` without the eta `have` · **the whole proof
with the middle state never named** (`heapLocal_seq_unnamed`, nine lines) · `cases` for the loop ·
everything introduced before the induction (`heapLocal_loop_aux_flat`) · `| _ =>` as a wildcard ·
a heap-reading guard (`guardAllocated`).

## Exercises
`m8-4` **heapLocal_seq** [C 3] — composition; `rename_i`; the eta gap. `deep` is a two-step trace
showing the **untrimmed** 22-line context at the hole, plus a fold with the unnamed variant.
`x52` **heapLocal_ite** [D 2] — two direct applications; the guard that transfers by reduction.
`x53` **heapLocal_loop** [C 4, hard] — the idiom; 24 `walk` rows, 6-step `loopTrue` trace, and the
`heapLocal_loop_aux_flat` fold (moved here at review, see below).

## Warnings — all compiled
1. **`rename_i` is NOT necessary for `heapLocal_seq` or for the loop.** Both applications take
   underscores in the store/heap slots — Lean solves `⟨?σ, ?h⟩` against `s'✝` by structure eta —
   and the `have` can be replaced by `rw [← hst₁, ← hhp₁] at hr₂`. Nine lines, compiles, clean
   through `wasm-check.cjs`; same trick shortens the `loopTrue` branch. §E.1's "first *needed* in
   `heapLocal_seq`" and `22-exec`'s "Unit 26 has a proof that cannot be written without it" are
   both **too strong**. What is true, and what the page now says: without a name there is nothing
   to write on the right-hand side of the `have`. The false claim was on the page and is gone;
   the compiled alternative is in `m8-4`'s `deep`, in a fold, with what it costs.
2. **ZERO downstream citations** for all three theorems (grepped `lean/e2`): `heapLocal_seq`,
   `heapLocal_ite`, `heapLocal_loop` appear nowhere after this fragment. No `why` promises one.
3. **`(s' := r₁)` in `heapLocal_loop_aux` is REDUNDANT.** The proof compiles without it and the hole
   gets the identical type. Do not write "Lean cannot infer it"; the `walk` says why it is written.
4. **`induction` AUTO-REVERTS** hypotheses mentioning the target's indices, so the flat form
   (`intro cmd s s' hex heq hFrame hd` before the induction) also compiles — shown in a fold, now
   inside `x53`'s `deep`. The corpus form's advantage is visibility, not necessity. `23-induction`
   warning 7 is otherwise confirmed: no `generalizing` here.
5. **`| loopTrue hb hbody hrest =>` (three names) is ACCEPTED**, silently; the IHs stay inaccessible
   and the complaint is `` Unknown identifier `ihrest` `` lines later, followed by
   `` Tactic `rcases` failed: `x✝ : ?m.354` is not an inductive datatype ``. Under `induction` the
   alternative lists **all premises first, then the IHs**: `hb, hbody, hrest, hbody_ih, ihrest`
   (re-derived from Lean at review — the previous summary said "interleaved", which is wrong).
   Only *too many* names errors (`| seq sMid hex₁ hex₂` → `3 provided, but 2 expected`).
6. **`rename_i s s' s'' _ _` shadows the outer `s s'`** → `s✝ s'✝`. The five are the three states,
   `hbody_ih✝`, `hrest✝`.
7. **Unit 36's author: `loop_invariant` (`39-invariant.lean:4`) is this idiom, line for line.**
   The page names Unit 36 three times; say "the manoeuvre from Unit 26".
8. `Exec.iteFalse hb` in the wrong branch reports `true` against `false`; the two *heaps* printed in
   that message reduce to each other and are not the disagreement.
9. **There is no `∪` notation in this course** (`28-local-heap` warning 9). Two `<code>` spans had
   it; both are now `Heap.union`. Do not reintroduce it.

## Not explained
`Exec`, inversion, `✝`, `HeapLocal`/`HeapLocalWeak`, induction over a derivation, `cases` as
no-confusion (refutation Unit 02, injectivity Unit 20 — both cited), `obtain`, `refine`, `rw [← h]`,
`rw … at h`, `have`, named arguments, the projection bloat.

## Deviations
1. 60 non-`ex` blocks against §D's ~26 (ERRATA §18); comparable to `27-locality` (57).
2. 2 `steps` against 1, 5 `trace` against 2 (2 top-level). §D's `Invalid target` `state` is present.
3. **The loop proof is not on the main line** — only its statement (`anat`), the failure, the idiom
   and three branch displays. Its trace and both full-proof variants are in `x53`'s `deep`.
4. One main-line `state` omits six trailing goal lines (the statement's conclusion verbatim); the
   caption says so, the full 13 lines are in the adjacent fold. All other displays ≤ 8 lines.
5. One `deep` trace step shows a 22-line display in full, deliberately: it is the answer to "what do
   I have to work with", which is `m8-4`'s whole difficulty, and the main line withheld it.

## Provenance
All displays are `check.sh 29` output, `trace_state` for mid-proof states, `snippet:L:C:` dropped
(said in the first caption). **Every state and trace step was regenerated at review through
`check.sh 29` and diffed against the page: all match byte for byte**, including the two 30-line
`induction` branch folds and the `ihrest` extract. Every quoted compiler message was reproduced by
breaking a real proof: the stranded `?_`, `3 provided, but 2 expected`, the `Exec.seq hr₁ hr₂`
mismatch, `Invalid target`, the `iteFalse`-in-both-branches `true`/`false` mismatch, the `h₂`-at-σ-h
mismatch, `Unknown identifier `sMid``/`ihrest`, `?m.354`, the four `Too many variable names` from
`cases`, `| _ =>` leaving two goals, `| seq _ _ =>` compiling silently, and the
`` synthesize placeholder for argument `left` `` from deleting `HeapLocal`'s hypothesis.
All five illustrations compile as one file through `check.sh 29` and through `wasm-check.cjs` on
prelude-29: clean (clears ERRATA §28).
Green at review: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` **0/0**, `frags` clean, sweep 3
(pre-existing); `render-check.js` **0**; `verify.sh 29` (1600 lines, 232 decls); banned grep **0**.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no fragment edit. One fold moved, one `deep` trace
replaced, one illustration added, fourteen fields rewritten.

**Facts that were wrong.**
- **The `rename_i` overclaim** — warning 1. "Here it is the difference between a proof you can write
  and one you cannot" is false; the alternative compiles. Rewritten to the true claim, and the
  alternative shipped as a compiled fold rather than suppressed.
- **Six off-by-one line counts.** "Eight context lines above `s'✝`" (seven, and the same paragraph
  lists seven items); "Nine unchanged context lines above `hb`" (eight); the `loopTrue` caption's
  "eight unchanged context lines" (seven); "the thirteen above them" in `m8-4`'s `deep` (eleven
  above, plus a two-line goal below); "the seven further lines of the goal" in the `skip` display
  (six); "a decision made three units ago" for Unit 18 (eight). Every count re-derived from Lean.
- **Unit 25 misattributed.** "paid for that conjunct twice, once easily and once with a two-cell
  counterexample standing behind it" — the two-cell counterexample stands behind `free`'s
  *equation*, not behind the conjunct, and `free`'s conjunct is the free one. Restated as what
  Unit 25 actually does, which also sharpens the establish-versus-spend contrast the paragraph is
  making.
- **"Eta is at work twice more in this proof"** — once. The paragraph named one place.
- **"the two induction hypotheses in it are printed above, on the main line"** — one is.
- **`∪`** in two `<code>` spans; the course has no such notation (warning 9).
- **"it is the way that works here"**, of leaving the frame quantifier under the arrow — the flat
  form works too (warning 4). Narrowed to "it is the way this proof takes".

**Nothing explained twice.**
- **`m8-4`'s `deep` trace was a verbatim subset of the main-line trace** — same four tactics, same
  four states, four `h` fields restating the ones above them. Replaced by a two-step trace showing
  the **untrimmed** context at the hole, which the main line explicitly withheld, and whose
  commentary reads down the twenty-one hypotheses asking which could close `⊢ Exec c₂ r₁ r₂`.

**Reader stumbles.**
- **A full solution to `x53` sat three blocks above `x53`.** The `heapLocal_loop_aux_flat` fold is
  the whole proof — statement, ten branches, the `loopTrue` body — and it was on the main line
  before the exercise that asks for it. Moved into `x53`'s `deep`, where it is the rejected
  alternative PEDAGOGY §7 wants and no longer the answer key. The main line closes the section on
  the two-line derivation of `heapLocal_loop` instead, and `x53`'s `variants` cross-reference was
  repointed.
- The `skip`-branch paragraph asserted that the goal is about `s✝` without saying why; it now says
  that `induction` abstracted the indices and each branch got its own states back.

**Prose.** Four "worth …-ing" constructions (PEDAGOGY §4's family) cut to zero. "The interesting
part is `hb`, and the interesting thing about it" rewritten. "Eight of the ten branches are like
this" said, after a sentence about two induction hypotheses, that all eight carry them; three do.

## Weakest part, honestly
`x52`'s rung 4 is most of its answer and `m8-4`'s hands over everything up to the last hole, so the
unit rests on `x53` — where the statement is still given, so the reader assembles rather than
invents the strengthening, which is the part Unit 36 will demand. Nothing asks the reader to say
why the flat variant is worse; the fold asserts it. `guardAllocated` is about a guard this language
does not have, so it is the one claim on the page that cannot be run against `Exec`. And the unit
now argues that `rename_i` buys readability rather than possibility, which is true but is a weaker
motive than the one §E.1 and `22-exec` promised the reader — a plan-level inconsistency this unit
can report but not repair.
