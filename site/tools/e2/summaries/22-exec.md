# Unit 19 · `exec` · Running a command is a relation
`site/content/22-exec.js` · 69 blocks (65 non-`ex`), 4 exercises, ~3970 words of main line
(captions, `anat` parts and `cmp` columns counted) plus ~4260 inside the four exercise panels,
5 `trace`, 6 `state`, 12 `code`, 2 `detail`, 2 `svg`, 1 each `anat` `txt` `cmp` `note kind:key`
`dod`. **Lean fragment untouched — by the author and by review.**
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Take Lean's refusal of the interpreter seriously on both its grounds, define `Exec` as an inductive
relation, and do the first four inversions.

## The hook I left (verbatim, final block; §D's wording)
> You can look at the last step of a derivation. The theorem we actually want — that a command has
> at most one final state — needs us to reason about *every* derivation at once, and on a derivation
> that is not the induction you know.

Opens on `21-language`'s hook in four words ("Take the function first.").

## Introduced
**Tactics:** `cases h` as **inversion** · `cases h with | ctor a b => …` · `rename_i`. ERRATA §25
asked me to check by eye that no derivation inversion occurs earlier; **I did, and none does** —
`Exec` is the first `inductive … : … → Prop` in the fragments, so there is nothing earlier to
invert.

**Syntax:** `inductive … : … → Prop` · **indices versus parameters**, with the compiler error naming
the distinction · implicit binders `{s}` · premises as explicit constructor arguments · the
`case skip` / `case seq.skip` tag and its dot-separated nesting · `Too many variable names
provided` and what it counts · `fail to show termination`, `termination_by` (**named, unused**).

**Names now usable:** `Exec` and its ten constructors, `exec_skip_inv`, `exec_assign_inv`,
`exec_load_inv`, `exec_load_stuck`, `exec_skip_seq_inv`. Illustration-only, no row, no fragment:
`runBad`, `ExecP`, `write_inv_bad`, `forever`, `Anything`, `ExecF`.

**Concepts:** inductively defined relations; the **least** relation closed under the rules, with
`Anything` compiled as the counterexample to closure-alone · derivations as finite trees, **two of
them drawn** (a two-command `seq`, and a loop that goes round twice) · big-step semantics ·
**stuck versus diverging**, conflated here (price deferred to Unit 35) · inversion · why safety
needs no error value.

**Rejected alternatives, all compiled:** the `Option State`-valued interpreter (the real
`fail to show termination`); a fuel counter (named, costed, handed to Unit 21); the command as a
*parameter* (`inductiveParamMismatch`); an `Option State`-valued *relation* — **written out in full
offline: 15 constructors against `Exec`'s 10, and the page says fifteen.**

## Exercises
`m5-1` **exec_skip_inv** [D 1] — first inversion; the constructor's equation deletes `s'`.
`x42` **exec_assign_inv / exec_load_inv** [C 2] — inversion producing the state, then inversion
recovering a premise; `v✝` and the underscore witness.
`x43` **exec_load_stuck** [C 2] — a fault is the absence of a derivation, proved.
`x44` **exec_skip_seq_inv** [C 3] — nested inversion; the daggered middle state.

## Not explained (a previous summary says it is known)
What `✝` means (`01-goalstate` owns it, ERRATA §15 — I add only `rename_i`) · `structure`/eta,
`;;`, `Bool` guards, the `a.f b` display rule · `absurd`, `simp`, `intro`, `⟨…⟩`, `;`, `<;>`,
`trivial`.

## Warnings to successors
1. **`obtain ⟨sMid, h₁, h₂⟩ := h` does not "drop" the names** (PEDAGOGY §8's wording). It leaves
   `s'✝ h₁✝ h₂✝` — all three go *inaccessible*, and the only complaint is on the next line.
   `x44`'s `pitfall` says what I compiled, not what §8 guessed.
2. **`rename_i sMid` after `| seq h₁ h₂` works and is compiled on the page** (`x44`'s `deep`),
   giving `s s' sMid : State`. **Author of `29-local-compose`:** `heapLocal_seq` inherits that
   exhibit; do not re-derive it.
3. **`.write`'s premise binds something its conclusion discards** (`old`), so every pre-`x42`
   demonstration of `cases … with` and `rename_i` uses it. An earlier draft used `.load` and thereby
   printed `x42`'s answer above `x42` — ERRATA §27's class. Do not move them back.
4. **`spin` belongs to Unit 21.** My diverging program is `forever`, illustration-only; my
   *terminating* loop is the countdown in the second `svg`'s `example`, also illustration-only and
   deliberately unnamed, so Unit 21 and Unit 37 can name their own.
5. The `note kind:key` is written against `25-hoare.lean`'s real `Hoare`, the **total** reading
   (`∃ s', Exec …`). If that definition changes, this page must.
6. **Unit 22's Hoare rules CONSTRUCT derivations; they do not invert them.** `hoare_skip` is
   `fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩` and `hoare_seq` is two `obtain`s and an `Exec.seq`. The
   first *inversions* downstream are `heapLocal_*` at Units 24–26 and `partialHoare_*` at Unit 35.
   Review found three forward promises on this page that had it the other way round; all three are
   fixed (below). Do not reintroduce them.

## Deviations
65 non-`ex` blocks against §D's ~26 (ERRATA §18) — level with `16-star`, below `21-language`'s 68
and `20-compare`'s 73. §D's `anat` on three constructors is `sketch`-tagged, on an extract: the
clauses are not contiguous. The `txt` draws five rules, not ten; the `code` above it has all ten.
§D's "two derivation trees drawn" is now literally met (it was not before review).

## Provenance and checks
**Every `state` and `trace` block was re-extracted by script at review and matched byte for byte
against `check.sh 22 <snippet> --incl` output** (`trace_state` for mid-proof states, `snippet:L:C:`
dropped, the first caption says so). The 8 `illustration`s compile silently as one file; the 3
`sketch`es give exactly the errors quoted under them; every `variants` and `pitfall` claim was
recompiled separately at review — the `rfl`-first refusal, the ten-goal variable-command split
(exactly `case skip` and `case loopFalse` close, `case assign` is the first that does not),
``Unknown identifier `v` `` / `` `hl` `` / `` `h₁` ``, the `And.intro hl` mismatch, `¬?m.87` with
its `` `simp` made no progress `` twin, the `obtain` pitfall's inaccessible context and its
"major premise type is not an inductive type" follow-on, the `.write`/`.free` stuck twins, and
`x44`'s counterexample carried all the way to `1 = 0`.

Green: `node --check`; `lint.mjs` **0/0** (69 blocks); `ledger.mjs` 0/0, sweep and `frags` clean,
**no waivers**; `render-check.js` 0 problems; `verify.sh 22` and bare `verify.sh` (2314 lines, 316
declarations); `gen-contexts.mjs --prove` **80/80**; `wasm-check.cjs` over the prelude through 22
plus all eight illustrations — *"the reader's Lean accepts all of it"*; banned-phrase grep clean.

## Weakest part, honestly
`m5-1` and `x42`'s first half are one-liners whose rung-4 hints are the answer, so the unit is
measured by `x43` and `x44`; and `rename_i` ships unexercised, which the page admits. The main line
runs ~3970 words against §D's ~4 screens.

## What review changed
**No Lean fragment was edited. No exercise `id`, `name`, `goal`, `sol` or hint rung was touched.**

- **Three forward promises were false and are repaired.** `orient.payoff` said the last exercise is
  "the shape of the `seq` case of nearly every rule in Module 6" — only `heapLocal_seq` has a `seq`
  case. `m5-1`'s `why` said "the `skip` case of the Hoare rules in Unit 22 is literally this proof";
  `hoare_skip` is a term-mode construction with no `cases` in it. `x44`'s `why` said "every
  structural rule of the Hoare logic in Unit 22 opens with the same `cases h with | seq h₁ h₂`";
  `hoare_seq` opens with two `obtain`s. All three now point where the inversions actually are
  (Unit 24 on for locality, Unit 35 for partial correctness), by description rather than by a
  future theorem name, so no `ledgerForward` waiver is needed.
- **A loop's derivation is now drawn, and its `example` compiles.** The `loopTrue` `anat` part
  asserted that the recursive premise at the *same* command is legitimate "because the thing being
  built is a finite tree", and nothing on the page showed one — the most load-bearing claim in the
  unit was the one exhibit it lacked, and §D's "two derivation trees drawn" was unmet. Four blocks
  added after the `seq` tree: a paragraph, an `illustration` (a countdown loop run from a store
  holding `2`, proved by `Exec.loopTrue rfl Exec.assign (Exec.loopTrue rfl Exec.assign
  (Exec.loopFalse rfl))`), a second `svg` of the three-storey tower, and the paragraph that spends
  it — `runBad` needed a shrinking argument because it computed an answer step by step; a term is
  only required to be finite. Compiled with `check.sh 22 --incl` and cleared through
  `wasm-check.cjs`.
- **The `Diverging` bullet was re-deriving what the new tower now shows** and is cut to two
  sentences that lean on it.
- **A reproducibility claim was not reproducible.** The ten-goal `detail` said its state was
  "obtained by putting `trace_state` between the two tactics above", but the example above is
  `cases h <;> rfl`, and inserting `trace_state` into a `<;>` chain prints ten separate reports
  rather than the one quoted. It now says to drop the `<;> rfl` and put `trace_state` on the line
  after the `cases` — which is what I ran, and the output matches byte for byte.
- **"you will use it forty times"** (`m5-1`'s `solNote`) was an invented count, and low: the
  fragments after this unit hold far more than forty inversions. Replaced with a claim that is not
  a number.
- **`x43`'s `why` opened "Edition-worthy in one line"** — §D's internal note to the author, copied
  into text the reader sees. Cut; the sentence after it was already the reason.
- **Two announcing sentences trimmed**, per PEDAGOGY §4: "…and the difference between them matters
  enough to name" pre-announced the paragraph two blocks later that makes exactly that point, and
  "it is the one worth drawing" said nothing once a tree had just been drawn.
- **The loop `example`'s caption says why the final store is two nested `Store.set`s.** Without it
  a reader stops on a term the `assign` rule builds one layer at a time and nothing collapses.
