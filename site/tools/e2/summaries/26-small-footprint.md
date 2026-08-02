# Unit 23 · `small-footprint` · Rules that mention only what they touch
`site/content/26-small-footprint.js` · 62 blocks (56 non-`ex`), 6 exercises, 75 KB, 6 `trace`
(all in `deep`), 3 `state` (all main line), 8 `code illustration` (5 main line, 1 in the `detail`,
2 in `deep`), 3 `code sketch`, 1 `detail`, 1 `defn`, 1 `cmp`, 2 `note kind:key`, 1 `txt`, 1 `ol`,
1 `dod`, 6 `sec`.
**Fragment extended by one theorem (`x48`); two `/- ex … -/` markers moved.**
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**,
by the author or by the reviewer; every `illustration`, every quoted error and every goal state was
re-extracted and re-run.*

## One job
State the three memory rules on exactly the cells they touch, cash Unit 07's exactness decision on
the free rule — then fail to compose two of them, three ways, on the page.

## The hook I left (verbatim, final block; §D's wording)
> Question (iii) has an answer, and it is the reason the next module takes five units instead of
> one. Three correct rules that will not compose, and one program proved from the semantics: the
> missing tool is a rule saying *a command that works on its own memory still works inside a bigger
> heap*. That rule cannot be assumed — it is a claim about what commands *do* — so the next unit
> has to find out what it would take for it to be true.

The three questions are an `ol` directly above it. Opens on `25-hoare`'s hook in six words.

## Introduced
**Tactics, syntax, notation: none**, as §D specifies.
**Names now usable:** `hoare_load`, `hoare_write`, `hoare_free`, `clearCell`, `clearCell_spec`,
`writeTwice_spec`, `readAndFree`, `readAndFree_spec`. Sketch-only: `hoare_write_bad`.
**Concepts:** **small-footprint specification** (`defn`) · its trade — tiny exact rules plus one
structural rule, against big rules with disequality side conditions · reading is not destructive ·
**why the store fact is `pure` and not `fact`**: under `∗` a `fact` conjunct owns an arbitrary heap,
so Unit 07's loose reading returns through the assertion language · the **auto-bound implicit**,
named and explained as a general Lean behaviour at its point of first need, and why the write
postcondition is eta-expanded · the layering point: `hoare_write`/`hoare_free` each end in one
Unit 06 equation and contain no `funext`.
**Rejected alternatives, all compiled:** `fact φ ∗ (l ↦ v)` (provable, strictly weaker;
`¬ (fact ⊤ ∗ (0 ↦ 4) ⊢ (0 ↦ 4))` measures the loss) · `aAnd (fact φ) (l ↦ v)` (equivalent, one
tactic shorter, rejected on *shape*) · the big-precondition write rule (prose) · `l ↦ (e.eval σ)`
unbound · `hoare_consequence` for `clearCell_spec` · the loose `↦` in the free rule (`x16` + `x18`).

## Exercises
`m7-1` **hoare_load** [C 3] — two `refine`s; `pure` forces the cut to be `Heap.empty ∗ singleton`.
`m7-2` **hoare_write** [C 2] — one `write_singleton`; the eta-expanded postcondition.
`m7-3` **hoare_free** [C 2] — one `erase_singleton`.
`m7-4` **clearCell_spec** [D 1] — one term; `(Atom.const 0).eval σ` reduces.
`x48` **writeTwice_spec** [C 2] — composition that works: same footprint both sides.
`m7-5` **readAndFree_spec** [C 3] — the defeat; `Exec.seq` by hand.

## Lean I changed
Added `writeTwice_spec` (§D ⧗) after `clearCell_spec`: `hoare_seq (hoare_write l (.const 1) old)
(hoare_write l (.const 2) 1)`; its ledger row lost `status:"todo"`. Moved the `m7-4` and `m7-5`
markers *below* their `def`s per ERRATA §21 — the reader is handed the program and asked for the
specification. Corpus 2327 lines / 319 decls; `--audit` 13 → 12.

## Warnings — all compiled
1. **`⟨…⟩` flattening nests on the RIGHT.** In `hoare_load` the fifth slot is `pure φ`, a
   conjunction; `…, ?_, rfl, rfl⟩` pushes the extra component into the sixth slot, an `Eq`, and
   Lean says `Constructor Eq.refl does not have explicit fields, but 2 were provided`. A conjunction
   in a non-final slot must be an explicit pair.
2. **Consequence fails on the POSTCONDITION, not the precondition.** `pure φ ∗ P ⊢ P` *is*
   provable (`star_pure_left` + `and_right`). What fails is `emp ⊢ pure φ`, refuted with store
   `fun _ => v + 1`. The store fact is discarded, not weakened — which is what the frame rule
   carries across. An early draft blamed `star_not_weakening`; that was wrong.
3. **`theorem … (l ↦ (e.eval σ))` COMPILES**, `σ` auto-bound as `{σ : Store}` in front
   (`#check` on the declaration confirms the binder is implicit), and the statement is false. The
   bodyless declaration's `unsolved goals` report prints `σ : Store` as its first context line — the
   cleanest auto-binding exhibit I found.
4. **Downstream citations, re-grepped at review over `27-*`…`41-*`.** `hoare_load` **2**, both
   `32-symbolic` (`readAndFree_framed` l.21, `copyCell_spec` l.77); `hoare_write` **2**
   (`30-frame:20` inside `write_with_frame`, the declaration immediately after `hoare_frame`, so
   "the first triple the missing structural rule is applied to" is exact; `31-aliasing-closed:21`
   inside `separated_write_ok`) — **`32-symbolic` does not cite it**, it proves `hoare_write_val`,
   a store-dependent generalisation; `hoare_free` **3** (`30-frame:27` in `free_with_frame`,
   `32-symbolic:23,107`); `readAndFree` **1**. `clearCell`, `clearCell_spec`, `readAndFree_spec`,
   `writeTwice_spec`: **zero.** Every `why` states exactly this and no more.
5. **`32-symbolic`'s `readAndFree_framed` is the answer to `m7-5`** and is already written.
   `m7-5`'s `solNote` promises the reader it re-proves this program from `hoare_seq`, consequence
   twice, and one rule they do not have, with no `Exec` constructor in it — verified true of the
   shipped term. **Author of `32-symbolic`: keep that true.**
6. **`hoare_free`'s pitfall is the state, not the lemma** — naming the final heap `Heap.empty`
   fails at `Exec.free`, whose conclusion fixes `Heap.erase s.heap l`.
7. **`clearCell_spec` and `writeTwice_spec` both unfold a plain `def` inside a `theorem`'s stated
   type** (ERRATA §28's class). Both are accepted by the reader's Lean — confirmed by
   `wasm-check.cjs` over the whole corpus and over prelude-26 plus all eight illustrations. The one
   `:= rfl` on the page, `(Atom.const 0).eval σ = 0`, is written as an `example`, which is the row
   of §28's table that passes.

## Deviations
1. 56 non-`ex` blocks against ~30 (ERRATA §18); below `25-hoare` (64) and `22-exec` (65).
2. **§D's "`m7-4` opens the unit on a win" cannot be met** — `clearCell_spec` *is* `hoare_write`
   specialised, so it cannot precede it. It sits fourth, where §D's own table puts it.
3. §D objective 3 asks that `pure` "forces the cut"; the page proves first that `fact` would *not*,
   with a compiled non-entailment, then reads `Heap.empty` off the state `m7-1`'s trace shows after
   the second `refine`.

## Provenance and checks
Every `state`/`trace` step is `check.sh 26 <snippet>` output byte for byte (`--incl` where needed),
`trace_state` for mid-proof states, `snippet:L:C:` dropped. **All twenty goal states and all three
quoted error blocks were regenerated from scratch at review and diffed against the page: identical.**
The eight `illustration`s compile as one file under `check.sh 26 --incl`, silently; the three
`sketch`es produce exactly the errors printed beneath them. Every `pitfall` and `variants` claim was
recompiled at review — the reversed cut, the flattened tuple, the bare-`pure` refutation, `rfl` in
the write tuple, the `ptsAtLeast` write witness (`twoCells` at 4, disagreement at 9), the
`aAnd emp (fact …)` strengthening, the two `Exec.free` arity errors, both `clearCell_spec`
mismatches and the `_` repair, both `writeTwice_spec` mismatches and the `free(l)` composition, the
three-slot `refine` with its two errors and its residual goal, the reversed `free(l) ;; x := [l]`
(eight proof lines, closing on `exec_load_stuck`), the `emp`-only collapse and the `fact` variant.
Green: `node --check`; `lint.mjs` **0/0** (62 blocks); `ledger.mjs 26-small-footprint` and
edition-wide **0/0**, `--fragments` clean, no waivers, `--sweep` 3 (all pre-existing);
`render-check.js` **0**; `verify.sh 26` and bare `verify.sh` (2327 lines, 319 decls);
`gen-contexts.mjs --prove` **150/150**; `wasm-check.cjs` over the whole corpus and over prelude-26
plus all eight illustrations — *"the reader's Lean accepts all of it"*; banned-phrase grep **0**.

## Weakest part, honestly
Four of six exercises are two or three lines and none is `hard`; the difficulty sits entirely in
`m7-1`'s six-slot tuple and `m7-5`'s refusal to compose. Nothing asks the reader to *reject* a
proposed rule for mentioning too much memory, so the `defn` is unmeasured. `m7-5`'s felt need
depends on the reader trying `hoare_seq` first — a reader who goes straight to the solution feels
nothing. And the page's shape is explain-then-ask throughout: the key lemma of `m7-2` and of `m7-3`
is named in the paragraph immediately above each, which §D's objective 4 requires but which leaves
those two exercises measuring tuple assembly rather than discovery.

## What review changed
**No Lean was edited. No exercise `id`, `name`, `goal`, `sol` or hint rung was touched.** Everything
below is prose, plus one block cut.

- **A wrong attribution to Unit 00.** The page said the big-precondition write rule costs "the same
  disequality Unit 00 added to the classical assignment rule". Unit 00 has no assignment rule; its
  exhibit is the aliased triple `{ [x] = 3 } [y] := 5 { [x] = 3 ∧ [y] = 5 }`, and the reader met a
  Hoare *assignment* rule one unit ago, `hoare_assign`, which carries no disequality at all. Now
  "the aliased triple on its opening page".
- **A wrong attribution to Unit 17.** The `pure φ ∗ P ⊢ P` illustration was captioned "from two
  Unit 17 theorems and nothing else". Its proof is `entails_trans (star_pure_left φ P)
  (and_right _ _)`: `star_pure_left` is Unit 17 (`m4-8`), `entails_trans` and `and_right` are
  Unit 12 (`m3-2`, `m3-3`). The caption now names all three with their units, and says the reader
  proved each — which is true; all three are exercises.
- **A wrong module.** "The rule *this* module is working towards adds untouched memory to both ends
  of a triple." The frame rule is Unit 27, Module 6; this unit is the second and last of Module 5.
  Now "the next module".
- **Three line counts that do not survive counting.** The `fact` load rule was captioned "the same
  cut, the same four lines" — it has four tactic invocations against `hoare_load`'s six, because it
  folds `show`/`simp` into a `by` inside the term. The `aAnd` version was captioned "Four lines
  against five"; the bodies are five and six. `m7-2`'s `deep` said the `funext` proof "is no longer
  than the real proof"; it is two tactics longer. All three now say what is true, and agree with the
  surrounding prose, which was right.
- **A duplicated goal display, and an exercise pre-solved by it.** A main-line `state` block above
  `x48` printed the two obligations left by `refine hoare_seq (Q := (l ↦ 1)) ?_ ?_` — byte for byte
  the same two states as the first two steps of `x48`'s own `deep` trace, with the tactic line
  repeated a third time in `x48`'s `setup`, which is rung-4 material sitting where the reader cannot
  avoid it. The `state` block is cut and the `setup` rewritten to say what is in scope. The contrast
  that block carried — obligations that fit, against the residual goal in the defeat section that
  does not — is stronger now that the reader assembles the first one.
- **A paragraph announcing two later sections** ("the last two sections of this unit are what its
  absence costs"), two paragraphs after the thesis had already been stated ("the rest of this unit
  is the setting up of that bet"). Cut to "That theorem does not exist yet."
- **A paragraph re-deriving its predecessor.** "That fixes the statement. Proving it means naming
  the final state and then cutting its heap, and the cut has exactly one candidate: the left piece
  has to satisfy `pure`, which forces it to be `Heap.empty`…" — the forcing argument is three blocks
  above. It now says what the proof term *owes* (state, derivation, cut; only the first is a
  decision) instead of re-proving why the cut is unique.
- **`auto-bound` was used as an unglossed technical term**, and it is introduced nowhere in
  Edition 2 (the three earlier occurrences are all in Edition-1 files, ERRATA §9). The paragraph now
  states the general rule — an identifier in a declaration's type that is bound nowhere gets a
  binder inserted, here `{σ : Store}`, in front of every other binder — and names it, so `m7-2`'s
  `variants` may keep the word.
- **Two `setup` fields that contradicted their own solutions.** `m7-2`'s said "Three lines after the
  `intro`, and no tactic other than `exact`" — there are four, and one of them is `subst`. `m7-1`'s
  listed "Two `refine`s, a `show` and a `simp`" and silently dropped the two-line opening. Both now
  match the `sol`.
- **An ambiguous ordinal.** `m7-1`'s `deep` said "the fourth state is the whole argument for `pure`"
  — fourth of the five steps, or fourth counting `start`? Now "the state after the second `refine`".
- **Third person, once** (`m7-2`'s `deep`: "a reader following the specification is asked…") →
  second person, per PEDAGOGY §3.
- **`σ'` used for something the goal calls `s'.store`**, in `m7-5`'s rung-1 hint.
- **`clearCell_spec`'s paragraph said Lean "sees the two as the same type"** — the things compared
  are assertions, and what is the same is the proposition each triple states. Reworded.

**Not changed, and why.** The explain-then-ask shape of `m7-2`/`m7-3` stands: §D objective 4
requires the page to say that each rule is one application of a named Unit 06 equation, and it
cannot say that after the exercise without wasting the layering point. The 56-block size stands
(ERRATA §18). Deviation 2 stands. The three `sketch` blocks stand — none displays a `sorry`, which
§E.1 reserves for Unit 24. A previous census line claiming "2 `cmp`, not 1 (the second is inside
`m7-3`'s `deep`)" was wrong: there is one `cmp` on the page, which is what §D budgets.
