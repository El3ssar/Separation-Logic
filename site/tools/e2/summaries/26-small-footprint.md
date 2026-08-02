# Unit 23 · `small-footprint` · Rules that mention only what they touch
`site/content/26-small-footprint.js` · 63 blocks (57 non-`ex`), 6 exercises, 75 KB, 6 `trace`
(all in `deep`), 4 `state`, 8 `code illustration` (6 top-level, 2 in `deep`), 3 `code sketch`,
1 `detail`, 1 `defn`, 1 `cmp`, 2 `note kind:key`, 1 `txt`, 1 `ol`, 1 `dod`.
**Fragment extended by one theorem (`x48`); two `/- ex … -/` markers moved.**
*Reviewed and revised — see “What review changed” at the bottom. **No Lean fragment was edited at
review**; two page `illustration`s were rewritten and one added, all recompiled.*

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
so Unit 07's loose reading returns through the assertion language · the auto-bound implicit, and why
the write postcondition is eta-expanded · the layering point: `hoare_write`/`hoare_free` each end in
one Unit 06 equation and contain no `funext`.
**Rejected alternatives, all compiled:** `fact φ ∗ (l ↦ v)` (provable, strictly weaker;
`¬ (fact ⊤ ∗ (0 ↦ 4) ⊢ (0 ↦ 4))` measures the loss) · `aAnd (fact φ) (l ↦ v)` (equivalent, shorter,
rejected on *shape*) · the big-precondition write rule (prose) · `l ↦ (e.eval σ)` unbound · 
`hoare_consequence` for `clearCell_spec` · the loose `↦` in the free rule (`x16` + `x18`).

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
3. **`theorem … (l ↦ (e.eval σ))` COMPILES**, `σ` auto-bound as `{σ : Store}` in front, and the
   statement is false. The bodyless declaration's `unsolved goals` report prints `σ : Store` as its
   first context line — the cleanest auto-binding exhibit I found.
4. **Downstream citations, grepped:** `hoare_load` 2 (both `32-symbolic`); `hoare_write` 2
   (`30-frame`, `31-aliasing-closed` — **`32-symbolic` does not cite it**, it proves
   `hoare_write_val`); `hoare_free` 3 (`30-frame` 1, `32-symbolic` 2); `readAndFree` 1. `clearCell`,
   `clearCell_spec`, `readAndFree_spec`, `writeTwice_spec`: **zero.** Every `why` states these.
5. **`32-symbolic`'s `readAndFree_framed` is the answer to `m7-5`** and is already written.
   `m7-5`'s `solNote` promises the reader it re-proves this program from `hoare_seq`, consequence
   twice, and one rule they do not have. **Author of `32-symbolic`: keep that true.**
6. **`hoare_free`'s pitfall is the state, not the lemma** — naming the final heap `Heap.empty`
   fails at `Exec.free`, whose conclusion fixes `Heap.erase s.heap l`.

## Deviations
1. 57 non-`ex` blocks against ~30 (ERRATA §18); below `25-hoare` (65) and `22-exec` (65).
2. **§D's "`m7-4` opens the unit on a win" cannot be met** — `clearCell_spec` *is* `hoare_write`
   specialised, so it cannot precede it. It sits fourth, where §D's own table puts it.
3. 2 `cmp`, not 1 (the second is inside `m7-3`'s `deep`).
4. §D objective 3 asks that `pure` "forces the cut"; the page proves first that `fact` would *not*,
   with a compiled non-entailment, then reads `Heap.empty` off `m7-1`'s fourth trace state.

## Provenance and checks
Every `state`/`trace` step is `check.sh 26 <snippet>` output byte for byte (`--incl` where needed),
`trace_state` for mid-proof states, `snippet:L:C:` dropped. The three quoted errors came from
breaking real proofs, verbatim but for `…` elisions. Every `pitfall`/`variants` claim compiled
separately, including `ptsAtLeast` against the *write* rule (witness `twoCells` at 4, disagreement
at 9) and the reversed `free(l) ;; x := [l]`. Green: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` unit and edition-wide **0/0**,
`--fragments` clean, no waivers, `--sweep` 3 (all pre-existing); `render-check.js` **0**;
`verify.sh 26` and bare `verify.sh`; `--prove` **94/94**; `wasm-check.cjs` over prelude-26 and over
that plus all 8 illustrations — clean, which is what clears `clearCell_spec` and `writeTwice_spec`,
both of which unfold a plain `def` in a `theorem`'s stated type (ERRATA §28); banned-phrase grep 0.

## Weakest part, honestly
Four of six exercises are two or three lines and none is `hard`; the difficulty sits entirely in
`m7-1`'s six-slot tuple and `m7-5`'s refusal to compose. Nothing asks the reader to *reject* a
proposed rule for mentioning too much memory, so the `defn` is unmeasured. And `m7-5`'s felt need
depends on the reader trying `hoare_seq` first — a reader who goes straight to the solution feels
nothing.
