# Unit 27 · `frame` · The frame rule
`site/content/30-frame.js` · 46 blocks (43 non-`ex`), 3 exercises, 88 KB rendered. 3 `trace` (all in
`deep`), 4 `state`, 4 `detail` (none before the first exercise), 1 each `steps` `tbl` `anat` `cmp`
`note key` `note warn`. **Lean fragment untouched** — all three exercises were already there,
including `free_with_frame`, which §D marks ⧗. No ledger row, no waiver, no `ledgerForward`.
**Reviewed and revised — see "What review changed". No Lean was edited at review**; every goal
state, every quoted compiler message and all six illustrations were re-derived from Lean.

## One job
Prove `hoare_frame`, and show that the length of a verification stops tracking the size of memory at
the point where the rule takes over.

## The hook I left (verbatim, final block; §D's wording)
> The rule is proved. There is one debt outstanding, issued on the first page: the statement we could
> not write down then, and can now.

Opens on `29-local-compose`'s hook in two words ("Eight lines.").

## Introduced
**Tactics, syntax, notation: none**, as §D specifies.
**Names now usable:** `hoare_frame`, `write_with_frame`, `free_with_frame`.
**Illustration-only, no row, collision-checked against all 39 fragments:** `HoareOn`, `LocalOn`,
`PreservesOn`, `frame_on`, `write_with_frame_by_hand`, `ne_from_precondition`,
`write_with_frame_any`, `tenCells`, `heapOnly_tenCells`, `write_with_ten_cell_frame`,
`frame_without_preserves_is_false`.
**Concepts:** the frame rule as a theorem · the cut in the *postcondition* as the proof's only
decision · locality as the exact hypothesis, not a checkable accident (`frame_on` — the same eight
lines over an arbitrary `E : State → State → Prop`) · `hd` passed and never read · three ways a
command loses `HeapLocal` against zero ways a language can lose `Preserves`.
**Rejected alternatives, all compiled:** the swapped cut (costs `disjoint_symm` and `union_comm`,
then dies on `⊢ Q r.store hR`) · the swapped orientation of `HeapLocal`'s conclusion, priced at two
lemmas **in the one proof where locality meets `∗`** (see warning 9) · the six-hole `refine`
(`⊢ Heap.disjoint ?refine_1 ?refine_2`) · `write_with_frame_by_hand` · `star_emp_right` ·
dropping `hpres`.

**Not explained** (earlier summaries own them): `Hoare`, `HeapLocal(Weak)`, `Preserves`, `HeapOnly`,
`Exec`, the six slots of `∗`, `⟨…⟩` flattening, `obtain`/`refine`/`subst`/`rw`, structure literals
in goal displays, `hoare_consequence`, the heap interface, metavariables and `?m.` displays.

## Exercises
`m8-5` **hoare_frame** [C 4, hard] — the theorem; six-step trace; the eight-line/five-move map.
`m8-6` **write_with_frame** [D 2] — two tactics, four names, no `Heap` in the proof.
`x54` **free_with_frame** [C 3] — the same lift plus `hoare_consequence` + `star_emp_left`.

## Warnings — compiled or grepped
1. **Unit 24 already displays seven of `m8-5`'s eight lines** (`27-locality.js` block 113, `sketch`,
   last hole a `sorry`, `hpres` not yet in the statement). `m8-5` is assembly plus one line.
2. **Downstream, grepped and re-checked at review:** `hoare_frame` **6 applications in 5
   declarations** — `31-aliasing-closed:22` (`separated_write_ok`), `32-symbolic`
   (`readAndFree_framed`, `copyCell_spec` ×2, `moveCell_spec`), `34-wp:95` (`wp_frame`). **Not one
   of them destructures `HeapLocal` or `∗`** — verified by reading all five. `write_with_frame`,
   `free_with_frame`: **zero** citations. Both `why`s say so.
3. **`HeapLocal` is never unfolded again** — one occurrence after this unit, `34-wp.lean:94`, as a
   hypothesis. Claimed in `orient.payoff`; keep it true.
4. **The `have base` in `write_with_frame` is NOT required**; the one-`exact` form compiles. In
   `m8-6`'s `variants`. Do not write that Lean needs it.
5. **`ledger.mjs` fires on later-unit internal names appearing in prose** — `x := alloc()` and
   `wp_frame` each cost an error. Describe the future, never name it.
6. **Two shipped files have swapped `phase` strings.** §D puts the Phase 5 boundary at
   `27-locality.js`; `26-small-footprint.js` carries Phase 5 and `27-locality.js` carries Phase 4.
   Nothing checks `phase`. Not mine to fix.
7. **`wasm-check.cjs <file>` compiles that file ALONE** — prepend `prelude.sh NN --incl` or every
   name is unknown. Its header does not say so.
8. **§D's ten-thousand-node linked list is unwritable**: `listRep` is Unit 32. Replaced by
   `write_with_frame_any` over an arbitrary `HeapOnly R` — strictly stronger — plus a ten-cell chain
   built with Unit 24's `heapOnly_star`, its first use anywhere.
9. **Unit 26 destructures `HeapLocal`'s conclusion too** (`heapLocal_seq`, `heapLocal_ite`,
   `heapLocal_loop_aux` each `obtain ⟨hdEnd, r, hr, hst, hhp⟩`), so "the only proof that opens
   `HeapLocal`" is **false**. What is true: those proofs consume `HeapLocal` *and produce it*, so a
   swapped orientation cancels on both sides and costs them nothing. The orientation is felt only
   where locality has to meet `∗`, which happens once in the whole course — in `hoare_frame`. Fixed
   at review; do not restate it the loose way.
10. **Dropping `hlocal` does NOT make the rule false.** Every `Cmd` is local, so the weakened
    statement is still true of this language; only the proof is lost. There is no `heapLocal_all` in
    the corpus, but truth does not need one. Only `hpres` has a witness against it
    (`frame_without_preserves_is_false`).

## Deviations
1. 43 non-`ex` blocks against ~26 (ERRATA §18) — yet 88 KB is the **smallest page in Module 6**
   (24: 84, 25: 97, 26: 125). At §18's summit floor deliberately: §D gives this unit no new Lean.
2. **§D says `write_with_frame` is five lines; the body is four** (two tactics). The page says four.
3. Warning 8. 4. Three `trace` against two, all in `deep`.
5. **`hoare_frame`'s proof is not on the main line** (ERRATA §27) — only the statement, the five
   moves in words, the six-slot `tbl` and the swapped cut. §D objective 1's mapping is in `m8-5`'s
   `solNote` and `walk`.
6. The retrospective is three end-of-page `detail`s; PEDAGOGY §11's lab format does not apply, its
   list being by *unit* number, and unit 30 is `33-swap`.

## Provenance
All 18 goal displays (74 lines) are `check.sh 30` output with `trace_state`, `snippet:L:C:` dropped.
**Re-derived from scratch at review** and diffed line by line against the page: **0 unmatched** —
the six `m8-5` trace states, the 20-line fold, the post-`subst` main-line goal, `⊢ Q r.store hR`
from the swapped cut, `⊢ Heap.disjoint ?refine_1 ?refine_2` from the six-hole `refine`, the two
`m8-6` states and the three `x54` states. Main-line displays are goal-line-only and the first
caption says so; the raw 20-line state is folded in `m8-5`'s `deep`.
**Every quoted compiler message was reproduced at review by breaking the real proof:** the
`And.intro hrex` mismatch from dropping `subst hu`; `preserves_of_heapOnly` without the leading `_`
(`of sort \`Prop\` … expected … \`Cmd\``); ``Variable name `hne` is not explicitly referenced``;
the frame-on-the-left `Type mismatch`; `hoare_frame`-alone in `x54`; `star_emp_right ?m.18`; and
`star_emp_left ?m.17` in the wrong slot. All match byte for byte.
**Also compiled at review, none of it shipped as text:** the `HeapLocalWeak` variant, stranded on
`⊢ s'.heap.disjoint hR`; the reversed-conclusion `hfRev` (**10 lines, 4 heap-lemma appeals**, as
`m8-5`'s `variants` claims); `hoare_consequence (star_comm _ _) framed (star_comm _ _)` as the
frame-on-the-left repair; `free_with_frame` over an arbitrary `HeapOnly R`.
The 6 `illustration`s compile as one file through `check.sh 30 --incl`.
Green at review: `node --check`; `lint.mjs 30-frame` **0/0**; `ledger.mjs 30-frame` **0/0**, `frags`
clean; `render-check.js` **0**; `verify.sh 30` (1631 lines, 235 decls); banned-phrase grep **0**.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no Lean. Fifteen fields rewritten, one block added.

**Facts that were wrong.**
- **"every use of the frame rule pays a `disjoint_symm` and a `union_comm`"** under the swapped
  orientation of `HeapLocal`'s conclusion. Uses of the frame rule never see `HeapLocal`'s internals;
  and Unit 26 opens the conclusion without paying anything (warning 9). Rewritten to the true and
  sharper claim, in the paragraph after the `tbl` and in `youWill` 3.
- **"Dropping either one leaves a rule with a witness against it"** (retrospective fold 1) — false
  for `hlocal` (warning 10), and it contradicted both `m8-5`'s `variants` and fold 3 on the same
  page. Replaced, and a new `p` added saying why no such witness can exist inside this language.
- **The heap-side counterexample was attributed to `HeapLocal`.** It refutes `HeapLocalAnyFrame` —
  locality with the premise deleted — and `HeapLocal` is *true* of `free`. `28-local-heap`'s review
  fixed this exact error in its own text; it had migrated here.
- **"Unit 26 proved it for all eight constructors of `Cmd`"** (`anat`) — Units 24 to 26 did, and the
  retrospective fold three sections down said so.
- **`m8-5`'s `why`: "the last one in it that is about the semantics rather than about a program"** —
  false. `preserves_of_storeStable`, `exec_seq_assoc`, `classical_conjunction_rule_is_false`,
  `wp_sound`, `wp_weakest` and `wp_frame` all come later. Clause deleted.
- **`youWill` 5: "no cell contents … appear"** — `old`, `new` and `w` appear throughout
  `write_with_frame`. What is true, and what the `dod` already said, is that no *heap* does.
- **"the same heap equation `heapLocal_write` is built out of"** — `heapLocal_write` proves that
  equation inline rather than citing `write_union_no_disjointness`; `heapLocal_write_short` is the
  one that cites it.
- **"The two proofs are not far apart in length"** — seven tactics against two.
- **Two intra-page pointers off by a section/two blocks** (ERRATA §27's tell): `write_with_frame_any`
  is one section up from `x54`, not two; the disequality paragraph is four blocks below `m8-6`, not
  two — reworded so nothing is counted.
- **The first `state` caption sourced its omitted context to "`m8-5`'s trace, in full"**; the trace
  trims and the fold shows the state *one tactic earlier*, at twenty lines. Caption now says that.

**Prose.** One paragraph-announcing-a-paragraph cut ("Here they are with what fills each, and where
it came from" — the `tbl` caption says it). The `steps` title "The frame rule, with no Lean in it"
was over a block full of `<code>` spans; now "The five moves". `simply`, introduced and then caught
by the banned grep, removed. "The second hypothesis is cheap and the first one is not" counted the
hypotheses in the opposite order from the `anat`, the `tbl` and Unit 24 — the paragraph now names
them instead.
The swapped-cut `state` caption said "the third goal", which is only right if all four star
obligations are holes; the prose two lines above supplies two of them. Now names the slot.

## Weakest part, honestly
All three exercises are assembly; nothing asks the reader to *state* anything and there is no [G].
Objective 6 is argued in two paragraphs and measured by nothing, because no counterexample command
exists inside `Cmd` — the address-choosing command is the one claim here a reader cannot run.
`ne_from_precondition` is `two_cells_distinct` renamed, which makes objective 5 cheaply. And the
main line never displays the eight lines of `hoare_frame`: "Read the eight lines again" at the top
of *What the proof does not contain* is addressed to a reader who has done `m8-5` or opened its
solution, and `frame_on`'s fold is the only place on the page where all eight are visible without
pressing a button.
