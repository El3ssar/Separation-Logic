# Unit 17 · `pure` · Propositions inside a star, and the toolkit
`site/content/19-pure.js` · 61 blocks (58 non-`ex`), 3 exercises, ~2370 words of prose in `p`/`note`/
`dod` (≈3.9 screens), 2 main-line `trace` + 3 in `deep`, 5 `state` (2 main line, 1 in the `detail`,
2 in `deep`), 1 `detail` (the one allowed before the first exercise), 3 `txt`, 1 `tbl`, 1 `cmp`,
2 `note`, 1 `dod`. **Lean fragment untouched.**
*Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review.*

## One job
Answer Unit 16's question with `pure`, prove non-aliasing at assertion level, and hand over the
normalisation library plus the technique it is used with — composition, not destructuring.

## The hook I left (verbatim, final block; word for word from §D)
> The algebra is complete and every law it has is proved. It cannot state the frame rule, because
> the frame rule says a *command* leaves the frame alone, and there are no commands. The next module
> builds them, and mentions `∗` exactly zero times.

Opens on `18-star-assoc`'s hook in seven words ("Attach the proposition the obvious way"), then
refutes that attachment.

## Introduced
**Tactics: none** — everything used is ledgered ≤ 15.

**Display:** `_root_.pure` in every goal state from now on (Lean's core has a `pure`; ours wins by
type and prints with its path); `#check @pure` → *Ambiguous term*, quoted in the `detail`.

**Names now usable:** `pure`, `two_cells_distinct`, `star_swap_middle`, `star_rotate_left`,
`star_rotate_right`, `star_pure_left`, `star_pure_right`, `star_or_right`, `star_exists_right`.
Illustration-only, collision-checked: `factStar_not_and`, `factStar_from_and`, `two_cells_not_pure`,
`two_cells_and_distinct`, `normalise_demo`, `pureRaw`, `pureRaw_agrees`.

**Concepts:** the two embeddings and **the rule behind them** — *an embedding must match the
resource discipline of the connective it sits under* · `fact φ ∗ P` strictly weaker than
`aAnd (fact φ) P`, refuted at one cell, which is `no_star_weakening` from the other end ·
**ownership implies non-aliasing**, and why the conclusion is `fact` · **proof by composition**,
motivated by the `refine entails_trans ?_ ?_` failure whose context is `⊢ Assertion` ·
normalisation, with a `tbl` of all eighteen shape-to-shape moves · one cut versus many cuts, which
is why `∨` and `∃` cross a star in both directions and `∀` does not.

**Rejected alternatives, all compiled:** `fact` under `∗`; `pureRaw` (identity proves both
directions — the cost is vocabulary, not truth); `pure` as `m4-7`'s conclusion; `starNoDisj`
(non-aliasing dies); `ptsAtLeast` (it **survives**, in five lines); `star_mono_right` for `_left`;
starting the chain with `star_assoc_left`; commutativity alone; the semantic `star_swap_middle`
(7 lines, 4 heaps named); `obtain` for `rcases` on `∨`; the witness in front of the outgoing tuple;
`aAnd` for `aOr`.

## Exercises
- `m4-7` **two_cells_distinct** [C 2] — the precondition already contains its own non-aliasing
  hypothesis; the two `subst`s are the proof.
- `m4-8` **star_pure_left/right, star_swap_middle, star_rotate_left/right** [C 3] — composition.
- `x38` **star_or_right / star_exists_right** [C 2] — give the cut back with one slot rewrapped.

## Not explained (previous summaries say it is known)
Modules 0–2 and Units 12–16, including the *cause* of the ∀/∃ asymmetry (Unit 15 owns it; this page
uses it as a contrast and does not re-derive it).

## Deviations from COURSE-PLAN.md
1. 58 non-`ex` blocks against ~26, 3.9 screens against ~3 (ERRATA §18); in line with
   `18-star-assoc` (50) and `17-star-algebra` (53).
2. §D objective 2 asks for `pure φ ∗ P ⊣⊢ aAnd (fact φ) P`. **No such corpus theorem exists** — the
   fragment has the two entailments separately. The page says the equivalence is two theorems.
3. §D wants `star_swap_middle` walked from the outside in. The main line walks the *design* and
   stops before the term, which is the exercise; the outside-in walk is `m4-8`'s `walk` and `deep`.
4. `ledgerForward: ['write_with_frame', 'node_cells_distinct']`, both in `m4-7`'s `why`, in a
   sentence saying "two later theorems you cannot read yet" (ERRATA §10).

## Warnings to successors
- **Downstream citations, re-grepped at review over `22-*`…`41-*` with word boundaries.**
  `star_swap_middle`, `star_rotate_left/right`, `star_pure_left/right`, `star_or_right`,
  `star_exists_right`: **ZERO, all seven.** `two_cells_distinct`: **1** — `35-listrep.lean:32–34`,
  where `node_cells_distinct` *is* `two_cells_distinct p (p+1) x next`, one line and no proof of its
  own. `pure`: **20 occurrences in 6 fragments** (`26`, `27`, `32`, `33`, `35`, `36`), including
  inside `lseg`'s definition — the page says "six later fragments" and gives no count.
  `entails_trans` after this unit: **11 occurrences in 5 proofs** (`36-lseg` 7 across
  `lseg_append` and `lseg_listRep`, `32-symbolic` 2 in `copyCell_spec`, `37-wand` 1 in
  `star_wand_adjunction` and 1 in `hole_elim`). **A pre-review draft called these "eleven chains" in
  three places; they are eleven links in five chains.** The page states all of it, zeros included.
  Do not upgrade any of the seven into a promise.
- **`refine entails_trans ?_ ?_` fails.** The obvious cure, `(Q := …)`, is a **named argument**,
  ledgered at `22-exec` — unavailable here. The page supplies the first component instead.
- **`36-lseg`'s list theorems are `refine entails_trans … ?_` chains in their `cons` branches only**
  (lines 33–38 and 56–61); the `nil` branches name heaps. The page says "the inductive step of each
  of Unit 33's two list theorems" for exactly that reason — `18-star-assoc`'s summary flagged it.
- **Slot numbering, again.** The star's slots are `⟨h₁, h₂, hd, hu, hp, hq⟩`: disjointness is the
  **third**, the union equation the **fourth**. `star_pure_left` underscores the third and
  `two_cells_distinct` underscores the fourth, and the page turns on the difference. One trace step
  said "slot four" of `star_pure_left`'s underscore; fixed at review. `17-star-algebra` had to fix
  the same error twice. Count from the corpus line, not from memory.
- **"elaborator" is not a word this course has introduced.** `18-star-assoc`'s summary says it was
  removed there; it survives once in `18-star-assoc.js:351` and appeared **five times** in this file
  before review. All five are gone. If you want the word, book a ledger row.
- **`star_same_loc_absurd` and `two_cells_distinct` are the same three lines** but for a trailing
  ` rfl`, as `16-star`'s summary asked; `m4-7`'s `solNote` says so.
- **`obtain` on a disjunction splits it silently**, leaving an unbulleted `case inr` reported at the
  `theorem` keyword.
- **Disjointness is the entire content of `two_cells_distinct`, but it is not the only such theorem
  in Module 3** — `star_same_loc_absurd` and `no_star_duplication` are the others. A pre-review draft
  called this "the one place in Module 3"; corrected.
- **Weakest part:** `star_pure_left` is worked in full in a main-line trace and is one fifth of
  `m4-8`, so that fifth is transcription; `x38`'s rung 4 gives both first lines.

## Provenance and checks
Every `state`/`trace` step is `check.sh 19 <snippet>` output (`--incl` where needed), byte for byte,
`trace_state` for mid-proof states, `snippet:L:C:` dropped. **All sixteen states were regenerated
from scratch at review** — `star_pure_left` ×4, `two_cells_distinct` ×3, the staged
`star_swap_middle` ×3, `refine entails_trans ?_ ?_`, `star_pure_right`, `star_or_right`'s two-goal
dump, `star_exists_right`, the `∀` converse, and `#check @pure` — and diffed against the page:
**identical byte for byte**. The 6 `illustration`s recompiled as one file under `check.sh 19 --incl`
(silent); the 6 `sketch`es are honest; every quoted error message was reproduced by breaking a real
proof (`singleton_disjoint_iff` before the `subst`s; `star_mono_right` for `_left`;
`star_assoc_left` opening the chain — **one error, not three**, as the page says; `obtain` on the
disjunction; the witness in front of the outgoing tuple, **two** errors; `hp` handed back bare).
Every `variants` claim was compiled separately, including the two `aAnd`-for-`aOr` directions, the
seven-line semantic `star_swap_middle` (four heaps named, a fifth built, `disjoint_union_right` ×2,
`disjoint_symm`, `union_assoc` ×2, `union_comm` — six applications of four lemmas, exactly as the
page claims), the `ptsAtLeast` survival, and `pure φ ⊢ fact φ` / `pure φ ⊢ emp` as `and_left`/
`and_right` terms. Lemma signatures (`star_mono_left`/`_right`, `singleton_disjoint_iff`,
`star_forall_left`) came from the fragments.

All green: `node --check`; `lint.mjs 19-pure` **0/0** (61 blocks); `ledger.mjs 19-pure` 0/0, sweep
and `frags` clean; `render-check.js` **0 problems**; `verify.sh 19` (898 lines, 164 declarations);
banned-phrase grep clean.

## What review changed
**No Lean was edited, and no exercise `id`, `name`, `goal`, `sol` or hint rung was touched.**
Everything below is prose.

- **Three counting errors about the corpus, all in forward-looking claims.** `orient.payoff`,
  `m4-8`'s `why` and the normalisation paragraph each said "eleven chains" / "eleven later proofs" of
  `entails_trans`. There are eleven *occurrences*, in five proofs. All three now say so. `m4-8`'s
  `why` also claimed Unit 33's two list theorems *are* such chains; only their inductive steps are,
  and `18-star-assoc`'s summary had warned about exactly this. The lemma list gained `star_comm`,
  which two of the five proofs use.
- **A slot number wrong in a main-line trace.** `star_pure_left`'s `intro` underscores slot three
  (disjointness); the step said slot four. `m4-7`'s rung-4 hint, which says the underscore *moves* to
  slot four, depends on the first one being right.
- **"Three shapes between the start and the finish"**, immediately above a `txt` whose caption reads
  "Four shapes, three moves". Two shapes lie between them.
- **The stated reason `no_star_weakening` holds was backwards** — "`⊢` would have to invent the
  resources back". Weakening fails because the forgotten conjunct's cells are *still in the heap* and
  an exact assertion refuses them. `16-star`'s summary is explicit that this is the one theorem there
  that turns on exactness; the page now gives that reason.
- **"`aAnd` … holds neither conjunct to anything about the heap"** — false of the second conjunct.
  What is true, and what the argument needs, is that the two conjuncts get the *same* heap, so what
  one claims costs the other nothing.
- **"An embedding you can always introduce and never eliminate"** — `fact φ ∗ P ⊢ fact φ` is
  provable, so "never eliminate" is false. Replaced by the checkable statement: `fact φ ∗ P` is
  strictly weaker than `aAnd (fact φ) P`, and what is lost is which heap `P` holds at.
- **"the remaining four slots are the facts you were handed"** in `star_pure_right` — two of the four
  are the empty-heap laws. Split.
- **"This is the one place in Module 3 where the disjointness conjunct is … the entire content"** —
  `star_same_loc_absurd` and `no_star_duplication` are two more. Named instead of claimed unique.
- **"Six lines instead of three"** for the `ptsAtLeast` version of `m4-7`. It compiles in five;
  the field now says five.
- **"the arity of the quantifier … decides whether it goes through"** (`x38`'s `why`) — `∀` and `∃`
  have the same arity, and `∨` is not a quantifier. The deciding quantity is how many cuts the
  premise hands you, which is what the paragraph three blocks earlier actually argues.
- **`x38`'s `state` caption enumerated eight context lines and listed six of them**, omitting the
  store and the heap. Rewritten to count what Lean prints.
- **"elaborator", five times.** Not a word the course has introduced, and `18-star-assoc`'s summary
  asked successors not to use it. Each replaced by what Lean is actually doing.
- **"one-line terms"** for `m4-8`'s first three, one of which is three lines. Now "terms with no
  tactic anywhere in them", which is the property the exercise turns on.
- **Two announcing sentences cut** — "The two embeddings now pair off", directly above the `txt`
  that pairs them, and "Watch that happen", directly above the trace. **One sentence restating its
  predecessor cut**: the `∀` paragraph ended on "The quantifier that has exactly one instance is the
  one that crosses a star freely", which is the previous paragraph's last sentence again, and is
  loose about `∨` besides.
- **A dangling pronoun in the first six words of the unit** — "Attach it the obvious way", whose
  antecedent lives only in the previous unit's closing block. Now "Attach the proposition".
- Minor: the `tbl` caption said "The complete algebra of `∗`" over a table whose last row is a
  theorem that does not exist; the opening `code` caption's "which is the whole point of it" now
  points at the underscore in the definition; one "never in question at any point".

**Not changed, and why.** The 61-block size stands (ERRATA §18, and every Module-3 unit is between
52 and 72). All three exercises keep their §D-prescribed ids, names, kinds and difficulties, and
their `goal`/`sol` text is the fragment verbatim; `m4-8`'s `goal` keeps the house convention of
`sorry` on all but the last statement. Deviation 2 stands: adding a `star_pure_iff` to the fragment
is Lean §D did not ask for, and the page states the equivalence in prose. The `∀` digression keeps
its `state` block: §D's objective 5 asks the reader to say why the converse fails for `∀`, and the
block is what makes "nowhere to go" checkable rather than asserted.
