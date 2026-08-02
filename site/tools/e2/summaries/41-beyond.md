# Unit 38 · `beyond` · Allocation, generalisation, and what is undone
`site/content/41-beyond.js` · 68 blocks (66 non-`ex`), 2 exercises, 71 KB source / 100 KB rendered,
~2110 words of main-line `p`. 17 `code` (13 `illustration`, 2 `verified`, **2 `sketch`**), 2 `detail`
(one before the first exercise), 2 `trace`, 1 `state`, 3 `txt`, 4 `note`, 1 each `cmp` `tbl` `dl`
`ul` `dod`. **Lean fragment untouched, by the author and by review.** One `ledgerAllow` (warning 4);
**two `ledger.json` rows added at review** (warning 8). Last unit.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean fragment was edited at
review**, and no exercise `id`, `name`, `goal`, `sol`, or `trace`/`state` `src` was touched.*

## One job
Break locality with an allocator and price the repairs; **prove** the generalisation to arbitrary
PCMs; state the address-expression limitation with the change that removes it.

## The hook I left
**None, by §D.** Final block, verbatim tail: *"…**§ Reference** is the notation table with how to
type each symbol, the theorem index, and the five rules of proof discipline. **There is no next unit
to hand anything to.**"* Opens on `40-variant`'s hook in three words ("Two questions, then").

## Introduced
**Tactics, syntax, notation: none.** **Names now usable:** `pcmStar`, `pcmStar_comm`,
`pcmStar_unit_left`. **Illustration-only, in no fragment, collision-checked (18):**
`no_semantics_survives_framing`, `no_local_allocator`, `framed_fresh_postcondition_holds`,
`fullHeap*`, `pcmStar_mono` (added at review), `countPCM`, `clashPCM`, `pcmStar_not_assoc`,
`pcmStar_assoc_of_distrib`, `heapPCM_distrib`, `split_is_unique`, `agreePCM` (re-declared from
Unit 10, as its handover invited) + `agree_split_is_not_unique`, `ACmd`/`AExec`/`AHoare`/`ahoare_load`.
**Concepts:** locality is losable · allocation · generalisation to arbitrary PCMs · ghost state and
concurrency, with the PCM proof as the licence · precision as the substitute for cancellation ·
proof irrelevance, named and explained in one clause inside the finite-heap `detail` (warning 8).

## Exercises
`x74` **pcmStar_comm** [C 3] — commutativity of `∗` over an arbitrary PCM; `K.op_comm` as a
conditional rewrite. `x75` **pcmStar_unit_left, and a PCM of your own** [**G** 2] — the unit law,
plus a second `PCM` the reader designs; `countPCM` and `exclPCM` ship in `deep` as *two* answers,
and the page says the editor does not check part two.

## Warnings — every one compiled
1. **§D understates the finding.** Associativity of `pcmStar` is **not** a consequence of the five
   laws: `clashPCM` (`Nat`, `+`, `0`, the pair (2,2) invalid) refutes it. The missing axiom is
   validity distributing over `op` — Unit 10's `disjoint_union_left`/`_right`, which that unit's
   summary says are **not** PCM fields. `pcmStar_assoc_of_distrib` + `heapPCM_distrib` restore it.
   This is why §D asked only for commutativity and the unit law.
2. **`example (P Q : Assertion) (σ : Store) : pcmStar heapPCM (P σ) (Q σ) = (P ∗ Q) σ := rfl`
   compiles.** The general definition instantiated at heaps is Unit 14's, definitionally.
3. **The allocation refutation needs no `alloc` and no semantics.** `no_semantics_survives_framing`
   quantifies over an arbitrary `E : State → State → Prop`; `no_local_allocator` is the four-line
   in-language corollary through `hoare_frame`. §D's `sketch` covers only the *semantics*.
4. **`ledgerAllow` on seven names**, with the reason in a comment in the file: six `K.*` field
   projections of a bound `K : PCM M` — Unit 10's summary predicted these and said "rename or
   waive", and the fragment cannot be renamed — plus `AExec.load`, a constructor of an
   `illustration` inductive. Without the waiver, 0 errors and 7 coverage warnings.
5. **Both `sketch`es were fed to Lean and fail exactly as their captions say**, before and after
   review (the `hoare_alloc` postcondition changed shape at review; the four errors did not).
6. `subst he` in `x75` works on `he : (fun x => x = K.unit) m₁`, an equation under an unreduced
   beta-redex; `rw [hm, he, K.unit_left]` and the `subst hm` route also compile, and `x74`'s equation
   slot closes in **both** orientations of `K.op_comm`. All in `variants`.
7. **`run_complete` (Unit 21) dies under Project 1 too**, and §D does not list it: `run` is a
   function and must pick one address, and the nondeterministic rule admits every free one. Project
   1's revisit list now names it alongside `exec_deterministic` and `partial_of_total`.
8. **Two `ledger.json` rows added at review**, both `kind: "library"`, both appended in the
   reviewer-row style already used by `03-compute`'s reviewer: **`Nat.add_comm` booked at
   `18-star-assoc`** (its true first use — `sqSum_comm`'s `simp` bracket — where it had no row) and
   **`Nat.add_assoc` booked at `41-beyond`** (first and only use: the `op_assoc` field of `countPCM`
   and `clashPCM`, and named at `x75` hint 3, which PEDAGOGY §8 forbids for an unbooked lemma).
   `ledger.mjs` over the whole course is 0/0 after the edit. **`proof irrelevance` and `structure
   extensionality`** appear on no ledger row and in no earlier summary; rather than book two words
   used once inside a closed aside, the aside now delivers the content in plain terms ("Lean treats
   any two proofs of the same proposition as the same term") and names neither.
9. **Weakest part.** Both exercises are short and rung 4 hands over the first line; `x75`'s design
   half is unchecked by the editor and the page says so. Objective 3 (why the existential is
   *required*) is argued in prose plus one compiled witness, not measured.

## Not explained (earlier summaries own them)
`hoare_frame`, `HeapLocal`, `Preserves`, `HeapOnly` · `∗`'s slots and `intro` pattern · `⟨…⟩`
flattening · `subst`/`rw`/`refine`/`obtain`/`▸` · `PCM`, `heapPCM`, `union_cancel_left` ·
`pure` versus `fact` (Unit 17) · the `x := [l]` / `[l] := e` surface notation (Unit 18).

## Deviations
1. **66 non-`ex` blocks against §D's ~30** (ERRATA §18, which rules the budgets shape and not a cap);
   prose *under* budget at ~2110 words against ~5 screens. The excess is the 13 compiled
   illustrations.
2. Warning 1 sharpens §D objective 4 rather than departing from it.
3. §D's Project 1 revisit list is extended by `run_complete` (warning 7), and its Project 2 list is
   corrected: the affected locality proofs are `heapLocal_load` (Unit 24) and both of Unit 25's, not
   "the three of Unit 24 and the compositional ones of Unit 26" — Unit 26's take locality of the
   parts as hypotheses and name no constructor, so they move to the **What must not** list.

## Provenance
Both `trace`s and the one `state` are `check.sh 41 <snippet> --incl` output byte for byte,
`trace_state` for mid-proof states, `snippet:L:C:` dropped (said in the first caption). `x74`'s
trace opens the solution's `by` slot as a `refine … ?_` hole, and says so. Every quoted message came
from breaking a real proof: the unswapped `hm`, the reordered `hp`/`hq`, `K.valid_comm hv` without
its underscores, `rw [K.op_comm]` without its premise, `rw [K.op_comm _ _ hv, hm]` in the wrong
order, `exact hp` too early, `unit_left := fun _ => rfl`, the five-name `intro`, both sketches.

**Re-derived from scratch at review, all identical to the page:** both traces (7 `trace_state`
points), the one `state`, and eight falsifiable `pitfall`/`variants` claims — including the
`?m.20 = ?m.20` metavariable number and the `case a` tag. The 13 illustrations compile as one file
against prelude-41 `--incl`, and **that file plus the whole prelude goes through `wasm-check.cjs`
clean — "the reader's Lean accepts all of it"**. Green at review: `node --check`; `lint.mjs`
**0/0** (68 blocks, 2 ex); `ledger.mjs` for this unit **0/0** and for the whole course **0/0**,
frags clean, sweep 3 (pre-existing); `render-check.js` **0 problems**; `verify.sh 41` (2327 lines,
319 declarations, fragment unmodified); banned-phrase grep **0**.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no `trace`/`state` `src`, no fragment edit. One block
added; two `ledger.json` rows added; twenty-one fields rewritten.

**Six false or self-undercutting claims.**
- **"something the course has claimed since Unit 24 and never demonstrated."** Unit 24 *did*
  demonstrate it, at `content/27-locality.js:63`, with `x := allocated?(l)`. The opening now says
  what is actually new here: Unit 24 argued it in words with a command nobody wants; this page
  proves it in Lean, with a command every language has, and what breaks is the frame rule itself
  rather than a clause of a definition.
- **"No theorem after Unit 18 inspects *how* an address was obtained"**, written three clauses
  before "what does change is the primitive rules of Unit 23 and the locality proofs of Units 24 to
  26". The paragraph now splits the downstream theorems in two — six stated per constructor, which
  change; everything stated over an arbitrary command, which does not — and names `heapLocal_seq`
  as the case that looks per-constructor and is not.
- **"Unit 33 … closed on a program that cannot be written."** `36-lseg` closed on the wand. It is
  Unit 37 that says the cursor-advancing body cannot be written down, at `40-variant.js:392`.
  Re-attributed.
- **The trilemma was not one.** "There is no way to keep all of: a deterministic allocator, a
  specification naming the location, and the frame rule. Three things can go" — the third repair
  (finite heaps) gives up none of the three; it is what the *second* repair needs before its total
  triple is provable at all. The lead now chains the three: restrict the rule, or stop naming the
  address, and once you stop naming it the model must guarantee there is an address to take.
- **"invalidates every inversion proof in Modules 5 to 9."** Module 8 (Units 32–34) contains none,
  and Unit 19 — Module 4 — contains the first. Replaced by the count: every `cases hex` from Unit 19
  onwards, twenty-three of them, grepped.
- **`dod`: "say why no theorem after Unit 18 has to be reproved,"** contradicted by the page's own
  ~40-line estimate. Now: name the six it obliges you to redo, and say why nothing stated over an
  arbitrary command is among them. `orient.youWill` item 6 repaired the same way.

**Three notation collisions.** The `dl`'s allocation spec was written `{∃ l, (x holds l) ∗ l ↦ 0}`,
in a notation this course does not have; it is now `{∃ l, x = l ∗ l ↦ 0}`, which is exactly how Unit
23's `txt` writes the load rule. The `sketch`'s `hoare_alloc` postcondition was
`aAnd (fact …) (l ↦ 0)` against that `∗`; it is now `pure (fun σ => σ x = l) ∗ (l ↦ 0)`, the shape
of the real `hoare_load`, re-fed to Lean (same four errors). And "a **pure** side condition", twice,
of a `fact` conjunct — `pure` is `aAnd (fact φ) emp` since Unit 17 and the two are not
interchangeable, which is Unit 17's whole point. Also `HeapLocal (.allocAt l)`, a third spelling of
a command the page calls `alloc-at` and the sketch calls `alloc`.

**One unbacked row in the inventory table.** "monotonicity and congruence · transfers ·
`star_mono` never touches a heap" was the only *transfers* row not backed by compiled Lean, on a
page whose thesis is that this is proved rather than asserted. `pcmStar_mono` is now a five-line
compiled illustration between `x75` and the failures, and the row cites it.

**One re-explanation and one announcement.** "`HeapLocal c` says: run `c` on a smaller heap, then
on that heap unioned with a frame, …" restates a definition twenty-three units after it was given;
the paragraph now names only the clause that does the work. "The question this section settles is
which laws survive…" restated the section heading — PEDAGOGY §4's paragraph-announcing-a-paragraph.

**Two duplications.** `x74`'s `expl` gave the `disjoint_symm` → `K.valid_comm`, `union_comm` →
`K.op_comm` comparison that the `cmp` block and the paragraph under it exist to give, three blocks
later; the `expl` now says what the panel is for and leaves the comparison to the main line.
`x75`'s `expl` said the fourth line was forced "because Lean prints the unit assertion applied
rather than reduced", while its own `variants` gives the compiled three-line route without it; it
now says the `subst` is a choice.

**Six counts and attributions.** "four characters of syntax" against the same page's — and Unit
37's — "one-line change" (now one line, with the `txt` caption saying which of the three lines
unblocks the walk and why the other two exist); "the same sentence with three *words* changed" of
three renamings; "the bodies differ in two names" of two lemma citations *and* a binder; "a
two-line refutation" in the ideas list, of a four-line one that never mentions the command;
"every proof in Module 1" in a `detail` whose body says Modules 1 and 2; "Which is the point of the
exercise" after a table summarising two.

**Checked and re-derived, then left alone.** Both `sol`s and `goal`s against
`lean/e2/41-beyond.lean`; both traces and the `state`; the two `sketch`es' error lists; the
`agreePCM` fold; the `cmp`'s quotation of `star_comm`, diffed against
`17-star-algebra.lean:24–26`; every unit citation in the prose (Units 07, 08, 10, 13, 14, 15, 16,
18, 20, 21, 23, 24, 25, 26, 29, 33, 35, 37) against the file→unit map; the `-∗` table row, against
`wand_curry`/`wand_uncurry`, which do cite `union_assoc` and both bridges; the `dod`; the `ul` of
ideas worth keeping, whose Unit 07/13/23 exactness thread is PEDAGOGY §2 word for word.

## Weakest part, honestly
`x74` and `x75` are two-line and four-line proofs, and both hint ladders end by handing over the
first line, so the measured work is small for a unit that carries the course's last big claim. What
makes them worth their place is not their length but their statement: `x74` is the sentence
"commutativity of `∗` is a fact about the algebra" written so that Lean can refuse it. The design
half of `x75` — build a PCM of your own — is the one genuinely open task on the page, and it is the
one the editor cannot check.
