# Unit 10 · `pcm` · The partial commutative monoid
`site/content/12-pcm.js` · 63 blocks (58 non-`ex`), 5 exercises, ~2550 words of main-line prose
(≈4.2 screens), 9 traces, 3 top-level `detail` (none before the first exercise). Lean fragment
**untouched**.
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Prove the two remaining laws and the two disjointness bridges, show that associativity needs no
hypothesis while commutativity is refuted by two one-cell heaps, and turn "heaps form a partial
commutative monoid" into a `structure` the reader builds and a term they can `#check`.

## The hook I left (verbatim, final block)
> You have an algebra of resources. What you do not have is a single fact about the relation that
> says *this heap splits into these two* — and its associativity is none of the laws above. It is
> the first statement whose proof has to manufacture hypotheses nobody handed you.

Opens on `11-union`'s hook in its first two blocks.

## Introduced
**Tactics:** `refine` with `?_` holes, `fun l => ?_` inside one, `case refine_N` numbering, and
`?_` versus `_` with the real `don't know how to synthesize placeholder` message (one clause links
back to §`goalstate`'s metavariables, as its summary asked).

**Syntax owned here:** `structure … where` with `Prop` fields *as a proof obligation per field*
(the keyword itself was met at `07-heap`, ERRATA §2); the `where` instance syntax; field projection
`k.op`, `k.op_comm` on a bound structure variable.

**Names now usable:** `union_assoc`, `union_comm`, `disjoint_union_left`, `disjoint_union_right`,
`PCM`, `heapPCM`, `union_cancel_left`. Illustration-only: `agreePCM`.

**Concepts:** monoid — with `(Nat,+,0)`, `(Nat,×,1)` and functions under composition, the third
non-commutative so the adjective earns its keep · commutative monoid · **partial commutative
monoid** (`defn` card, five laws, exactly one qualified) · right neutrality as a *derived* law,
proved on the page for an arbitrary `PCM` · **cancellativity**, with a compiled PCM in which it
fails · derive the mirror image rather than reprove it.

**Rejected alternatives, all compiled:** the textbook PCM qualifying *every* law · `constructor` +
two `intro l` for `refine` · `_` for `?_` · the 16-line direct proof of `disjoint_union_right` ·
`valid := fun _ _ => True`, which breaks exactly `op_comm` · a right-biased `op`, which works ·
a typeclass instead of a `structure` (`detail`).

## Exercises
- `m2-5` **union_assoc** [C 3] — three leaves, no hypothesis; the middle needs `union_eq_none.mpr`,
  the fourth case needs a `have` because no lemma states it.
- `m2-6` **union_comm** [C 3] — `rcases hd l` spends the hypothesis, a `cases hl :` inside each
  branch; a `detail` shows the hypothesis-free proof stopping at `⊢ some v = some w`.
- `m2-7` **disjoint_union_left / _right** [C 4] — `refine`; the mirror is conjugated with
  `disjoint_symm`, and the 16-line direct reproof sits in `deep` for comparison.
- `x23` **heapPCM** [D 1] — eight fields; two need `fun _ _ hd => …` because their heaps are
  implicit; `deep` carries the arbitrary-`PCM` proof of right neutrality.
- `x24` **union_cancel_left** [C 4] — `congrFun` on the hypothesis; `he` is unused in half the
  cases; `agreePCM` then refutes cancellativity for PCMs in general.

## Not explained (earlier summaries say it is known)
All of Modules 0 and 1; `rcases`, `constructor`, `Or.inl/inr`, `.1`/`.2`, `.mp`/`.mpr`, dot-notation
resolution, `absurd`, `subst`, `by_cases`, `congrFun`, `funext`, `cases hl : e with`, `by …` in a
term, the three lookup lemmas and the never-unfold-`Heap.union` discipline.

## Deviations from COURSE-PLAN.md
1. **58 non-`ex` blocks against §D's ~30**, over §C's band; prose *under* budget. The excess is 15
   compiled `code`/`anat` blocks and 4 `state`s. ERRATA §18. Largest Module-2 unit; not a precedent.
2. **§D's `(List, ++, [])` example is unusable** — §E.2 books `List`/`[]` at unit 20. Replaced by
   `(Nat, ×, 1)` and composition, which is the better pair since one of them is non-commutative.
   **Plan gap.**
3. **The `note kind:'key'` does not name `∗`** (§E.5 books it at unit 14). It makes §D's claim in
   English and names Unit 38 as where it is proved.
4. **The hook says "none of the laws above" and "a single fact about the relation"**, not §D's "the
   four laws" and "a way to say": `Heap.splits` was written down at Unit 08 and this unit proves
   five theorems, so both of §D's counts were false as worded.
5. §D asks for 2 traces; there are 9, one or two per exercise, per PEDAGOGY §7.

## Warnings to successors
- **`ledger.mjs` fires on `K.op` and not on `k.op`** — the coverage check skips dotted names with a
  lowercase head. **Author of `41-beyond`:** your fragment binds `K : PCM M` and projects `K.op`,
  `K.valid_comm`, `K.unit_left`; quoting it will produce six coverage warnings. Rename or waive.
- **`heapPCM` and `union_cancel_left` have no downstream consumers anywhere**; `PCM` is used only in
  `41-beyond`. The closing `note` says so — do not turn it into a promise.
- **`union_eq_none` is called exactly four times in the corpus, all in this fragment**
  (`12-pcm.lean:12, 40, 43, 48`). `union_comm` five times; `union_assoc` three after this unit.
- **`cases hl : e with` rewrites the goal only when `e` literally occurs in it.** In `union_assoc`
  it does not; in `union_comm`, after `rw [union_of_none h₂ h]`, it does. Both states are on the
  page and that contrast is the walk's main point.
- **`refine ⟨fun l => ?_, fun l => ?_⟩` prints both goals at once, 11 lines** — in a `detail` per
  PEDAGOGY §6.1; the main line shows `case mp.refine_1` alone, after a one-hole demo.
- **A hypothesis-carrying `union_assoc` compiles** (unused-binder warning); the real cost is that it
  stops applying to the three overlapping singletons on the page. That is what `m2-5`'s `variants`
  argues, not the warning.
- **`agreePCM` (`Option Val`, left-biased `op`, `valid a b := a = none ∨ b = none ∨ a = b`) is a
  compiled PCM that is not cancellative.** Unit 38 can reuse it; do not build a second.
- **Weakest part, honestly:** `x23` transcribes the table three blocks above it (§D wants the
  difficulty low), so the unit is measured by `m2-5`, `m2-7` and `x24`; and `m2-5`'s rung-4 hint
  gives away the hardest leaf.

- **`disjoint_union_left` is 15 proof lines, `disjoint_union_right` 6, the from-scratch mirror 15.**
  The page states those three numbers; an earlier draft said 15/5/16 and "eleven lines saved". A
  later edit that changes either proof must recount.
- **`disjoint_union_left` has THREE obligations**, not four: `mp.refine_1`, `mp.refine_2`, `mpr`.
- **`heapPCM` has six bare-name fields, three of them theorem names** (`op`, `unit`, `valid` are
  definitions; `op_assoc`, `unit_left`, `valid_unit` are theorems; `op_comm` and `valid_comm` are
  wrapped).
- **The two `disjoint_union_*` bridges are NOT axioms of `PCM`.** The "what has just been proved"
  paragraph counts six statements that *are* the axioms and says outright that the bridges are not
  among them; do not fold them back into the list.
- **`∪` has never been shown to an Edition-2 reader** and has no ledger row. Heap combination is
  written `Heap.union` or `h₁.union h₂` in prose everywhere on this page.

## Provenance and checks
Every `state` and `trace` step is `check.sh 12 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (the first `state` says so). All 15
`code`/`anat` blocks were re-extracted by script and re-run: `verified` ones report only
`has already been declared`, the two `sketch`es give exactly the quoted errors, `illustration`s are
silent bar the `#check` block whose output is the quoted `state`. The two `agreePCM` blocks compile
as a pair, in page order. Every `pitfall`/`variants` claim was compiled separately: `rcases hd with
h | h`; swapped `.1`/`.2`; `rw [h1] at hl`; both wrong arguments in `m2-5`'s doubly-silent leaf;
bare `union_comm`/`disjoint_symm` as fields; `valid := fun _ _ => True`; the right-biased instance;
the hypothesis-carrying `union_assoc`; right cancellation; and the two-example refutation of
cancellation without disjointness.

All green: `node --check`; `lint.mjs` **0/0** (63 blocks); `ledger.mjs 12-pcm` 0/0 and edition-wide
0/0, sweep and `frags` clean, **no waivers of any kind**; `render-check.js` 0 problems;
`verify.sh 12` (547 lines, 93 declarations) and bare `verify.sh` (2286 lines, 312 declarations);
`gen-contexts.mjs --prove` **43/43**; banned-phrase grep and the widened sweep clean; ERRATA §7's
`<code>`-collision grep returns zero. (`tools/validate.js` rejects the file — "chapter id 'pcm' is
not in the baseline" — as it rejects every Edition-2 unit; it is a first-edition tool.)

## What review changed
Recorded so a successor does not reintroduce any of it. **The Lean was not touched** — every `sol`
was re-checked to occur verbatim in `12-pcm.lean`, every `state` and every `trace` step was
regenerated with `trace_state` through `check.sh 12 --incl` and diffed against the page (identical,
byte for byte), all seven `illustration`s and both `sketch`es were re-extracted and re-run, and every
`pitfall`/`variants` claim was recompiled as its own snippet. Every fix below is prose.

- **Four arithmetic errors, all in `m2-7`.** `solNote` said "Fifteen lines and then five" (the second
  proof is six lines); the `deep` caption said "sixteen lines against five" (fifteen against six);
  the following paragraph said "Eleven lines saved" (nine); `setup` and the rung-4 hint both said the
  theorem has "four" obligations/leaves (three: two forward components and the backward direction).
- **`x23`'s `solNote` said "Five of the eight lines are a theorem name and nothing else."** Six lines
  are a bare name; only three of those are theorem names.
- **The "what has just been proved" paragraph called the two `disjoint_union_*` bridges axioms** —
  "Those are not five unrelated facts about heaps; they are the axioms of a structure" — while
  omitting `valid_unit` and `valid_comm`, which *are* fields four blocks later. A reader reaching the
  `defn` card would have found the distribution law missing and two laws unannounced. Rewritten to
  count the six statements that map onto fields and to say explicitly that the bridges do not.
- **`m2-5`'s `why` located `union_eq_none.mpr` in "the middle branch".** It is the leaf where *both*
  left-hand heaps are silent — the same error `11-union`'s review had already fixed in `x21`'s `why`.
- **`∪` was used six times in one paragraph.** The symbol has no ledger row and appears in no
  Edition-2 unit. Rewritten in dot notation, which is what the goal states on the same page print.
- **The `refine` paragraph announced "Two details are doing work here", gave both in one sentence,
  and the next paragraph opened "The other detail is the question mark"** — three things counted as
  two. Restructured; no announcement sentence survives.
- **The `_`-instead-of-`?_` caption said "two identical complaints".** The two differ (`h₁` versus
  `h₂`), and Lean prints the `h₂` one first. Now "two complaints of the same shape", with the
  difference named.
- **"One property of heaps has been used implicitly for several units and never stated."** Neither
  "the rest of the heap" nor "complement" occurs anywhere in Units 00–09; the claim was unsupported.
  Replaced by the honest motivation — Unit 07 made ownership exact, and the complementary phrase
  names something only if a heap determines its complement. `x24`'s `why` had duplicated that
  sentence and now points forward to Unit 38 instead.
- **The commutativity paragraph reasoned about `Heap.union`'s `match`** ("one of the two branches of
  the `match` is empty on both sides of the equation") — unparseable, and against the unit's own
  never-open-the-definition discipline. Now: at every address there is at most one answer to be had,
  so a rule for preferring one answer over another has nothing to decide.
- **The second opening paragraph was a table of contents** ("This unit proves the two laws, proves
  the two bridge lemmas … and then writes the name down"). Cut to the claim it was carrying. The
  first paragraph's opening clause defined *associative* and *commutative* for a reader PEDAGOGY §1
  says already has them; cut.
- Minor: "merely constrained" (banned word, greppable) → "narrowed it down".

**Not changed, and why.** §D's **New Lean** list includes "`obtain` applied to the result of `.mp`
on an `↔`"; the unit uses `have h' := disjoint_union_left.mp (disjoint_symm hd)` and then `h'.1` /
`h'.2`, which is the corpus proof verbatim and may not be rewritten. `obtain` is booked at `11-union`
in any case, so nothing is introduced late. **The 58 non-`ex` blocks against §D's ~30 stand**: the
prose is 2,550 words against a ~5-screen budget, so the overrun is entirely compiled exhibits and
goal states, and reading every block against PEDAGOGY §4's test found nothing that could come out
without deleting an argument. It remains the largest Module-2 unit and should not be a precedent —
see ERRATA §18.
