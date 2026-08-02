# Unit 16 · `star-assoc` · Associativity
`site/content/18-star-assoc.js` · 52 blocks (50 non-`ex`), 2 exercises, ~2050 words in `p` blocks
(~2650 counting captions, the `note` and the `dod`; ≈4 screens, budget ~4), 1 main-line `trace` +
3 in `deep`, 6 `state` (all inside folds), 4 `detail` (one before the first exercise, one after
`m4-4`, two inside `m4-4`'s `deep`), 3 `tbl`, 2 `cmp`, 1 `txt`, 1 `steps`, 1 `note kind:'key'`,
1 `dod`. **Lean fragment untouched** — `x37`'s `star_assoc_iff` was already written. One
`ledgerForward`, one `ledgerAllow`.
*Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review.*

## One job
One theorem, both directions, done properly: the law that closes the commutative monoid, and the
proof on which every difficulty is disjointness bookkeeping.

## The hook I left (verbatim, final block)
> The algebra is nearly complete and you can move resources around freely. Two things are missing
> before it can be used. First: how do you attach an ordinary proposition — one about the store, of
> the kind `fact` embeds — to a separating conjunction, when a proposition owns no memory and `∗`
> insists that its two sides own disjoint pieces? Second, and further off: there is still nothing in
> this course to reason *about*. No program has been written down.

Opens on `17-star-algebra`'s hook in its first four words ("That law is associativity"), and puts
`splits_assoc` beside `star_assoc_left` in a `cmp` in block 1, as §D asks.

## Introduced
**Tactics: none.** `intro`, `subst`, `obtain`, `refine … ?_`, `rw`, `rw … at`, `constructor`, the
focus dot — all ledgered ≤ 14 and used without ceremony.

**Syntax owned here:** **deeply nested `intro` patterns** — a six-slot tuple inside slot 5 (forward)
or slot 6 (mirror) of a six-slot tuple, eleven names in one line. §D says "nothing else", and the
page now says so in as many words, in the paragraph after the pattern is displayed.

**Names now usable:** `star_assoc_left`, `star_assoc_right`, `star_assoc_iff`. Illustration-only, in
no fragment: `sqSum`, `sqSum_comm`, `sqSum_not_assoc`, `union_assoc_hyp`, `starNoDisj_assoc_left`.

**Concepts:** the re-bracketing picture — *nothing moves; one intermediate name dies and one is
born* · the three pairwise disjointness facts and the two ways of bundling them, which is the
unit's thesis · `disjoint_union_left`/`_right` name a **side of `Heap.disjoint`**, not a side of the
goal · `subst` before you build, and why the goal is untouched · **the commutative monoid of
assertions, complete** (`tbl` mapping each law of `∗` to what it spends) · **`∗` as the connective
any PCM induces**, with the caveat stated *inside* the `note` rather than retracted after it: the
unit law and commutativity transfer with the same proofs, associativity does not, because
`star_assoc_left` cites a bridge twice and neither bridge is a `PCM` field. Unit 38 is named for
the proof of the part that does transfer.

**Rejected alternatives, all compiled:** `rw [hu₂] at hd₁ hu₁` for `subst` (works; costs two dead
context lines) · `obtain` before `subst` (metavariables) · the flat eleven-name pattern · the wrong
conjunct handed to the bridge · `disjoint_union_left.mpr` where `_right` is wanted · a
hypothesis-carrying `union_assoc` (survives — all three facts are in scope) · deleting disjointness
from `∗` (associativity survives, commutativity does not) · `sqSum`, commutative and not associative
· `⟨star_assoc_left, star_assoc_right⟩` unapplied · the two `⊣⊢` components swapped.

## Exercises
- `m4-4` **star_assoc_left / star_assoc_right** [C 4, `hard`] — the hardest pure-`∗` proof; both
  directions; `deep` has the full forward `trace`, a `steps` mapping each obligation to the picture,
  a `cmp` of the swap, and three compiled `variants` exhibits.
- `x37` **star_assoc_iff** [D 1] — packaging; a two-slot term with no tactic in it.

## Not explained (earlier summaries say it is known)
All of Modules 0–2 and Units 12–15: `⟨…⟩` flattening, the six-name `intro` pattern, `∗`'s
definition, `⊢`/`⊣⊢`, `refine`'s holes, `Heap.union`'s left bias, `union_assoc`/`union_comm`, the
two bridges, `equiv_symm`, `star_congr`.

## Deviations from COURSE-PLAN.md
1. **50 non-`ex` blocks against §D's ~22**; prose at budget. ERRATA §18. Below `17-star-algebra`
   (53) and `16-star` (60).
2. **§D asks for 2 main-line traces; there is 1.** Every goal state in this proof is 10–14 lines and
   `show` cannot shorten a *context*. The only ≤8-line state on the page is what the un-nested
   six-name `intro` leaves, and that is the main-line trace; the full forward trace is in `m4-4`'s
   `deep` (where §D puts it) and the two long context dumps are in the one pre-exercise `detail`,
   per PEDAGOGY §6.1.
3. **The main line does not display the assembled proof.** It exhibits the `intro`, `subst` and
   `obtain` lines individually with their states, the four-row disjointness table and the six-slot
   goal table, and stops before the `refine`. `13-splits` and `17-star-algebra` both flagged
   "the worked example is half the exercise" as their weakest point; a difficulty-4 `hard` exercise
   cannot afford it a third time. Every §D objective is still met on the page.
4. **§D's hook names only the first of "two things missing".** The page names the second — no
   program has been written down — because otherwise the sentence counts to two and stops at one.
5. `ledgerForward: ['star_swap_middle']` (named in `m4-4`'s `why` and in `orient.payoff`, both
   attributed to Unit 17). `ledgerAllow: ['star_assoc']` — the page says in as many words that no
   such theorem exists, which is ERRATA §1's documented false-positive class.
6. **§D's Unit 38 entry says "swap heaps for permissions … and every law of Module 3 holds
   verbatim". That is too strong and this page contradicts it**, with the reason: generic
   associativity needs validity-composition, which is not a `PCM` field. `13-splits`' retrospective
   reached the same conclusion about `splits_assoc`, and `41-beyond.lean` proves only `pcmStar_comm`
   and `pcmStar_unit_left`. **Author of `41-beyond`:** the plan sentence, not this page, is the one
   to fix.

## Warnings to successors
- **Every goal state in `star_assoc_left` is 10–14 lines.** There is no `show` that fixes it, because
  the length is context, not conclusion. Plan for folds if you quote this proof.
- **`subst hu₁` then `subst hu₂` also compiles**, and then the equation slot takes
  `union_assoc hP hQ hR` directly instead of `rw [hu₁, union_assoc]` — no holes needed, one `exact`.
  Compiled. The page does not show it; it is a legitimate alternative answer and
  `gen-contexts --prove` will accept the corpus version only.
- **In the mirror, `rw [hu₁, union_assoc]` is character-identical to the forward direction and does
  something different**: `union_assoc` fires on the *right*-hand side of the equation. The `walk`
  says so; do not "simplify" that row.
- **The corpus `refine` leaves slot 3 filled inline and slots 4 and 6 as `?_`.** A pre-review
  sentence said "slots 3 and 4"; if you cite the shape of this proof, count from the corpus, not
  from the four-row disjointness table.
- **`Iff.rfl` is booked at `31-aliasing-closed`**, so the unfolded shape of the goal cannot be
  displayed as an `Iff.rfl` example before then. I checked the unfolding with
  `example … (k : ∃ h₁ h₂, …) : (P ∗ (Q ∗ R)) σ h := k` and did not ship it.
- **"elaborator" appears in no Edition-2 content file.** It was used once here and has been removed.
  If you need the word, book a row first.
- **Downstream counts, re-grepped at review over `19-*`…`41-*` with word boundaries:**
  `star_assoc_left` **7** (`19-pure` ×2, `36-lseg` ×4, `32-symbolic` ×1) · `star_assoc_right` **2**
  (both `19-pure`) · `star_assoc_iff` **ZERO**, and `x37`'s `why` now says so outright, as `x36`'s
  does for its four.
- **The six-name `intro` pattern does NOT stop here.** `19-pure.lean:8,25,44`, `32-symbolic.lean:59,64`,
  `35-listrep.lean:28` and `37-wand.lean:14` all open `intro σ h ⟨…⟩`, two of them with a nested
  tuple. A pre-review sentence in `m4-4`'s `why` claimed everything after this page is a composition
  with no heaps in it; that is false and has been narrowed to the true claim — no later proof
  *re-brackets* by hand.
- **Author of `19-pure`:** `m4-4`'s `why` claims by name that `star_assoc_right` *opens*
  `star_swap_middle` and `star_assoc_left` *closes* it, and that neither `star_rotate_*` names a
  heap. `19-pure.lean:13–21` bears both out today.
- **Author of `36-lseg`:** the page claims the inductive step of each of your two list theorems is a
  chain of `entails_trans` with `star_assoc_left` in it twice and no heap named. True of the `cons`
  branches only — your `nil` branches do name heaps. The sentence says "inductive step" for that
  reason.
- **`sqSum`, `union_assoc_hyp`, `starNoDisj_assoc_left` are new illustration names**, checked
  against the whole corpus for collisions (none) and deliberately kept out of the fragment. They
  have no `ledger.json` rows and `ledger.mjs` stays quiet because the blocks *declare* them
  (ERRATA §10). If a later unit wants to cite one, add an `illustration`-status row first.
- **Overlap with `13-splits` is structural and deliberate, but it is the unit's real risk.** Unit 11
  already taught `subst`-before-the-bridge (with the same metavariable message), extract-with-`.mp`,
  build-with-`.mpr`, the `rfl` reward for choosing the witness the goal wants, and — in its
  `variants` — the mirror with the two lemma names swapped. §D nevertheless makes all of those this
  unit's objectives 3–6. The page handles it by naming Unit 11 in block 1 and by saying that the
  argument inside the packaging is Unit 11's; it does **not** re-derive the splitting picture. If a
  reviewer wants further cuts, the paragraph beginning "Doing it first" and pitfall (2) are the two
  that repeat Unit 11 most closely.
- **Weakest part, honestly:** `x37` is a two-name term whose rung-4 hint is the whole answer — §D
  grades it 1, so that is the prescribed shape — and `m4-4`'s rung-4 hint hands over the `intro`
  pattern, the `subst`, the `obtain` and the witness, leaving only the two bridge applications and
  the mirror. The unit is measured by `m4-4` alone, and by about half of it.

## Provenance and checks
Every `state` and every `trace` step is `check.sh 18 <snippet>` output (`--incl` for `x37`'s two),
byte for byte, `trace_state` where a mid-proof state was wanted, `snippet:L:C:` dropped, quoted
errors de-line-broken. The two `refine` goals are printed unelided; the single-goal versions in the
`deep` fold come from `trace_state` inside a focus dot. All five `illustration` blocks compile as
one file (silent); the two `sketch`es are honest — the statement pair gives exactly `unsolved goals`
twice, and the bare `intro` line is one tactic and says so. **Every `pitfall` and `variants` claim
was compiled as its own snippet** — including all six quoted error messages.

All green after review: `node --check`; `lint.mjs 18-star-assoc` **0/0** (52 blocks); `ledger.mjs
18-star-assoc` **0/0**, sweep and `frags` clean; `render-check.js` 0 problems; `verify.sh 18`
(852 lines, 155 declarations); banned-phrase grep clean.

## What review changed
**No Lean was edited, and no exercise `id`, `name`, `goal`, `sol` or hint rung was touched.** All
sixteen `state`/`trace` states were regenerated from scratch with `trace_state` through
`check.sh 18` and diffed against the page: **identical byte for byte**, including the two-goal
`refine` dump and both halfway-through-the-rewrite states. All five `illustration`s were
re-extracted and recompiled as one file (silent). All six quoted error messages were reproduced by
breaking a real proof: the flat eleven-name pattern, `obtain` before `subst` (`?m.114`/`?m.115`/`?m.116`
unchanged), `⟨hd₂, hQR⟩`, the mirror's `⟨hd₂, hPR⟩`, the unapplied `⟨star_assoc_left, …⟩`, and the
swapped `⊣⊢` components — plus `x36`'s `⟨star_comm Q P, star_comm P Q⟩`, quoted in `x37`'s
`variants`. Everything below is prose.

- **Two factual errors about the corpus proof's own shape.** "Slots 3 and 4 are the ones worth
  leaving as holes" — the corpus fills slot 3 inline and leaves 4 and 6. And the six-slot table's
  caption said "Two of the six take a hypothesis you already have under its own name"; only slot 5
  does. Both corrected.
- **The `note kind:'key'` was contradicted by the paragraph directly under it.** It claimed "every
  law on this page holds with the same proof" over an arbitrary PCM; the next paragraph then said
  associativity does not. The note now claims the unit law and commutativity, names the symmetry of
  validity among the fields it lists (`star_comm` spends it, via `disjoint_symm`, and the list had
  omitted it), and ends on the exception; the paragraph under it picks that word up.
- **"the two `obtain` lines of the proof are the exact place where that shows"** — `star_assoc_left`
  has one `obtain`. The second bridge is in the third slot of the `refine`, and the sentence and
  `youWill` item 8 now say "two places", not "two lines".
- **`m4-4`'s `why` overclaimed the future.** "This is … the last one. Everything after it that looks
  like this is a *composition* of finished theorems rather than a new argument with heaps in it" —
  seven later proofs open `intro σ h ⟨…⟩` and two of them nest. Narrowed to what is true: no later
  proof re-brackets by hand.
- **"the packaging is what this page is about, because it is where every mistake is made"** — the
  page's own thesis, three sections later, is that every difficulty is in the disjointness table,
  and §D asks the unit to report that the difficulty is mathematical rather than syntactic. The
  sentence now says the packaging is what the page teaches you to handle and that the argument
  inside it is about disjointness. A new paragraph after the nested pattern states §D's "nothing
  else" outright, which no block previously did.
- **"The repair in both cases is `rw … at`"**, in the `subst`-refuses fold. False for the second
  case: `hd₁` is not an equation and `rw … at` repairs nothing. Split in two.
- **"elaborator"** — a word that occurs in no Edition-2 content file. Replaced by "the type
  mismatch", which is what `x37`'s `variants` actually shows.
- **A sentence restating its predecessor** (PEDAGOGY §4's last row): "So this slot generates nothing
  to discharge. There is no disjointness side condition hiding in it, no proof obligation left
  behind." Merged. Same for `x37`'s `why`, where "until this line exists, associativity cannot be
  used that way at all" and "Packaging the pair is what makes … usable as a rewrite" said one thing
  twice; and for "Two facts are in the context and two are wanted. They are four different
  statements."
- **Two competing accounts of why `subst` goes first**, in consecutive paragraphs — "that is the
  point of doing this now rather than later: `subst` costs nothing here" against "Doing it first is
  what makes the next line possible at all." The first now says only that the move is free; the
  second gives the reason to make it.
- **An unverifiable forward claim cut:** "which is the shape every specification in Modules 6 and 7
  is written in". Most specifications there are two conjuncts; the re-bracketing only bites at
  `32-symbolic.lean:76`. The `orient.payoff` and `m4-4`'s `why` carry the forward claims that were
  actually grepped.
- **A flourish cut:** "the reliable way to spend twenty minutes on a two-character mistake" —
  neither number is a fact. Replaced by the load-bearing statement, that the naming rule is what
  decides which lemma goes where in each direction.
- **`x37`'s `variants` said a reader "cannot see which is which"** about `⟨star_comm P Q,
  star_comm Q P⟩`. The arguments differ and are visible; the true difference is that reading them
  requires remembering which way `star_comm` points. Rewritten.
- **One announcing sentence cut** — "Put the two statements side by side", immediately before the
  `cmp` that does exactly that — and "Here is the goal, read slot by slot" trimmed into the
  paragraph it opened.
- **`x37`'s `why` now states its own downstream count is zero**, matching what `x36` did one unit
  earlier, instead of implying a use that never arrives.

**Not changed, and why.** The 52-block size stands (ERRATA §18). Both exercises keep their
§D-prescribed ids, names, kinds and difficulties, and their `goal`/`sol` text is the fragment
verbatim; `m4-4`'s `goal` keeps the house convention of `sorry` on the first theorem and a bare
`:= by` on the second, as `17-star-algebra`'s `m4-1` and `m4-2` do. The single main-line trace
stands (deviation 2): there is no second state on this page short enough for the main line, and
inventing one by cutting hypotheses would break PEDAGOGY §10. The overlap with `13-splits` stands:
§D makes it this unit's objectives 3–6, and the page's answer is to cite Unit 11 rather than pretend
the argument is new.
