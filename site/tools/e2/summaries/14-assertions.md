# Unit 12 · `assertions` · Assertions and entailment
`site/content/14-assertions.js` · 72 blocks (67 non-`ex`), 5 exercises, ~2380 words of main-line
prose (≈4 screens), 6 traces, 3 `detail` (none before the first exercise). Fragment extended by
two theorems (`x29`); four rows added to `ledger.json` in total (`and_comm_iff`, `and_assoc_iff` by
the author; `True.intro`, `False.elim` at review).
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Lift the algebra to a logic, and make it visible that lifting the *classical* connectives achieves
nothing — so the reader is primed to notice when something finally does.

## The hook I left (verbatim, final block; word for word from §D)
> Every definition here has been a lifting, and every proof the corresponding proof one level down.
> Nothing about *memory* has entered the logic. It enters with one definition, and there are two
> candidates for it — the question Unit 07 posed and did not answer.

Opens on `09-footprint`'s nameless type — `ptsAtLeast`/`ptsExactly` are quoted in the first block
and `Assertion` is the name of the type they already shared. `13-splits`'s hook said *the logic
starts now*; the first sentence takes the first step rather than restating it (see review note 1).

## Introduced
**Tactics: none.**

**Syntax:** `infix:40` and **precedence numbers** — Lean's `∧` at 35 and `∨` at 30 named, the parse
of `P ⊢ Q ∧ Q ⊢ P` predicted then *proved* by `example … := rfl`, and a throwaway `infix:20 " ⊩ "`
compiled to break it. `Sort u` / universe polymorphism (`#check @aExists` → `{α : Sort u_1}`).
Applying an entailment to a store, a heap and a premise (`h₁ σ h hp`). Terms at three binders.

**Notation:** `⊢`, `⊣⊢`.

**Library names first written here:** `True.intro` and `False.elim` (reached as `hq.elim`, by
`02-terms`' dot-notation rule). Both are introduced in the main line beside the `aTrue`/`aFalse`
definitions and exhibited by a compiled `example` pair, because four `variants` fields build their
counterexamples out of them. Both now have ledger rows at this unit.

**Names:** `Assertion`, `Entails`, `AssertionEquiv`, `aTrue`, `aFalse`, `aAnd`, `aOr`, `aExists`,
`fact`; `entails_refl/_trans`, `and_left/_right/_intro`, `or_left/_right/_elim`,
`equiv_refl/_symm/_trans`, **`and_comm_iff`**, **`and_assoc_iff`**. Illustration-only:
`and_comm_eq`, `factExact`, `aExistsT`.

**Concepts:** assertion as a predicate on states, and *why the heap divides and the store does not* ·
entailment as containment, a **preorder proved not assumed**, failing antisymmetry, hence `⊣⊢` ·
**pointwise lifting** (`defn`) · `⊢` as a folded `def` and a folded notation, through which `intro`
finds three binders — **two from the quantifier, one from the arrow; `Assertion` is not unfolded by
`intro` and the page no longer says it is** · `fact`, with the identity function as *proof* that its
truth ignores the heap · **`∧` has projections and duplication is free** — the baseline Unit 14 is
measured against.

**Rejected alternatives, compiled:** one bundled state argument (prose) · `infix:20` · `P ∧ Q` at
`Assertion` · `{α : Type}` for `aExists` · pointwise `↔` for `⊣⊢` (prose) · **equality of
assertions** (`and_comm_eq`; `#print axioms` gives `[propext, Quot.sound]` against none) ·
`factExact`, the embedding Unit 17 takes.

## Exercises
`m3-2` **entails_refl/entails_trans** [D 1] — identity and composition; `deep` sets Unit 01's `comp`
beside it. `m3-3` **and_left/_right/_intro** [D 1] — projection and pairing through a folded `def`;
compiled `P ⊢ aAnd P P`. `x27` **or_left/_right/_elim** [D 2] — the unit's only case split.
`x28` **equiv_refl/_symm/_trans** [D 1] — the second component of `⊣⊢` runs backwards, so the
composition reverses; real `case right ⊢ R ⊢ P`. `x29` **and_comm_iff/and_assoc_iff** [D 2] — ⧗ in
§F; written, compiled, added to the fragment; drills `⟨…⟩` flattening both ways.

## Not explained
All of Modules 0–2: `abbrev`, `show`, `⟨…⟩` and flattening, `.1`/`.2`, `rcases`, `constructor`,
`funext`, `propext`, `#print axioms`, `✝`, dot-notation resolution.

## Deviations from COURSE-PLAN.md
1. **67 non-`ex` blocks against §D's ~20**; prose ~4 screens against ~3. The excess is exhibit
   pairs (14 `code`, 4 `state`, 1 `anat`, 6 traces). ERRATA §18. This is the **largest early unit so
   far** — above `12-pcm`'s 63 and `13-splits`'s 47 — and review looked for cuts against PEDAGOGY §4
   and found none that did not delete a required rejected alternative or a compiled refutation.
   **Not a precedent; a successor at this size should expect to be asked why.**
2. **One `defn`, on *pointwise lifting*, not one per connective** (§D asks five or six). Five cards
   restating one pattern is the loop PEDAGOGY §2 forbids; the closing `tbl` enumerates instead.
3. The `anat` covers **both** fragment lines, so `infix:40` is dissected inside it.
4. `x28`'s `why` corrects §D: `equiv_*` have **no downstream consumers**. The page claims only that
   **thirteen** later theorems conclude in `⊣⊢`, across **six** units, and are read as an
   equivalence. (The pre-review page said twelve across five. Recounted; see below.)
5. `ledgerForward: ['star_or_left', 'star_or_right']` on the chapter object, for `x27`'s `why`,
   which names the two later theorems the exercise's proof is reused by. Same shape as
   `02-terms`' waiver for `star_mono_*`. ERRATA §10's first kind: the sentence says in as many words
   that they are "two later theorems you cannot read yet".

## Warnings to successors
- **Checked counts, re-checked at review with word boundaries.** `entails_refl`+`entails_trans`:
  **28** occurrences after this fragment in **7** units (`17`, `19`, `30`, `32`, `35`, `36`, `37`).
  Theorems concluding in `⊣⊢` after this fragment: **13**, in **6** units (`15-pointsto` 1,
  `17-star-algebra` 4, `18-star-assoc` 1, `34-wp` 5, `36-lseg` 1, `38-partial` 1).
  **`and_left`, `and_right`, `and_intro`, `or_left`, `or_right`, `or_elim`, `equiv_*`,
  `and_comm_iff`, `and_assoc_iff`: ZERO downstream consumers, all of them.** The previous version of
  this summary claimed `and_intro` 4 and `or_left`/`or_right` 2 each; those were substring hits on
  `wand_intro`, `emp_wand_intro`, `star_or_left` and `star_or_right`. Grep with `\b…\b`.
- **`⊢ P ⊢ P` is real output** — two different glyphs. ERRATA §4's row fires only when something
  precedes the turnstile on the line, so a goal line opening with it never fires. Do not "fix" that.
- `intro σ h` alone leaves `⊢ P σ h → P σ h`; a fourth `intro` gives `` `introN` failed `` **plus the
  three-binder context, which the page now quotes in full**. `.1` and `⟨…⟩` both resolve through the
  folded `aAnd`/`AssertionEquiv`, as `rw` did in `09-footprint`.
- **`Sort u` is never exercised on a `Prop` in the whole corpus.** The page says the generality is
  free, not needed. `{α : Type}` fails only on a proposition-indexed family, reporting `?m.1`.
- **The closing claim is verified, not asserted:** an abstract-resource copy (`Store → Res → Prop`
  over `variable (Res : Type)`) compiles. Off the page because `section`/`variable` have no ledger
  rows. **Author of `41-beyond`:** that argument is already checked at assertion level.
- **Unit numbers in prose are §D unit numbers, not file numbers** (ERRATA §13). Every one on this
  page was re-checked against §D at review: 00→`00-aliasing`, 01→`02-terms`, 02→`03-compute`,
  03→`04-funext`, 07→`09-footprint`, 08→`10-disjoint`, 13→`15-pointsto`, 14→`16-star`,
  15→`17-star-algebra`, 17→`19-pure`, 22→`25-hoare`. **Module numbers too**: `∗` is in Module 3,
  *this* module — the pre-review page twice called it "the next module's connective".
- **`x26` and the three `04-funext` drills still carry `status: "todo"`** though declared. Untouched.
- **Weakest part:** all five exercises are [D], four are one-line terms, and every rung-4 hint is
  most of the answer. The unit measures no proof skill; its content is the recognition in the
  closing table. §D's own exercise table prescribes exactly this, so it cannot be fixed here.

## Provenance and checks
Every `state`/`trace` step is `check.sh 14 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped, in-sentence errors de-line-broken (the
first `state` caption says both). Where a split leaves two goals the trace shows only the next one,
and each such state was captured with `trace_state` inside the later bullet. **At review all six
traces were regenerated from scratch** — two snippets, `trace_state` at every step — and diffed
against the page: identical, byte for byte. All 23 Lean-bearing blocks were re-extracted by script
and re-run (`verified` report only `has already been declared`, `illustration`s silent apart from
the two `#check`/`#print` outputs the page quotes, `sketch`es give exactly the quoted errors).
Every `pitfall`/`variants` error quote was recompiled as its own snippet: `h₂ (h₁ hp)`, the
unused-binder linter warning, `h₂ σ h h₁`, `exact hpq`, a one-field `⟨…⟩`, the `aOr P Q ⊢ P`
refutation, `fun _ _ hp => hp` for `or_left`, `h₁ σ h hpq`, `rcases hpq with hp`, the
`aOr P P ⊢ R`/dropped-`h₂` pair, `entails_trans h₁.2 h₂.2`, and the three-error flat triple.

All green: `node --check`; `lint.mjs 14-assertions` **0/0** (72 blocks); `ledger.mjs 14-assertions`
0/0 and edition-wide 0/0, sweep and `frags` clean, one `ledgerForward` waiver (deviation 5);
`render-check.js` 0 problems; `verify.sh 14` (641 lines, 120 declarations) and bare `verify.sh`
(2312 lines, 316 declarations); `gen-contexts.mjs --prove` **54 proved, 0 failed**;
`check-all-exercises.cjs assertions` 2/2 (only `m3-2`/`m3-3` are in the installed
`context-index.json`); **`wasm-check.cjs` over the whole corpus plus this page's two `theorem`-
bearing illustrations, clean** — which matters because ERRATA §28's export rule bites `theorem`s,
and `and_comm_eq` is one; banned-phrase grep clean.

## What review changed
**The Lean fragment was not touched.** Every `sol` was re-checked against `14-assertions.lean`,
every trace regenerated, every error quote recompiled. Two `ledger.json` rows added
(`True.intro`, `False.elim`). Everything else is prose.

- **Two ledger-order errors, now green.** `star_or_left` and `star_or_right` were named bare in
  `x27`'s `why`. The sentence now marks them as unreadable-yet and the chapter carries a
  `ledgerForward`. The page's *unit* attribution was already right (15 and 17); only the waiver was
  missing.
- **Two names used before they existed anywhere in the course:** `True.intro` and `False.elim`
  (as `hq.elim`), in four `variants` fields. Introduced in the main line where `aTrue`/`aFalse` are
  defined, with a compiled two-line `example` giving `aFalse ⊢ P` and `P ⊢ aTrue`, and rowed.
- **A false statement about what `intro` unfolds.** The page said `intro` had to unfold `Assertion`
  as well as `Entails` to find three binders. It does not: `Entails`' body is `∀ σ h, P σ h → Q σ h`
  and that is the whole of it. The `anat` said the same thing a second way — "it is where the
  **three** arguments you will introduce come from", under the `∀ σ h` chip — and now says two of
  the three.
- **`∗` called "the next module's connective", twice.** It is in Module 3, this module, two units
  down. Both fixed; `x29`'s `why`, which said Module 3, was right and is unchanged.
- **A wrong count in `x28`'s `why`:** twelve theorems over five units. It is **thirteen over six**.
- **A `variants` claim contradicted by the page's own `walk`:** halving `and_comm_iff` from `⊣⊢` to
  `⊢` "to see that the second half was not free". For commutativity the second half is the same text
  as the first, which the `walk` says three lines earlier. Now the two halvings are distinguished.
- **A muddled cost argument in the `Why not equality?` fold** — "getting one direction out of an
  equation means proving a biconditional you had before you started", which is not true (`▸` does
  it). Replaced by the real cost: `funext` and `propext` before you can talk about one state.
  The same fold's "Unit 03 showed that half the proofs already do" is now the checkable form: Unit
  03's audit found two of its four theorems depending on those axioms.
- **An imprecise attribution:** "That is the definition Unit 17 takes" of `factExact`. Unit 17
  defines the same assertion as `aAnd (fact φ) emp`, not as that lambda. Said so. The name `pure`
  was tried in the sentence and removed — it is a ledger-order error and buys nothing.
- **The opening was a recap.** The first sentence summarised Module 2 in thirty words, which is
  what `13-splits`'s hook had just said. PEDAGOGY §2: open by picking up the thread, not by
  restating it. Replaced by the first move.
- **`show` re-explained** ("restates a goal as anything definitionally equal to it, and a folded
  definition is definitionally equal to its body") — ledgered at `03-compute` and load-bearing since
  `09-footprint`; `13-splits`' review cut the same re-explanation. Reduced to the one line the
  reader can type, and merged with the paragraph after it. One block fewer.
- **`orient.payoff` and `m3-2`'s `why` carried the same sentence** ("cited twenty-eight times in the
  Lean of seven later units"). Kept in the `why`, where PEDAGOGY §8 wants the forward-pointing
  justification; cut from the payoff.
- **`m3-2`'s `variants` used `aTrue`/`aFalse` before the page defines them.** They are defined two
  sections later. The field now says so in four words.
- **The `introN` error was quoted with its context silently truncated.** Lean prints the three
  binders under that message, and they are the evidence for the sentence the block supports. Now
  quoted in full, and the caption says the context is part of the message.
- Minor: `.1` described as "a different tactic" (it is a projection); the opening `code` caption
  repeated the sentence above it.

**Not changed, and why.** All five exercises stay [D] with giveaway rung-4 hints — §D's table
prescribes the set and the difficulties, and inventing a [C] here would contradict the plan. The
72-block size stands; see deviation 1. The `⊩` demonstration, the `#check @aExists` pair, the two
closed `detail` folds and the `factExact` exhibit all stay: each is the rejected alternative
PEDAGOGY §7 requires for a decision the unit actually takes, and each is compiled.
