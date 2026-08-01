# Unit 01 · `terms` · Propositions are types, proofs are terms
`site/content/02-terms.js` · 44 blocks (40 non-`ex`), 4 exercises, ~1750 words of paragraph prose.
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Establish that a proof *is* a term whose type is the statement — so implication is a function type,
modus ponens is application, a hypothesis is an argument — and hand over the four connectives,
buildable and destructible, in term mode and tactic mode.

## The hook I left (verbatim, final block)
> Nothing you have written can compute. `2 + 2 = 4` was closed by `rfl`, and so was `3 + 1 = 4`
> inside an existential — but why did that work, and when will it stop working? Memory is going to
> be a function, and the first thing we ask of two heaps is whether they are equal.

`two_add_two` is **on the page**, so `03-compute` can open on a line the reader has seen.

## Introduced
**Tactics:** `exact` · `obtain ⟨…⟩ :=` · `rcases … with … | …`, **and that `rcases` and `obtain`
are one tactic under two spellings** (both accept both kinds of pattern; compiled) ·
`constructor` (on `∧` in the main line, on `↔` in a fold) · `left` / `right` · `·` focus dot ·
`;` (see warnings).

**Syntax:** `fun x y => e` as a proof · `→` right-associativity · application as modus ponens ·
`∀` as the dependent function type, and that a binder list, a `∀` and a chain of `→` are one thing ·
`∃` · `∨` · `↔` · `⟨…⟩`, the single-constructor rule, **and its flattening** (`⟨a,b,c⟩`=`⟨a,⟨b,c⟩⟩`) ·
`.1`/`.2`, and that they are shorthand for the field names `left`/`right` · implicit binders
`{x : T}` · `@f` · `rfl` as a term · the word *sort*, glossed in one clause where the first
``of sort `Prop` … of sort `Type` `` message appears.

**Names / dot notation:** `Or.inl`, `Or.inr`, `Or.elim` (as `h.elim`), `Or.symm`, `Eq.symm`,
`Eq.trans` (as `h1.trans h2`), `Iff`, `Iff.intro`, `.mp`, `.mpr` — with the resolution rule stated:
`h.foo` = `Head.foo h`, by the head constant of `h`'s **type**. `.mp`/`.mpr` are `Iff`'s field
names, which is why `constructor` on an `↔` prints `case mp` / `case mpr`.

**Concepts:** propositions-as-types · why `∨` can be neither projected nor built with `⟨…⟩` · why
`∃` cannot be projected · the six-slot shape of `star`, met with no heaps in it · that
`Entails P Q` will be `∀ σ h, P σ h → Q σ h`, so **every entailment proof is a lambda**.

**Course names now usable:** `implication_example`, `mp`, `comp`, `and_comm'`, `or_comm'`,
`and_comm_tac`, `or_comm_tac`, `exists_example`, `exists_three`, `exists_mono`, `nested_pack`,
`nested_unpack`, `two_add_two`.

## Page order (so a successor can find things)
proof-is-a-term → `implication_example` `anat` → `mp`, explicit binders and their failure →
implicit binders and `@` → **x03 `comp`** → `∃`/`∧` and `⟨…⟩` → **x04 `and_comm'`** → the corpus
`and_comm'` line, *after* the exercise → `∨` cannot be projected, `Or.elim`, dot notation →
tactic mode: `constructor` on `∧` with its two-goal state, then `or_comm_tac` with `rcases`, `;`,
`left`/`right` → **x05 `exists_mono`** → flattening `anat` + the “why six” key note →
**x06 `nested_pack`/`nested_unpack`** → the entailment-is-a-lambda paragraph → `dod` → hook.

## Exercises
- `x03` **comp** [D 1] — `fun hp => g (f hp)`; composition as application, no `by`.
- `x04` **and_comm'** [D 2] — `⟨h.2, h.1⟩`; destruction and construction in one term. **The corpus
  line proving it sits after the exercise, not before it.**
- `x05` **exists_mono** [C 2] — `intro`/`obtain`/`exact ⟨n, h n hn⟩`; witness in, witness out.
  Its *statement* is `#check`ed early, as the implicit-binder exhibit, and the caption says so.
- `x06` **nested_pack / nested_unpack** [C 3] — six slots packed flat, five unpacked flat. Its `sol`
  holds **both** theorems; they are adjacent in the fragment, so `lint` accepts it. `nested_pack`'s
  proof *is* on the page above, deliberately — `why` and `setup` both say the first half is typed
  rather than solved, and `nested_unpack` is where the work is.

## Not explained
Everything in the `00-aliasing` and `01-goalstate` summaries, in particular `Prop`, `Option`, `fun`,
the two-slot `⟨…⟩`, `intro`, `simp … at h`, the goal display, `✝`, `case` labels and `?m.N`.

## Lean and provenance
Fragment `lean/e2/02-terms.lean`, 20 declarations, **unchanged by review**. `verify.sh 02` clean
(73 lines, 20 top-level declarations). `nested_unpack` uses `simp [hxy] at hpx` deliberately: `rw`,
`subst` and `▸` are all booked later, and an `rcases` `rfl` pattern is `subst` in disguise.

**Every `state` and `trace` in the file is `tools/e2/check.sh 02 <snippet> --incl` output with
`trace_state`, byte for byte**, with the `snippet:L:C:` prefix dropped from error text. At review
every one was re-extracted and re-run; all matched:

| shown | snippet compiled |
|---|---|
| `mp (P Q : Prop) : …` | `#check mp` + the `example` calling it |
| the ``of sort `Prop` … of sort `Type` `` error | `example … := mp hp hpq` |
| `exists_mono` / `@exists_mono` signatures | `#check exists_mono` + `#check @exists_mono` |
| ``Invalid `⟨...⟩` notation … more than one constructor`` | `or_comm_bad` |
| x03's two `comp` errors | `comp_bad`, `comp_rev` |
| x04's `And.intro h.left` error | `ac_bad`; `and_forget_left` compiled clean |
| `@Or.symm` signature | the three-line `.symm`/`.trans` block |
| `case left` / `case right` after `constructor` | `and_comm_ctor` + `trace_state` |
| the `iff_and_comm` trio | compiled clean |
| x05's two `projNonPropFromProp` errors | `em_bad`; `forall_mono` compiled clean |
| x05 variants' `Exists.intro n hn` error | `exact ⟨n, hn⟩` with `h` unused |
| x06's `nu_bad` context, `` `simp` made no progress ``, `And.intro hpx` | three snippets |
| x06's `Exists.intro 2 rfl` error | `⟨2, rfl⟩` for `n + 1 = 4` |
| x06 variants' `?m.14 = ?m.14` vs `a = b` | `nested_pack` with `x = b` for `x = a` |
| x06 solNote's `` `simp` made no progress `` | `simp [hxy] at hqy` |
| x06 variants' reversed equation | `y = x` with the `simp` aimed at `hqy` |
| all five `trace` blocks | one file per proof, `trace_state` at every step |
| “`rcases` and `obtain` are one tactic” | `obtain hp \| hq := h` and `rcases h with ⟨hp, hq⟩`, both clean |

`No goals.` is the infoview's wording, not Lean output.

## Deviations from COURSE-PLAN.md
1. **40 non-`ex` blocks against §D's “~30”**, at §C's 16–40 ceiling; seven tactics each need a
   before/after per PEDAGOGY §7. Review held the count at 40 exactly: every promotion was paid for
   by a cut. The four `cmp`s live in exercise `deep`, costing no main-line block.
2. **§D's caption for those `cmp`s (“you will write this in Unit 02; you cannot yet”) is wrong and
   unused.** §E books `obtain`/`rcases`/`constructor`/`left`/`right`/`·` at unit 01, and
   `and_comm_tac`/`or_comm_tac` are in *this* fragment. Tactic mode is taught here.
3. **`#check @funext` dropped** (§D lists it). Its type needs `Sort`, booked at `14-assertions`.
   `#check @Or.symm` carries the lesson with a readable type.
4. **The `or_comm_tac` trace's first state is 9 lines**, breaking PEDAGOGY §6.1: two 7-line goals,
   and the blank line between them *is* the lesson. Same call as `01-goalstate` §2.
5. `x04` is `and_comm'` alone; `or_comm'` and `or_comm_tac` are the main line's worked `∨` example,
   since introducing four tactics inside an exercise breaks §7.
6. **No `dl` of term-level vocabulary** (§D's size line asks for one) and **no `cmp` in `x05`/`x06`**
   (§D asks for one per exercise). Both rejected at review on block budget: the `dod` already
   enumerates the vocabulary, and `x05`/`x06` have no term-versus-tactic contrast worth drawing —
   their solutions are tactic proofs with no short term equivalent.
7. **`and_comm_tac` is in the fragment but has no `code` block of its own.** Its proof body is the
   right column of `x04`'s `cmp`, which now names it, and `x04`'s `deep` traces it. The main line's
   `∧`-with-tactics exhibit is `and_comm_ctor` instead, so that `constructor` is taught in the open.

## Warnings to successors
- **`;` (two tactics on one line) is introduced here, not at `04-funext`** — corpus `or_comm_tac`
  is `· right; exact hp`. ERRATA §17(a); the ledger row has been moved and no waiver remains.
  **`04-funext`'s author: treat it as already met.**
- **`calc` is NOT taught here.** ERRATA §8 assumed `calc_demo` was in this fragment; it is at
  `lean/e2/03-compute.lean:6`, and the row now sits at `03-compute`, **whose author owns it**.
  This unit chains two equations with `h1.trans h2` instead. ERRATA §17(b).
- **`inductive` is waived**, and the waiver is still load-bearing after ERRATA §19. The exemption
  reaches `state` blocks and `Note:`/`Hint:` continuation lines, but it **downgrades rather than
  silences**: drop `ledgerAllow` and you get a `diagnostic` warning, not silence. Verified by
  removing it (1 warning) and restoring it (0/0).
- **`Or.elim` has a `library` row at `02-terms`** (added by `ledger-checker`, verified at
  `lean/e2/02-terms.lean:20`). The original gap was a symptom of ERRATA §19: the checker treats a
  token as a possible citation only if it has `_` or `.` or is CamelCase, so a lowercase,
  underscore-free name (`absurd`, `trivial`, `ite`) is **invisible until it already has a row**.
  Adding Lean to a fragment does not make the checker notice a new name; a manual sweep does.
- **`Type` has a row at `02-terms`**, not at `12-pcm` where it first appears in Lean, because §E's
  rule is about *mentioning* and the propositions-as-types material mentions it. The word *sort* is
  now glossed here too, in the caption of the `mp hp hpq` error.
- **`constructor` and the `↔` material.** `constructor` on `∧`, with its `case left` / `case right`
  state, is **main line**. `Iff`, `.mp`, `.mpr` and `Iff.intro` are in a closed `detail` whose title
  names them, and both are in the `dod` and in `orient.youWill`. `10-disjoint` (`constructor` on
  `↔` in `singleton_disjoint_iff`) may use all of it without ceremony, but should assume the reader
  met `.mp`/`.mpr` once, in a fold.
- **Weakest part, honestly:** `x03` and `x04` are one-liners whose rung-4 hints give the answer, so
  the unit is really measured by `x05` and `x06`; and `x06`'s first theorem is a transcription
  exercise by design.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **The exercise's answer was printed two blocks before the exercise.** The corpus line
  `and_comm' … := fun h => ⟨h.2, h.1⟩` sat above `x04`, whose four graded hints then walk the reader
  to it. Moved to *after* `x04` and recaptioned as the course's copy of what the reader just wrote;
  the paragraph above now introduces `.1`/`.2` in prose so the exercise still has what it needs.
- **The same proof was traced twice.** The main line carried a `code` + `trace` of `and_comm_tac`
  whose three goal states are identical to the `trace` in `x04`'s `deep` ten blocks earlier. Both
  cut. The budget they freed went to promoting `constructor` out of a closed fold — §D objective 4
  requires the reader to be able to split an `∧` goal with it, and nothing in the open text
  delivered that. Net block count unchanged (40 non-`ex`), and the tactic section now runs
  easy-to-hard, `∧` before `∨`, with `·` explained on the three-tactic proof rather than the
  five-tactic one.
- **A false statement about the previous unit.** “Unit 00 *ended* with a theorem…” — it did not;
  `lookup_of_unallocated` is two-thirds of the way through it. Now “Unit 00 *proved*”.
- **A miscount, twice.** “`∀` has appeared in their place, **twice**” — under `@` the implicit pair
  becomes one `∀` and the hypothesis becomes an arrow; the sentence now says that, which is a better
  statement of the `∀`/`→` identity it was reaching for anyway. And “**Three** pieces of syntax”
  introduced four; `·` moved to the `constructor` block, leaving three.
- **A caption that pointed at the wrong lines.** “Read the last two lines first: a proof was offered
  where a statement was wanted” — those lines are the *location*; the sort mismatch is four lines
  up. Rewritten, and *sort* is now glossed there, because `x06`'s pitfall quotes it again.
- **Two back-references that were not accurate.** The `defn` said Lean “rejects `(5 : Option Val)`”
  — a type ascription the reader has not met, and not what Unit 00 showed; it now names what Unit 00
  actually refused. `x06`'s setup said “dissected three blocks above”; it is two, and now says
  “just above”.
- **A gap a reader would stall in:** `obtain` and `rcases` are introduced ten lines apart with no
  word on the difference. One clause added, and both spellings compiled.
- **Three banned-phrase-family hits**, none caught by a literal §4 grep: “the **obvious** thing to
  try”, “the abbreviation is **worth pausing on**”, “One consequence is **worth stating** before it
  is needed”. All rewritten. §4's list should probably grow `obvious` and `worth …-ing`.
- Minor: “the **kernel** actually checks” → “Lean finally checks” (*kernel* is unexplained and the
  `defn` already says *checker*); `x03` hint 1's “there is no `Q` and no `R` in the context” → “no
  *proof* of `Q`…”; `x05`'s `why` claimed `star_mono` is “in the second half of the course” (it is
  Unit 15 of 38); `#check exists_mono` gained a caption saying which exercise it is; `Iff` is now
  “a type with one constructor and two fields” rather than “a structure”, since `structure` is not a
  keyword the reader has met.

## Checks — all green
`node --check` · `lint.mjs` 44 blocks, 0 errors, 1 warning (`x06`'s two-theorem `goal`, expected) ·
`ledger.mjs` 0/0 · `render-check.js` 0 problems, 5 traces · `verify.sh 02` clean ·
banned-phrase grep clean, including the widened sweep above.
