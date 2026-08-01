# Unit 04 · `update` · LAB — the update family
`site/content/05-update.js` · 35 top-level blocks (30 non-`ex`), 5 exercises, ~980 words of
main-line prose. Lab format: brief → worked example → five exercises → retrospective.
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Guided doing: five theorems about changing a function at one point, with no new syntax, so that
the heap laws of Units 05 and 06 are recognised rather than learned.

## The hook I left (verbatim, final block)
> `update_comm` used `hne` exactly once, to derive `z ≠ y` from `z = x`. Remember that line: in
> twenty-three units it is the reason the frame rule is true. But nobody hands you `hne` in a real
> program, and `update` cannot give a cell up — "not mine" is what `emp` will be made of.

The unit opens on `04-funext`'s hook (“The theorems there are about updating a function at one
point”) with “Here is the operation those theorems are about.”

## Introduced
**Tactics: none.** The page says so in its first paragraph; that is the point of it.

**Names now usable:** `update`, `update_same`, `update_other`, `update_shadow`, `update_comm`,
`update_idem`. Named in prose only: `↓reduceIte`, the core simproc collapsing an `if` whose
condition is settled (no ledger row; the checker does not fire on it). The page says the arrow is
part of the name.

**Concepts:** locality of an update ("the baby frame rule") · shadowing (unconditional) versus
commuting (conditional), and that the asymmetry is what the frame rule will be made of · the rule
for choosing between `simp` and hand-driven `rw` — `simp` when both branches want the same text
and the route is not the content; `rw` when the *location* a hypothesis is spent at is.

## Exercises
- `m0-1` **update_same** [D 1] — `simp [update]`; `deep` splits it into `simp only [update]` then
  `simp only [↓reduceIte]` so the intermediate goal prints.
- `m0-2` **update_other** [D 1] — `simp [update, hne]`; three rules instead of two, the middle one
  the hypothesis. The residue `⊢ y = x → value = f y` is read as a bill.
- `m0-3` **update_shadow** [C 2] — `funext` → `by_cases` → `<;> simp [update, h]`.
- `m0-4` **update_comm** [C 3] — hand-driven, eight lines; the `have` is bolded in the `walk` as the
  one line consuming `hne`.
- `x13` **update_idem** [G 2] — the reader writes the statement (see deviation 2).

## Not explained
Everything `04-funext` introduced, plus its unused-simp-argument warning and its
`⊢ x = a → f a = f x` residue, so `m0-2`'s pitfall starts from recognition. **`unfold` and `have`
are NOT re-introduced**: `03-compute`'s review moved both to its main line and withdrew the request
that this page reintroduce them. The page uses them and says only what is local — that `unfold`
leaves the conditional standing where `if_pos` can reach it, and what the `have`'s subproof did.

## Provenance
No Lean fragment touched; `verify.sh` still reports 310 declarations. **Every `state`, and every
`trace` step's `state`, is `tools/e2/check.sh 05 <snippet> --incl` output byte for byte**,
`trace_state` where a mid-proof state was wanted, `snippet:L:C:` prefix dropped (first caption says
so). Each `sketch` block's error is that block compiled. At review **all twelve `code` blocks were
re-extracted from the finished file and re-run**: the four `illustration`s compile silently, the
five `sketch`es produce exactly the errors quoted beneath them, and the three `verified` blocks are
corpus text. Every "this one is false" claim in a `variants` or `pitfall` field was compiled as its
own snippet — the full list is in “What review changed”. `↓reduceIte` and the rule counts came from
`simp?` run offline — it belongs to §`errors` and is not on the page.

## Deviations from COURSE-PLAN.md
1. **§D objective 1 says "which three rewrites `simp` fired in each". It is three in
   `update_other`, two in `update_same`** (`update`, `↓reduceIte` — `simp` settles `x = x`
   unprompted). The page states the real counts and makes the difference the lesson.
   **Plan slip**, recorded in ERRATA §22.
2. **`x13`'s `goal` is a placeholder, not the statement.** PEDAGOGY §8 wants a [G] statement
   revealed at rung 3, but `app.js` mounts an editor only when `goal` exists *and renders it above
   the box*. So `goal` is two comment lines plus `example : True := by`, which `starterFor`
   completes with `sorry`. Hence `lint.mjs`'s one warning, which is expected; `--prove` passes.
   ERRATA §22.
3. **30 non-`ex` blocks against §D's ~16**, inside §C's 16–40 and below the three preceding units
   (40, 52, 64). ERRATA §18 makes the budget advisory. Prose is at budget (~980 words ≈ 2 screens).
4. §D's "New mathematics" is one `note` between `m0-4` and `x13` plus the first retrospective
   answer, not a section: PEDAGOGY §11 allows one sentence between exercises.

## Ledger
`ledgerForward: ['emp', 'Heap.write', 'write_same', 'write_other', 'write_shadow', 'write_comm',
'write_of_eq']`. `emp` is the contractual hook's; the six others are the "here is where this goes"
kind, one per exercise `why`, naming the heap theorem that exercise becomes. `ledger.mjs 05-update`
is 0/0; a stale-waiver warning fires the moment one of them stops being named, so do not copy the
list without the sentences.

## Warnings to successors
- **The one-liner for `update_comm` needs `hne` in *both* orientations.**
  `by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [update, hzx, hzy, hne, hne.symm]` closes
  it; drop `hne.symm` and one goal of four survives as `⊢ y = x → b = a`; drop `hne` too and three
  of the four survive. Both compiled; on the page, in `m0-4`'s `deep`.
- **`simp [update]` on an equation between two `update`s, with no `funext` first, gives
  `` `simp` made no progress ``** rather than a partial simplification. Bare `simp` gives the same
  message on `update_same` and `update_other`. Expect all three again in Unit 05.
- **Author of `07-heap` (Unit 05):** the proof shapes are installed and named here — three moves for
  a function equality, three regions for two write points, and the `have` turning "this point is
  `x`" into "this point is not `y`". The page promises by name that `write_same` and `write_other`
  are `update_same` and `update_other` with one type changed. Do not re-derive the shapes.
- **Author of `08-heap-laws` (Unit 06):** this page promises, by name, that `write_shadow` and
  `write_comm` are `update_shadow` and `update_comm` line for line — they are, in the fragment
  today — and that `write_of_eq` is the hypothesis-carrying generalisation of `x13`'s statement,
  which `x13`'s `variants` argues for on its own merits. If any of that changes, this page must.
- **`Store` is named here**, in the brief: `Store` is `Var → Val` is `Nat → Nat`, so `update` is
  already at the store's type. §D Unit 02 asked for that connection to be visible at Unit 04.
  `21-language`'s `storeSet_same` / `storeSet_other` are *literally* `update_same` / `update_other`
  applied — the page does not say so (too far forward), but its author should.
- **Weakest part, honestly:** `m0-1` and `m0-2` are one-liners whose rung-4 hints are the answer,
  and `m0-1`'s answer is the worked example three blocks above it (which §D mandates), so the unit
  is measured by `m0-4` and `x13`; and `x13`'s placeholder starter is a workaround for a UI
  constraint, not a design. A later [G] author with a better one should take it.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **Two false claims about where the payoff lands.** `orient.payoff`, the brief and three `why`
  fields all said Unit 05 proves these five theorems again. It does not: `07-heap.lean` holds six
  *lookup* laws (the `update_same` / `update_other` shapes) and contains no `funext` at all; the
  equations between heaps — `write_shadow`, `write_comm`, `write_of_eq` — are Unit 06's
  (`08-heap-laws.lean`). Every claim now names the actual theorem and the actual unit, which
  required six `ledgerForward` entries and is a strict improvement on the vague version.
- **A miscount in the `cmp` that states the unit's rule.** "Three of the five proofs on this page
  are one line" — the line counts are 1, 1, 2, 8, 2. Now "four of the five end in a single `simp`
  call", which is what the column was reaching for and is true.
- **A false claim in the worked example's opening.** "Both lines above are instances of it" — the
  second concrete line (`update (fun _ => 0) 3 7 5 = 0`) is an instance of `update_other`, not of
  `update_same`. Fixed in the paragraph and in the `sketch`'s caption.
- **A claim `04-funext` had already refuted.** `m0-3`'s `setup` said "Both sides are functions of
  type `Nat → Nat`, so `rfl` is not in question". `04-funext`'s whole opening is a function equality
  that `rfl` *does* close. Rewritten to say what actually blocks it.
- **A wrong statement of `<;>`'s rule**, in the exact words `04-funext`'s review removed from its
  own page: "`<;>` is available exactly when…". It means *is the move to reach for when*.
- **`decidable` used to mean *settled*.** A `trace` step said "The right-hand side is now decidable"
  of a conditional whose condition a hypothesis had just settled. `Decidable` is a typeclass the
  reader met at `03-compute`; the word is now spent only on that.
- **A wrong concept named in the retrospective.** "which of Unit 05's heap laws carry a
  **disjointness** hypothesis" — heap laws carry a *disequality*; disjointness is Unit 08's, is
  about two heaps, and is not introduced. Both occurrences reworded, the second to "an assumption
  that two whole regions of memory do not overlap", which says the thing without the word.
- **`sorry` appeared in a `sketch`.** §D.0 names it once at Unit 00 and bans it thereafter; §E.1
  books its first *display* at Unit 24. `m0-4`'s `deep` used `· sorry` to stub the second branch.
  Replaced by the real two branches: the quoted error is byte-identical, and the sketch now shows
  that the failure is confined to the first region.
- **An overstated comparison.** `m0-2`'s `variants` called `h : f y = value` "far stronger" than
  `hne : y ≠ x`. The two are incomparable.
- **Two re-explanations of things `03-compute` owns.** The paragraph introducing the hand-driven
  proof re-taught what `unfold` does and that it does not try `rfl`; `m0-4`'s `walk` re-taught what
  `have` does. Both cut to the locally load-bearing clause.
- **A claim in `m0-1`'s `expl` that was muddled about decidability.** "the condition being decidable
  *without* knowing what `x` is" — the instance exists either way; what matters is that nothing
  *reduces* `x = x`, so the proof has to be handed over (`if_pos rfl`) or found (`simp`). Rewritten,
  and it now ties the section's three spellings together.
- **A tension between a paragraph and the state below it.** "`simp only [ … ]` fires exactly the
  rules named and stops" is contradicted two lines later by a state in which `simp only [update]`
  has also turned `x = x` into `True`. The paragraph now says what `simp only` actually does.
- Minor: "one word" said of `simp [update]`; "two-character term" said of `rfl` (three);
  `orient.youWill` promised the `simp` rewrites for all four laws, one of which has no `simp` in it;
  "essentially every equation between heaps"; "Note the last two entries"; "how fast you have
  become"; a dangling "the four proof shapes" that the page never enumerates.

## Checks — all green
`node --check` · `lint.mjs` 35 blocks, 0 errors, 1 warning (`x13`'s placeholder `goal`, expected
per ERRATA §22) · `ledger.mjs 05-update` 0/0, sweep clean · `render-check.js` 0 problems (91 KB,
6 traces) · `verify.sh 05` and bare `verify.sh` clean (310 declarations) ·
`gen-contexts.mjs --prove` 17/17 · banned-phrase grep clean, including the widened sweep
(`obvious`, `worth …-ing`, `just`, `simply`, `essentially`, `it turns out`) · all twelve `code`
blocks re-extracted and recompiled through `check.sh 05 --incl`, every `state` and `trace`
re-diffed against the output.
