# Unit 08 · `disjoint` · Disjointness
`site/content/10-disjoint.js` · 45 blocks (41 non-`ex`), 4 exercises, ~1800 words of `p`/`defn`/
`note`/`dod` prose including the three folds (≈2.8 screens), 7 traces, 3 `detail` — one before the
first exercise. 103 KB rendered.
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Define what it means for two heaps not to overlap, and prove the first theorem in the course in
which a disequality between two addresses is **derived** rather than assumed.

## The hook I left (verbatim, final block; word for word from §D)
> We can say two heaps do not overlap. We still cannot *combine* them, and "the heap splits into
> these two pieces" needs both halves of that sentence.

The page must display `Heap.union` (`Heap.splits` mentions it), so the paragraph before the folds
ends "What you have here is the text of an operation and not one law you can use" — that is what
makes the hook true. Opens on `09-footprint`'s hook in its first sentence.

## Page order (so a successor can find things)
the two halves of "splits" → the `write_comm`/`update_comm` debt → **sec** *What "does not overlap"
says* → domains rejected → `def Heap.disjoint` → `defn` → inclusive-disjunction paragraph → `svg`
→ **detail** *Could the domains be written down after all?* → **sec** *Two structural facts* → the
folded `def : Prop` opens under `intro` → the say-nothing example + `trace` → **m2-1** → the empty
heap → **m2-2** → **sec** *Where a disequality comes from* → both statements as a `sketch` → the
ownership reading → `note kind:key` → the three-sentence argument → **h4** `subst` → **h4** `<;> ·`
→ **m2-3** → **x19** → **sec** *The other half of the sentence* → `def Heap.union` / `def
Heap.splits` → the `match` paragraph → **detail** *Disjointness is stronger than it needs to be*
→ **detail** *Why not make the union demand a disjointness proof?* → `dod` → hook.

## Introduced
**Tactics:** `subst` (own `h4`, compiled example, `trace` showing `l₂` *and* the equation leaving the
context; the elimination rule stated and compiled three ways; rejected alternative `rw [heq] at hd`,
compiled) · `<;> ·` (own `h4`, working and semicolon versions side by side, surviving `case inr` goal
printed, and one clause saying that a trailing `<;>` with its argument indented underneath is layout).
`rcases`, `left`/`right`, `constructor` on `↔` and `absurd` get their first *use* here per §E; none is
re-explained. The word **injection** for `Or.inl`/`Or.inr` is glossed once, at `m2-2` rung 3 — no
earlier Edition-2 unit uses it.

**Syntax:** `match … with` in a `def`, one clause only. **`11-union` still owns "why it blocks
reduction".**

**Names now usable:** `Heap.disjoint`, `Heap.union`, `Heap.splits`, `disjoint_symm`,
`disjoint_empty_left`, `disjoint_empty_right`, `singleton_disjoint`, `singleton_disjoint_iff`,
`self_disjoint_iff_empty`. Illustration-only: `dom`, `compatible`, `unionOf`.

**Concepts:** disjointness of resources, at one address at a time · **separation implies
non-aliasing** (`note kind:'key'`) · the inclusive disjunction as a bound on overlap, not a partition.

**Rejected alternatives, all compiled:** domains as predicates on `Loc` (equivalent; eight lines of De
Morgan by hand one way against four the other) · compatibility, the weakest hypothesis making
`Heap.union` commutative — proved so, refused because the course wants ownership, not
well-definedness · `unionOf` carrying its proof, where associativity **cannot be stated**.

## Exercises
- `m2-1` **disjoint_symm** [D 1] — `intro hd l`, `(hd l).symm`; pitfall `hd.symm` before an address
  is chosen, whose `Function.symm` error displays what the hypothesis is.
- `m2-2` **disjoint_empty_left / _right** [D 1] — no tactics; why `rfl` settles `Heap.empty l = none`;
  the wrong injection, whose error lands on `rfl`.
- `m2-3` **singleton_disjoint and singleton_disjoint_iff** [C 3] — separation proves non-aliasing.
  Its `expl` names the shape: `singleton_disjoint` is `write_comm`'s proof with a disjunction where
  that one had an equation, down to the same `have : x ≠ l₂ := by rw [hx]; exact hne`.
- `x19` **self_disjoint_iff_empty** [C 2] — `deep` shows `rw [h1]` leaving `⊢ none = Heap.empty l`
  where `exact h1` closes it.

## Not explained (previous summaries say it is known)
Everything in Modules 0 and 1: all of `funext`/`by_cases`/`<;>`/`;`/`·`/`rw … at`/`have`/`intro`,
`cases h` on distinct constructors, `rcases`/`constructor`/`left`/`right`/`Or.inl`, `.mp`/`.mpr` and
dot-notation resolution, `Ne.symm`, `rfl`'s definitional condition, the goal display and `case`
labels, the four heap operations and the six lookup laws, and exact ownership.

## I changed the Lean fragment — one line (original pass; review touched no Lean)
`singleton_disjoint_iff` ended `exact absurd h (by simp)`. `by` in an argument position is booked at
**`11-union`**, one unit later, and the ledger regex was `,\s*by\b` — comma only, so it could not see
`f x (by tac)`. PEDAGOGY §2 quotes that exact line as the canonical Edition-1 violation. Now
`cases h` (booked at `03-compute`). Same statement, same marker; everything re-run. The regex has
since been widened to `[,(]\s*by\b`, so the fragment pass now enforces what I fixed by hand.

## Deviations from COURSE-PLAN.md
1. **41 non-`ex` blocks against §D's ~26.** Prose is *under* budget; the excess is 16 compiled `code`
   blocks, 3 `state`s and 7 traces, because two new tactics each need a working exhibit and a broken
   one. ERRATA §18. In line with every preceding unit (00: 40, 02: 40, 03: 52, 04: 64, 07: 40,
   08: 40).
2. **§D's second `detail` is Unit 09's own objective 2.** Mine states the cost — associativity cannot
   be *typed* — and hands the resolution to Unit 09 rather than arguing it. The extra fold (domains
   as predicates) carries §D objective 1 in depth.
3. **Both post-exercise `detail`s now sit after `def Heap.union`,** not before it (review; see
   below). §D's ordering of the two folds is unchanged relative to each other.

## Warnings to successors
- **`Heap.union` may not be mentioned in this unit before the `code` block that defines it.** The
  compatibility fold proves `Heap.union h₁ h₂ = Heap.union h₂ h₁` under compatibility and originally
  sat *above* the definition. If you move blocks in this file, keep that fold after it.
- **Two `ledger.json` rows were wrong and are now fixed** — read your own rows, not just the summary
  of them. `trivial` was booked here; its only uses are `17-star-algebra.lean:72,75`, and that unit
  owes it **one** clause. The term-mode `by` row was comma-anchored, blind to `f x (by tac)`; widened
  to `[,(]\s*by\b`, and both spellings arrive together at `11-union:18,19`.
- **`rw`'s trailing `rfl` will not unfold an ordinary `def`.** `rw [h1]` leaves
  `⊢ none = Heap.empty l` where `exact h1` closes the same goal. In `x19`'s `deep`.
- **`<;>` followed by `;`** runs the second tactic on the first goal only — two compiled instances.
- **`subst` eliminates the variable on the *right* when there is one.** `heq : l₁ = l₂` removes
  `l₂`; `heq : l₂ = l₁` removes `l₁`; `heq : l₁ = 4` removes `l₁`. All three compiled at review; the
  page states the rule rather than the single instance.
- **Author of `11-union`:** both `def`s are displayed here with one clause on `match`. Blocked
  reduction, `simp only [Heap.union]` parking and left-biasing-as-discipline are yours, and my
  closing paragraph names them without using the phrase *left-biased*. The compatibility fold does
  contain a compiled `funext` + `unfold Heap.union` + `cases hx : h₁ l with` proof about
  `Heap.union`; it is closed, captioned as your technique, and its prose says it is the one thing
  this page proves about the combination and that nothing later cites it.
- **Author of `16-star`:** `x19`'s `why` promises this theorem is why there is no contraction rule.
- **Weakest part, honestly:** `m2-1`/`m2-2` are one-liners whose rung-4 hints are the answer. The
  main-line `<;> ·` vehicle, `¬ Heap.disjoint (Heap.singleton 4 3) (Heap.singleton 4 7)`, is two
  lines of `m2-3`'s `mp` branch with concrete numbers — deliberate, since PEDAGOGY §7 wants the
  tactic before its use, but it makes `singleton_disjoint_iff` easier than [C 3] suggests. Review
  considered replacing the vehicle and kept it: specific-before-general is the better teaching, and
  the exercise still owns `by_cases`, the disequality orientation and the whole first theorem.

## Provenance and checks
Every `state` and `trace` step is `check.sh 10 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so). All 16 `code`
blocks were re-extracted by script and re-run; each `sketch` gives exactly the error quoted beneath
it, bar the statements-only one, which quotes nothing. The compatibility-commutativity
`illustration` compiles with the `def compatible` block directly above it, as on the page. Every
`pitfall`/`variants` claim was compiled separately; inline error quotes have their line breaks
removed, per `09-footprint`'s convention.

**Re-verified independently at review.** All 16 `code` blocks re-extracted and re-run: both
`verified` blocks are byte-for-byte in `lean/e2/10-disjoint.lean`, all six `illustration`s silent,
all six `sketch`es giving exactly the errors printed beneath them. All 7 `trace` blocks regenerated
with `trace_state` and diffed against the page — identical, every line. Every inline error quote
recompiled: `Nat.symm` on `hd l.symm`; the `hd l` type mismatch; the `of sort `Prop` … of sort
`Type`` message from explicit binders; the unused-variable warning on `fun l =>`; the `hx : x = l₁`
mismatch from `left` in the `pos` branch; the `Heap.singleton ?l ?v ?l` pattern failure from
`rcases hd l₁` after `rw [heq] at hd` (and `rcases hd l₂` compiling); `Unknown identifier `l`` from
using `hd` before `funext`; `⟨disjoint_symm, disjoint_symm⟩`; and `<;> rw [h1]; rfl` leaving
`case inr`.

All green: `node --check`; `lint.mjs` 45 blocks **0/0**; `ledger.mjs 10-disjoint` **0/0**;
`render-check.js` 0 problems, 7 traces; `verify.sh 10` (412 lines, 80 declarations);
`gen-contexts.mjs --prove` **38/38, 0 failed**; banned-phrase grep clean, including a widened sweep
for *obvious / naturally / indeed / crucial / essentially / notice that / observe that /
straightforward*.

*(The edition-wide `ledger.mjs --sweep` currently reports three unrowed names — `double'`,
`double'_three`, `double'_unfold` — introduced by concurrent work on `03-compute.lean`. Not from
this unit; flagged for whoever owns that fragment.)*

## What review changed
Recorded so a successor does not reintroduce any of it.

- **`Heap.union` was used before the page defined it.** The compatibility `detail` — whose second
  `illustration` is a proof *about* `Heap.union` — sat between `x19` and the `sec` that introduces
  `Heap.union` and `Heap.splits`. The flagship rule of Edition 2, broken in a fold. The fold now
  sits immediately after the definition, and its opening sentence has been rewritten to hang off the
  `match` paragraph ("The asymmetry above is there to settle what the combination holds at an address
  where both heaps are defined") instead of announcing union cold. Two consequences were repaired
  with it: the closing section said "nothing on this page proves anything about either", which the
  fold falsifies (now "Both are stated and neither is put to work", with the fold's own prose owning
  the exception), and the `unionOf` fold's "the way out is to make the operation total" now reads as
  what `Heap.union` above already did.
- **A wrong statement of what `subst` does.** "`subst` eliminates the one it can, and here that is
  `l₂`" — both sides are local variables and either is eliminable in principle. The real rule
  (right-hand side when it is a variable) is now stated, with the two other orientations, all three
  compiled.
- **Two wrong line counts** in the domains fold: "three lines" / "nine lines" for the two directions
  of the `↔`. They are four and eight.
- **An over-claim about `rw [heq] at hd`:** the main line said it "works too" in the exercise below,
  while `m2-3`'s `variants` shows it works only with the instantiation moved from `l₁` to `l₂`. The
  main line now says what it does close, and points at the cost.
- **A false universal:** "Every proof in this unit begins by choosing which address to apply `hd`
  at." Two of the four have no disjointness hypothesis. Now restricted to the proofs that have one.
- **The paragraph before `x19` gave the exercise's proof away** — "at every address the two
  disjuncts of the definition are the same statement, so disjointness with itself says directly that
  the heap is undefined everywhere". It now poses the question and stops.
- **A misattribution in `m2-3`'s `expl`:** "Unit 05's pattern". Unit 05's exercises are single `simp`
  calls; the pattern is `write_comm`'s, from Unit 06, and the two proofs agree line for line down to
  the `have`. Naming it tells the reader they have written this proof before.
- **A misattribution in `m2-2` rung 3:** `rfl` as a *term* is Unit 01's, not Unit 02's; Unit 02 gave
  the condition under which it is accepted. Both are now credited, and `Or.inl`/`Or.inr` are named
  there, which rung 3 is supposed to do.
- **A self-contradiction in `m2-2`'s `expl`:** "which is why the second one exists rather than being
  derived. Once `disjoint_symm` is available, it could be…" — `disjoint_symm` is available, one
  exercise earlier. Rewritten to say the term is kept because it is shorter and depends on nothing.
- **Three restatements of *separation implies non-aliasing* thinned to two.** The section-opening
  paragraph re-told the `write_comm` debt that the unit's second paragraph had already told, and the
  ownership paragraph ended on two sentences saying the same thing. `m2-3`'s `why` no longer repeats
  the Unit 00 sentence either.
- **`solNote` over-claim:** "the longest proof you have written" — `write_comm` is the same eight
  tactic lines. Now "two proofs and fifteen lines — the longest exercise so far".
- **`injection` was an unglossed technical noun**, used five times and introduced by no earlier
  Edition-2 unit. Glossed once, at first occurrence.
- Minor: one clause added saying a trailing `<;>` with its argument indented underneath is layout,
  not a different tactic (the reader meets the form here for the first time); "only the first goal is
  left over from the `rw`s" → "a sequenced tactic acts on the first goal only", which is the actual
  rule; the `svg` caption now says what the second colour means; "The other move is…" → "The second
  piece is the branching", matching the repaired sentence above it.
