# Unit 00 · `aliasing` · The rule that is false
`site/content/00-aliasing.js` · 42 blocks (40 non-`ex`), 2 exercises, ~2870 words of main-line
prose (≈4.5 screens). *Reviewed and revised — see “What review changed” at the bottom.*

## One job
Exhibit a Hoare rule that memory makes false, show the disequality repair is sound and destroys
modularity, name the move that replaces it — and get the reader's first two proofs past Lean.

## The hook I left (verbatim, final block)
> That refutation is a fact about `Option`, not about Hoare logic — there is no Hoare logic here
> yet. Before we can even write the statement we want to refute, we need to be able to write
> mathematics down at all, and Lean's answer to what a proof is turns out to be unusually simple.

## Introduced
**Tactics:** `intro` (incl. `intro ⟨h3, _⟩`) · `simp [f]` · `simp [f, h]` · `simp [f] at h` ·
`trace_state` (named in one sentence beside the first `trace`, as the way every goal state in the
course was obtained — `01-goalstate` still owns the full treatment) · `sorry` (named once in a
`txt` skeleton, banned thereafter).

**Syntax:** `abbrev` · `def` · `example` · `theorem` · `:=` vs `:= by` · explicit binder
`(x : T)`, including a proof binder `(hx : x ≠ 4)` · `Prop` (named once, as "the type Lean calls
`Prop`", in the binder callout) · `Nat` · `Option`/`some`/`none` · `if _ then _ else _` ·
`fun x => e` · `→` as a type former · `¬ P` = `P → False` · `≠`, and that `x ≠ 4` and `¬ x = 4`
are the same proposition with Lean printing the second · `∧` · `#check` · `#eval` · `⊢` and the
hypothesis context · `✝` (see below) · the abbreviations
`\to \forall \exists \and \not \ne \vdash \mapsto \star`, as a `tbl`.

**Names:** `Loc` `Val` `Heap` `Var` `Store` `aliasedAfter` `twoAllocated`; plus
`lookup_of_unallocated`, tagged `illustration`, compiled but deliberately **not** in the fragment.

**Concepts:** aliasing · memory as a function; the `Option` encoding, with the rejected
alternative (a packaged domain `D` plus a function on it) and its cost · `abbrev` versus `def` for
a type name, with the concrete cost of `def` (three elaboration failures, verified) · store vs
heap, and that only the heap is a resource · *unproved* versus *false* · ownership versus truth,
**named only** in the `cmp`, decided at `15-pointsto`.

## Exercises
- `x01` **write a heap, prove a lookup** — a heap is a function you type out; `none` ≠ `some 0`;
  first `simp [def]`. Its Lean was ⧗ and is now in the fragment as `twoAllocated`. **The name
  `twoAllocated` is fixed by the given statement**; only the stored values and the order of the
  conditionals are the reader's choice.
- `x02` **the aliased postcondition is unsatisfiable** — `¬P` as `P → False`;
  `intro ⟨h3, _⟩`; `simp … at h` aimed at the *context*, not the goal.

Both editors were checked against `assets/editor.js`'s `starterFor`: the starter really is `goal`
plus `  sorry`, so both `setup` fields describe what the reader actually sees.

## Provenance of every `state` / `trace`, and of every claim about a Lean message
All from `tools/e2/check.sh 00 <snippet> --incl`, `trace_state` where a mid-proof state was
needed. Line-and-column prefixes are dropped everywhere and every caption now says so.

| shown | how obtained |
|---|---|
| `aliasedAfter : Heap` / `some 5` / `none` | the `#check`/`#eval` block itself |
| `⊢ twoAllocated 7 = none` | `trace_state` before `simp [twoAllocated]` |
| `h3 : … / right✝ : … / ⊢ False` (used twice) | `trace_state` after `intro ⟨h3, _⟩` |
| `error: unsolved goals / x : Loc / ⊢ ¬x = 4` | compiling the `sketch` block above it |
| `error(lean.synthInstanceFailed): … OfNat (Option Val) 5 …` | `if x = 4 then 5` without `some`; only the trailing `Hint:` line dropped |
| `error(lean.unknownIdentifier): Unknown identifier \`right\` / error: expected token` | `simp [aliasedAfter] at right✝` |
| `` `simp` made no progress `` (x01 and x02 pitfalls/variants) | four separate snippets, all compiled |
| `⊢ False` residues (x01 pitfall, x01 variants, x02 variants) | compiled; the `h3 : True` state in x02's `variants` is verbatim, including the order `right✝` then `h3` |
| "three elaboration failures" for `def` instead of `abbrev` | all five `abbrev`s turned into `def`s, then `aliasedAfter`: exactly 3 `error(lean.synthInstanceFailed)` |

`No goals.` is the infoview's wording.

## Deviations from COURSE-PLAN.md
1. §D.0 budgets ~26 non-`ex` blocks; the unit ships 40, the ceiling of §C's 16–40. Prose is at
   budget (~4.5 screens against ~4); the excess is short exhibit blocks — §D.0's own mandated
   inventory (2 `anat`, `svg`, `cmp`, `note`, `dod`) plus objective 5's symbol table plus four
   real Lean messages. Reviewed and left as is: no block was found that could be cut without
   losing a verified exhibit.
2. `x02`'s scaffold is a `sketch` `code` block plus a `trace`, not a third `anat`.
3. `lookup_of_unallocated` is `illustration`-only, so the fragment stays plan corpus + `x01`.
4. §D.0's New Lean list names the abbreviations `\wand` and `\1`; the symbol table omits both.
   `−∗` is Unit 34's connective and putting it in front of the reader on page one would be a
   forward reference the prose could not honestly mark. Deliberate.

## Checks — all green
`node --check` · `lint.mjs` 0/0 · `ledger.mjs` 0/0 · `render-check.js` 0 problems ·
`verify.sh 00` clean · banned-phrase grep clean · ERRATA §7's `<code>`-collision grep returns
zero.

Getting the ledger to 0 took two rulings, both in ERRATA (**§10**, **§11**), both worth reading
before your own unit:
- `✝` is real on page one because §D.0 mandates the `intro ⟨h3, _⟩` scaffold and PEDAGOGY §10
  forbids inventing a state. Its ledger row moved to `00-aliasing`; the page owes one clause
  saying the name is not the reader's to type, and has it.
- The promissory note's forward references are waived **by name** on the chapter object:
  `ledgerAllow: ['∀', 'leading-dot name resolution (.ctor)', 'Hoare', 'ptsAtLeast', 'aAnd',
  'instance', 'where']`. The last two are not the note's: they occur inside the compiler message
  quoted verbatim in `x01`'s `deep`, and trimming them would make the quotation a paraphrase.
  Shape-row names are matched literally — copy them verbatim. `ledgerAllow` is chapter-wide; the
  only Lean `∀` in the file is in the promissory-note block. `ledgerForward` is honoured for prose
  `<code>` spans only, which is why `star` lives there and the shape rows do not.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **A false claim about the site.** The page said "every code block on this page is editable" and
  described success as "a green tick". `assets/app.js` mounts an editor **only** on `ex` blocks
  carrying a `goal`; the button reads *Check with Lean* and success reads *Lean accepts this
  proof* beside a green dot. Fixed. **If your unit describes the workbook UI, read
  `assets/editor.js` first.**
- **A wrong diagram.** The `svg`'s two annotations were positioned against the wrong arrows —
  `h 1 = some 7` sat beside the arrow leaving location 3. Redrawn: four rows, each annotated on
  its own baseline, arrows starting to the right of the text so nothing overlaps.
- **An unsupported design claim.** "`def` would make the name opaque, and you would pay for that
  on every line" — `def HeapD := Loc → Option Val` in fact costs nothing visible. Replaced with
  the verified failure (all five as `def`s → three elaboration errors on `aliasedAfter`).
- **An arithmetic overstatement.** A two-cell routine's specification was said to carry `O(n²)`
  side conditions. It carries `O(n)`; the *program's* pairwise-distinctness bookkeeping is the
  quadratic one. Both now stated separately.
- **The hook was pre-stated four blocks early.** The paragraph opening the promissory-note
  section said "a fact about `Option`, not about Hoare logic — there is no Hoare logic on this
  page", which is the contractual hook almost verbatim. Rewritten to say what `x02` fell short of
  (generality: the rule quantifies, `x02` did not) instead.
- **`x01`'s hints 3 and 4 told the reader to substitute "the name you gave your heap".** The name
  is fixed by the given statement. Fixed in `hints`, `setup` and `solNote`.
- **Ledger rows booked here but never delivered:** `Prop` and `trace_state`. Both now named, in
  one clause each.
- **A gap a beginner would stall in:** the residue `⊢ ¬x = 4` after deleting `hx : x ≠ 4`. The
  page now says the two are the same proposition and Lean prints the second.
- Error-message fidelity: the `Unknown identifier` block had lost its `(lean.unknownIdentifier)`
  tag while the other quoted message kept its tag. Restored, and every caption now states that
  the line-and-column prefix is dropped.
- Softened two overstatements: `✝` "is not a character a source file may contain" (it is not
  accepted where an identifier belongs), and "find the last colon before the `:=`" (that
  heuristic breaks on the promissory note's own statement).

## Warnings to successors
- `twoCells` was renamed to **`twoAllocated`** in the fragment by another agent mid-write.
- `<code>\star</code>` in prose tokenises as `star` (booked at `16-star`) and needs
  `ledgerForward`. Same trap for the English word `swap` (`33-swap`); its `<code>` tags are gone.
- `index.html` has **no `<script>` tag** for this file; integration is a later step.
- Forward promises the page makes by name (page prose uses §D **unit** numbers, as the plan does;
  file ids here per ERRATA §13): `03-compute` (decidable equality of `Nat`; `some` injective),
  `09-footprint`, `14-assertions`, `15-pointsto` (`↦`), `16-star` (`∗`), `21-language`,
  `25-hoare`, `30-frame` (the frame rule is *proved*, not assumed), `31-aliasing-closed`.
  **Author of `31-aliasing-closed`:** this page promises the separating replacement in **four
  lines**, standing beside the refutation — which is §D Unit 28 objective 3, so it should hold. If
  it does not, this page must change.
  §D unit 05 (`07-heap`) should know that the `Option` encoding is not merely *named* here: the
  widened codomain, the packaged-domain alternative and the cost of the alternative are all
  argued on this page. `07-heap` inherits that argument and should not re-run it.
- Weakest part, honestly: hint 4 of both exercises is nearly the whole answer. Deliberate (§D.0
  wants a first-timer to finish), but neither exercise measures anything; `x03` is the first that
  does.
