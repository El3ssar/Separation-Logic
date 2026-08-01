# Unit 00 · `aliasing` · The rule that is false
`site/content/00-aliasing.js` · 42 blocks (40 non-`ex`), 2 exercises, ~1650 words of running prose.

## One job
Exhibit a Hoare rule that memory makes false, show the disequality repair is sound and destroys
modularity, name the move that replaces it — and get the reader's first two proofs past Lean.

## The hook I left (verbatim, final block)
> That refutation is a fact about `Option`, not about Hoare logic — there is no Hoare logic here
> yet. Before we can even write the statement we want to refute, we need to be able to write
> mathematics down at all, and Lean's answer to what a proof is turns out to be unusually simple.

## Introduced
**Tactics:** `intro` (incl. `intro ⟨h3, _⟩`) · `simp [f]` · `simp [f, h]` · `simp [f] at h` ·
`sorry` (named once in a `txt` skeleton, banned thereafter). `trace_state` is *not* on the page.

**Syntax:** `abbrev` · `def` · `example` · `theorem` · `:=` vs `:= by` · explicit binder
`(x : T)`, including a proof binder `(hx : x ≠ 4)` · `Nat` · `Option`/`some`/`none` ·
`if _ then _ else _` · `fun x => e` · `→` as a type former · `¬ P` = `P → False` · `≠` · `∧` ·
`#check` · `#eval` · `⊢` and the hypothesis context · `✝` (see below) · the abbreviations
`\to \forall \exists \and \not \ne \vdash \mapsto \star`, as a `tbl`.

**Names:** `Loc` `Val` `Heap` `Var` `Store` `aliasedAfter` `twoAllocated`; plus
`lookup_of_unallocated`, tagged `illustration`, compiled but deliberately **not** in the fragment.

**Concepts:** aliasing · memory as a function; the `Option` encoding, with the rejected
alternative (a packaged domain `D` plus a function on it) and its cost · store vs heap, and that
only the heap is a resource · *unproved* versus *false* · ownership versus truth, **named only**
in the `cmp`, decided at `15-pointsto`.

## Exercises
- `x01` **write a heap, prove a lookup** — a heap is a function you type out; `none` ≠ `some 0`;
  first `simp [def]`. Its Lean was ⧗ and is now in the fragment as `twoAllocated`.
- `x02` **the aliased postcondition is unsatisfiable** — `¬P` as `P → False`;
  `intro ⟨h3, _⟩`; `simp … at h` aimed at the *context*, not the goal.

## Provenance of every `state` / `trace`
All from `tools/e2/check.sh 00 <snippet> --incl` with `trace_state`: `⊢ twoAllocated 7 = none`;
the `#check`/`#eval` output; `h3 : … / right✝ : … / ⊢ False` after `intro ⟨h3, _⟩` (used twice);
and `error: unsolved goals / x : Loc / ⊢ ¬x = 4`, real compiler output from the `sketch` block
above it, file:line prefix dropped. `No goals.` is the infoview's wording.

## Deviations from COURSE-PLAN.md
1. §D.0 budgets ~26 non-`ex` blocks; I ship 40, the ceiling of §C's 16–40 — unreachable at 26
   alongside §D.0's own inventory plus objective 5's symbol table and a real error message.
2. `x02`'s scaffold is a `sketch` `code` block plus a `trace`, not a third `anat`.
3. `lookup_of_unallocated` is `illustration`-only, so the fragment stays plan corpus + `x01`.

## Checks — all green
`lint.mjs` 0/0 · `ledger.mjs` 0/0 · `render-check.js` 0 problems · `verify.sh 00` clean ·
banned-phrase grep clean.

Getting the ledger to 0 took two rulings, both now in ERRATA (**§10**, **§11**), and both worth
reading before your own unit:
- `✝` is real on page one because §D.0 mandates the `intro ⟨h3, _⟩` scaffold and PEDAGOGY §10
  forbids inventing a state. Its ledger row moved to `00-aliasing`; the page owes one clause
  saying the name is not the reader's to type, and has it.
- The promissory note's five forward references are waived **by name** on the chapter object:
  `ledgerAllow: ['∀', 'leading-dot name resolution (.ctor)', 'Hoare', 'ptsAtLeast', 'aAnd']`.
  Shape-row names are matched literally — copy them verbatim. `ledgerAllow` is chapter-wide;
  I confirmed the only Lean `∀` in the file is in that block. `ledgerForward` is honoured for
  prose `<code>` spans only, which is why `star` lives there and these five do not.

## Warnings to successors
- `twoCells` was renamed to **`twoAllocated`** in the fragment by another agent mid-write.
- `<code>\star</code>` in prose tokenises as `star` (booked at `16-star`) and needs
  `ledgerForward`. Same trap for the English word `swap` (`33-swap`); I dropped its `<code>` tags.
- `index.html` has **no `<script>` tag** for this file; integration is a later step.
- Forward promises the page makes by name (page prose uses §D **unit** numbers, as the plan does;
  file ids here per ERRATA §13): `03-compute`, `05-update`, `09-footprint`, `14-assertions`,
  `15-pointsto` (`↦`), `16-star` (`∗`), `21-language`, `25-hoare`, `30-frame` (the frame rule is
  *proved*, not assumed), `31-aliasing-closed`. **Author of `31-aliasing-closed`:** I promised the
  separating replacement in **four lines**, standing beside the refutation. If that number is
  wrong, this page must change.
- Weakest part, honestly: hint 4 of both exercises is nearly the whole answer. Deliberate (§D.0
  wants a first-timer to finish), but neither exercise measures anything; `x03` is the first that
  does.
