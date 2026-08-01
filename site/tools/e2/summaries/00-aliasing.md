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
in the `cmp`, decided at Unit 13.

## Exercises
- `x01` **write a heap, prove a lookup** — a heap is a function you type out; `none` ≠ `some 0`;
  first `simp [def]`. Its Lean was ⧗ and is now in the fragment as `twoAllocated`.
- `x02` **the aliased postcondition is unsatisfiable** — `¬P` as `P → False`;
  `intro ⟨h3, _⟩`; `simp … at h` aimed at the *context*, not the goal.

## Provenance of every `state` / `trace`
All via `tools/e2/check.sh 00 <snippet> --incl` with `trace_state`: `⊢ twoAllocated 7 = none`;
the `#check`/`#eval` output block; `h3 : … / right✝ : … / ⊢ False` after `intro ⟨h3, _⟩` (used
twice); and `error: unsolved goals / x : Loc / ⊢ ¬x = 4`, real compiler output from the `sketch`
block directly above it (file:line prefix dropped). `No goals.` is the infoview's wording.

## Deviations from COURSE-PLAN.md
1. §D.0 budgets ~26 non-`ex` blocks; I ship 40, the ceiling of §C's 16–40. Not reachable at 26
   alongside §D.0's own inventory plus objective 5's symbol table and a real error message.
2. `x02`'s scaffold is a `sketch` `code` block plus a `trace`, not a third `anat`.
3. `lookup_of_unallocated` is `illustration`-only, so the fragment stays plan corpus + `x01`.

## Checks
`lint.mjs` 0/0 · `render-check.js` 0 problems · `verify.sh 00` clean · banned-phrase grep clean.
`ledger.mjs 00-aliasing` → **5 order errors, all deliberate**, reported to `ledger-checker`:
(`✝` was a sixth; `ledger-checker` moved its row to unit 00 after I reported it. §D.0 mandates
the `intro ⟨h3, _⟩` scaffold, so the real page-one state contains `right✝`; I gloss it in one
clause, because PEDAGOGY §10 forbids inventing a state.)
- `∀`, leading-dot `.write`/`.const`, `Hoare`, `ptsAtLeast`, `aAnd` — all inside the promissory
  note, which §D.0 requires verbatim and tagged `sketch`. `ledgerForward` is set but `ledger.mjs`
  honours it **only for prose `<code>` spans**, never for Lean blocks. These five recur every run.

## Warnings to successors
- `twoCells` was renamed to **`twoAllocated`** in the fragment by another agent mid-write.
- `<code>\star</code>` in prose tokenises as `star` (booked at `16-star`) and needs
  `ledgerForward`. Same trap for the English word `swap` (`33-swap`); I dropped its `<code>` tags.
- `index.html` has **no `<script>` tag** for this file; integration is a later step.
- Forward promises made by name: Units 02, 04, 13 (`↦`), 14 (`∗`), 27 (frame rule *proved*), 28.
  **Unit 28's author:** I promised the separating replacement in **four lines**, beside the
  refutation. If that number is wrong, this page must change.
- Weakest part, honestly: hint 4 of both exercises is nearly the whole answer. Deliberate (§D.0
  wants a first-timer to finish), but neither exercise measures anything; `x03` is the first that
  does.
