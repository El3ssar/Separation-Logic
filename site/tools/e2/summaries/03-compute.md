# Unit 02 · `compute` · Equality, computation, and the limits of `rfl`
`site/content/03-compute.js` · 55 blocks (52 non-`ex`), 3 exercises, ~2350 words of main-line
paragraph prose (~3500 including captions, trace commentary and the two folds).
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Split equality in two — definitional (Lean's kernel reduces both sides to one term) versus
propositional (a statement you prove) — by building what makes reduction possible (`inductive`,
constructors, a `def` by cases) and then breaking it on a variable; and give `Option` and `if`
their meanings.

## The hook I left (verbatim, final block)
> `Heap` is a type now, and it has no operations. The smallest useful one changes what is stored at
> one address and leaves every other address alone — and writing it will show you that `rfl` was
> never going to be enough here, because two heaps are two *functions*, and nothing on this page can
> prove two functions equal.

`04-funext` opens on it (“Two heaps are two functions… Unit 02 left that as an obstacle”), so the
join is confirmed from both sides.

## Introduced
**Tactics:** `rfl` *as a tactic* and its limit · `rw [h]` · `rw [← h]` · `rw … at h`, and the
silent trailing `rfl` · `simp only [f]` (first shown inside x07's `deep`, then developed in the
main line, which back-references x07) · `show` · `unfold` (and that it does **not** try `rfl`) ·
`have h : T := e`, anonymous `have` / `this` · `cases hl : e with | none => … | some v => …`
(the saved-equation form) · `cases h` on an equation between distinct constructors (zero goals).
**`show`, `unfold` and `have` are all main line** — see “What review changed”.

**Syntax / keywords:** `inductive` and its constructor list · pattern-matching `def`
(`| pat, pat => e`, no `match`), and that `0`/`m + 1` are the spellings of `Nat.zero`/`Nat.succ m` ·
leading-dot constructor names (`.none`, `.some v`) · a `by` block standing where a term is wanted ·
`calc … := h` / `_ = c := h` · `#print` (glossed against `#check`) · `Decidable` ·
`instance` (named, not written) · `open Classical in`, `noncomputable` (both inside one `detail`,
as costs).

**Library:** `Option.some.inj` · `congrArg` · `absurd` · `False` (as *the inductive with no
constructors*) · `Nat.decEq` · `Nat.zero_add`.

**Concepts:** definitional vs propositional equality, with the rule in a `note kind:'key'` (*a
variable in a position being cased on is what blocks reduction*) · Lean's **kernel**, glossed in one
clause at first use · constructor distinctness and injectivity · decidability, and why `Loc := Nat`
is forced by the `if` in every heap literal · the saved equation as what ties a split's witness back
to the expression.

**Course names now usable:** `double`, `double_unfold`, `double_three`, `double_zero_left`,
`some_inj`, `some_ne_none`, `some_ne_none'`, `defined`, `defined_of_ne_none`, `rw_demo`, `calc_demo`.

## Page order (so a successor can find things)
`two_add_two` → `#print Nat` → `inductive`, constructors → `addNat`, a `def` by cases → **the rule
breaks on `addNat 0 n`** → `defn` definitional vs propositional → `note` the rule → `double` →
**x07** → `rw`, its trace, `← ` and `at` → `show` → `unfold` + `have` → `simp` vs `simp only` →
`detail: calc` → `#print Option`, leading dots, `orDefault` → distinctness/injectivity →
`absurd`/`False` → **x08** → `Decidable`, the `funHeap` refusal, the `abbrev` block →
`detail: what decidability costs` → `cases hl :` vs `cases`, the `cmp` → `defined` → **x09** →
`dod` → hook.

## Exercises
- `x07` **double** [D 1] — two `rfl`s and one `simp [double]`; classify an equation before running it.
- `x08` **some_inj / some_ne_none** [D 2] — `Option.some.inj h`; `by simp` versus `intro h; cases h`.
- `x09` **defined_of_ne_none** [C 3] — `cases hl : h l with`, `absurd hl hne`, `⟨v, hl⟩`.

All three `goal` fields end `:=` or `:= by`, so `assets/editor.js`'s `starterFor` appends `  sorry`
and the reader really does see what each `setup` describes. Checked against the function, not assumed.

## Lean and provenance
`lean/e2/03-compute.lean`: `rw_demo`, `calc_demo`, `double` + three theorems (x07), three `some_*`
(x08), `defined` + `defined_of_ne_none` (x09). **Unchanged by review.** `verify.sh 03` clean (111
lines, 31 top-level declarations); `gen-contexts.mjs --prove` proves all nine exercises in the
course, including the three here — the `/- ex x09 -/` marker sits *between* `def defined` and the
theorem, per ERRATA §21.

**Every `state` and `trace` field is `tools/e2/check.sh 03 <snippet> --incl` output byte for byte**,
with `trace_state` where a mid-proof state was wanted and the `snippet:L:C:` prefix dropped (the
first caption says so). At review every code block was re-extracted from the finished file and
re-run, and every state and trace was re-diffed against the output; all matched.

| shown | snippet compiled |
|---|---|
| `inductive Nat` / `inductive Option` / `inductive Decidable` | the three `#print` blocks themselves |
| `` Tactic `rfl` failed … ⊢ addNat 0 n = n `` | the `addNat 0 n` sketch above it |
| x07 deep: `⊢ n + n = 0 + n + n` residue | `example … := by simp only [double]` |
| x07 deep: `Not a definitional equality` + `Type mismatch` pair | `double_zero_left … := rfl` |
| `rw_demo` trace (2 steps) | `trace_state` around each `rw` |
| x07 deep trace (2 steps) | `trace_state` around `simp only [double]` |
| x08 deep trace (2 steps) | `trace_state` around `intro h` / `cases h` |
| x08 deep: `Function expected at Option.some_inj … ↔ …` | `Option.some_inj h` |
| `Nat.decEq : (n m : Nat) → Decidable (n = m)` + `synthInstanceFailed` | the `funHeap` sketch |
| `dependsOnNoncomputable … propDecidable` | the `open Classical in` sketch |
| the `cmp`'s two `case some` contexts | `cases hl : h l with` and `cases h l with`, `trace_state` in the `some` branch of each |
| x09 deep trace (3 steps) | `trace_state` at every step |
| x09 deep: the two `Application type mismatch` errors | the same proof with `hl :` deleted |
| x07 `variants` (five claims), x08 `variants` (`none ≠ some v`; `cases h` on `h : v = w` giving `case refl`), x09 `pitfall` (swapped `absurd`) and `variants` (`none ≠ h l`; the empty heap) | one snippet each, all compiled; the two error texts quoted in x09 are verbatim |

The only elision is the trailing `Hint:` line of the two `synthInstanceFailed` messages, captioned.
`No goals.` is the infoview's wording, not Lean output.

## Ledger
`ledgerAllow: ['cases … with | ctor']` and `ledgerForward: ['pointsTo_value_unique']`; both still
load-bearing, neither stale. `ledger.mjs 03-compute` is 0/0.

Four rows **added at review** to `tools/e2/ledger.json`, all first introduced on this page and all
previously invisible to the checker (same class as `Or.elim` at `02-terms`, ERRATA §19):
`Nat.decEq`, `Nat.zero_add` (both `library`), `open Classical`, `noncomputable` (both `keyword`).
`Nat.zero_add` matters beyond this unit — `04-funext` names it in prose. `absurd`, `congrArg`,
`Option.some.inj`, `calc`, `#print` and `False` already had rows; the previous summary's warning
that they did not is **withdrawn**.

## Deviations from COURSE-PLAN.md
1. **52 non-`ex` blocks against §D's ~28 and §C's 16–40 band.** §D's New Lean list here is 26 items,
   the largest in Module 0, and PEDAGOGY §7 wants each with a before/after; the count is exhibit
   pairs (`code` + `state`), not prose, and paragraph prose is at budget (~2350 words ≈ 4 screens). Review
   went looking for cuts and found none that did not delete a compiled exhibit or an objective;
   three blocks were *added* (see below) because two objectives were only reachable through a closed
   fold. Recorded rather than fixed. ERRATA §18's ruling covers it, and its warning about early
   units borrowing from the summit is acknowledged: this is the largest unit in Module 0 and should
   stay that way.
2. **`Nat.beq` and `Bool` dropped.** `Bool` is booked at `21-language`, so `Nat.beq`'s type cannot
   be shown honestly. `Nat.decEq` and `#print Decidable` carry the lesson. **Plan gap.**
3. **No `detail` on the dependent-pair alternative to `Option`.** `00-aliasing` argues it (its
   summary says so, and instructs `07-heap` not to re-run it); a third pass would be a loop.
4. **No `anat` on `Option`** (§D's size line asks for one). `#print Option` plus one paragraph does
   the dissection, and the page's single `anat` is spent on `calc_demo`, which has no other home.
5. `calc` is taught, per ERRATA §17(b), inside the `detail` "Putting the intermediate terms on the
   page". `calc` occurs in **no other fragment in the corpus**, so the fold is the right place for
   it; `show`, `unfold` and `have`, which later units do use, are not in it.

## Warnings to successors
- **`ledgerAllow: ['cases … with | ctor']`.** x09's `deep` shows the proof with the `hl :` deleted,
  to print the two errors that causes; `cases h l with | none =>` is token-identical to the
  inversion form booked at `22-exec` — ERRATA §7's first collision, hit for real. **Author of
  `22-exec`:** the token has appeared; nothing about inversion has been taught.
- **`unfold` does not try `rfl`**; `rw` does. Verified, and stated in the main line.
- **`Option.some_inj` exists and is an `↔`**; `Option.some.inj` is the implication. x08's `pitfall`
  quotes the real error.
- **`show` is introduced as a readability device only.** §E books its first load-bearing use at
  unit 22 (`25-hoare`). Nothing between here and there needs it.
- **Weakest part, honestly:** x07 and x08 are drills whose rung-4 hints are the answer, so the unit
  is measured by x09 alone; and the `Decidable` section is the one place where the reader is told a
  mechanism (instance search) rather than shown one, because writing an `instance` is not on this
  unit's ledger row.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **`rfl` was called a “two-letter proof”** in the unit's first sentence. It has three letters.
- **`show`, `unfold` and `have` were in a closed `detail` together with `calc`.** §D objective 5
  requires `have`, `orient.youWill` promised it, and §E's first *use* of both `have` and `unfold` is
  unit 04 (`05-update`) — so a reader who never opened the fold was stranded one unit later, and
  `04-funext`'s `needs` list already assumes `have`. `unfold` and `have` are now a main-line
  paragraph plus their (unchanged, recompiled) code block, with the `unfold`-does-not-try-`rfl` trap
  in the open; the fold now holds `calc` alone and is retitled for it. Cost: two blocks. The
  previous summary's warning to `05-update`'s author is **withdrawn** — nothing needs re-introducing.
- **One paragraph carried five ideas** (distinctness, injectivity, `congrArg`, `absurd`, `False`).
  Split in two, and the missing step restored: `¬ P` is `P → False`, so `hn h` *is* an inhabitant of
  `False`, and `False` is an `inductive` with an empty constructor list — which ties `absurd` back to
  the machinery this unit had just built instead of asserting it.
- **Two counts that were wrong or unverifiable.** “a complete definition of the natural numbers and
  it is **four lines** long” (the display is five lines and the definition proper is three) and “the
  same **four-line** shape as `Nat`”. Both now say what the shape *is* — a name and a list of ways to
  build a value — which is the point either way.
- **`#print` was used without being introduced**, though §D's New Lean list books it here. One
  caption, saying what it answers that `#check` does not.
- **A gap a beginner would stall in:** `addNat`'s patterns are `0` and `m + 1` while the prose talks
  about `zero` and `succ`, and nothing said they were the same two constructors. One clause in the
  caption.
- **“the kernel” was used three times, unglossed.** `02-terms`' review removed the word for exactly
  this reason. Glossed once, in the `defn`, and left standing thereafter.
- **A caption re-stated Unit 00's conclusion** that only the heap is a resource. Replaced by
  something this page earns: `Var := Nat` is the *same* decidability decision as `Loc := Nat`.
- **Banned-phrase family:** “**The obvious** objection” (§4's `Obviously` row; `02-terms`' review
  flagged the same family) and “not with one **obvious** goal”. Both rewritten. A literal §4 grep is
  clean; the widened sweep (`obvious`, `worth …-ing`, `it turns out`, `essentially`) is clean too.
- Minor: “easy to leave out and **expensive to leave out**” (the same phrase twice in one clause);
  “Now **note** which argument” → “Now look at”; x08's `cmp` said “one word” / “two words” of things
  that are tactics, and tinted the *delegated* column `kind:'good'` although the page prefers the
  other one — the tint is gone; `orient.needs` now names `intro` and `¬ P` as `P → False`, which x08
  uses; `orient.youWill` now names `unfold`, which the `dod` already claimed.

## Checks — all green
`node --check` · `lint.mjs` 55 blocks, 0 errors, 2 warnings (x07 and x08 have multi-theorem `goal`
fields, expected) · `ledger.mjs 03-compute` 0/0 and `ledger.mjs` over every e2 file 0/0 ·
`render-check.js` 0 problems · `verify.sh 03` clean · `gen-contexts.mjs --prove` 9/9 ·
banned-phrase grep clean.
