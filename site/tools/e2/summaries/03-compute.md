# Unit 02 · `compute` · Equality, computation, and the limits of `rfl`
`site/content/03-compute.js` · 61 blocks (58 non-`ex`), 3 exercises, ~2600 words of main-line
paragraph prose (~3800 including captions, trace commentary and the two folds).
*Reviewed and revised — see “What review changed” at the bottom.*
*Then repaired: x07 taught something FALSE in the reader's browser. See “What the two-kernel
repair changed”, and read ERRATA §28 before you write `:= rfl` after a `def` anywhere.*

## One job
Split equality in two — definitional (Lean's kernel reduces both sides to one term) versus
propositional (a statement you prove) — by building what makes reduction possible (`inductive`,
constructors, a `def` by cases) and then breaking it **twice**: on a variable, and on the keyword
the definition was declared with. And give `Option` and `if` their meanings.

The second blocker is new, and it is the whole of the repair. In the Lean the reader runs, a
`theorem` is *exported* and may not unfold a plain `def` to prove itself; an `abbrev` is reducible,
its body travels with its name, and `rfl` sees through it. So the unit now teaches, rather than
asserts, why `abbrev Heap := Loc → Option Val` is an `abbrev` — the line `00-aliasing` puts in front
of the reader two units before it can be explained.

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

**Concepts:** definitional vs propositional equality, with the rule in a `note kind:'key'` (*two
things block `rfl`: a variable in a position being cased on — the term — and a plain `def` under a
`theorem` — the keyword; the `Note:` line in Lean's message says which*) · `abbrev` as
`@[reducible] def`, and reducibility as the reason the model's five names are `abbrev`s · Lean's **kernel**, glossed in one
clause at first use · constructor distinctness and injectivity · decidability, and why `Loc := Nat`
is forced by the `if` in every heap literal · the saved equation as what ties a split's witness back
to the expression.

**Course names now usable:** `double` (a `def`), `double'` (an `abbrev` with the identical body),
`double'_unfold`, `double'_three`, `double_unfold`, `double_zero_left`, `some_inj`, `some_ne_none`,
`some_ne_none'`, `defined`, `defined_of_ne_none`, `rw_demo`, `calc_demo`. **`double_three` is gone**
— it was `double 3 = 6 := rfl`, which the reader's Lean rejects; the computing case is now
`double'_three` on the `abbrev`. `04-funext` uses `double_zero_left` in its `#print axioms` audit and
is unaffected: that theorem and its `simp [double]` proof are untouched.

## Page order (so a successor can find things)
`two_add_two` → `#print Nat` → `inductive`, constructors → `addNat`, a `def` by cases → **the rule
breaks on `addNat 0 n`** (the term blocker) → `defn` definitional vs propositional → `def double` +
`abbrev double'` → **the rule breaks again on `double n = n + n := rfl`** (the keyword blocker), with
the real browser error and its `Note:` line → the export/reducibility paragraph, and why `addNat`'s
equations are `example`s → `note` the rule, now with both blockers and the `Note:` as the
discriminator → **x07** → `rw`, its trace, `← ` and `at` → `show` → `unfold` + `have` → `simp` vs `simp only` →
`detail: calc` → `#print Option`, leading dots, `orDefault` → distinctness/injectivity →
`absurd`/`False` → **x08** → `Decidable`, the `funHeap` refusal, the `abbrev` block →
`detail: what decidability costs` → `cases hl :` vs `cases`, the `cmp` → `defined` → **x09** →
`dod` → hook.

## Exercises
- `x07` **double** [D 1] — four theorems now: `double'_unfold` and `double'_three` by term-mode
  `rfl` on the `abbrev`, then `double_unfold` — *the same statement as the first* — and
  `double_zero_left`, both by `simp [double]`. Two controlled comparisons: first against third
  isolates the keyword, first against fourth isolates the term.
- `x08` **some_inj / some_ne_none** [D 2] — `Option.some.inj h`; `by simp` versus `intro h; cases h`.
- `x09` **defined_of_ne_none** [C 3] — `cases hl : h l with`, `absurd hl hne`, `⟨v, hl⟩`.

All three `goal` fields end `:=` or `:= by`, so `assets/editor.js`'s `starterFor` appends `  sorry`
and the reader really does see what each `setup` describes. Checked against the function, not assumed.
x07's `goal` carries explicit `sorry`s under its first three statements and ends `:= by` on the
fourth, which is the same shape it had with three.

## Lean and provenance
`lean/e2/03-compute.lean`: `rw_demo`, `calc_demo`, `double` **and `double'`** + four theorems (x07),
three `some_*` (x08), `defined` + `defined_of_ne_none` (x09). **Unchanged by review; changed by the
two-kernel repair.** `verify.sh` with no argument clean; `gen-contexts.mjs --prove` 38/38 — the
`/- ex x07 -/` marker sits *below* both definitions, because the reader is handed both and writes
only the theorems, and the `/- ex x09 -/` marker sits *between* `def defined` and the theorem, both
per ERRATA §21.

**Every `state` and `trace` field is real compiler output, byte for byte**, with `trace_state` where
a mid-proof state was wanted and the position prefix dropped (the first caption says so). At review
every code block was re-extracted from the finished file and re-run and every state re-diffed; at
the repair the same was done again **through both kernels**:

- goal states and traces — `tools/e2/check.sh 03 <snippet> --incl`, and re-confirmed identical in
  the browser;
- **every error message quoted in and around x07 — `tools/e2/wasm-check.cjs`, the reader's Lean.**
  For those lines the two kernels disagree, and the reader's is the one on the page. Local Lean
  4.32.2 accepts `theorem double_unfold … := rfl` without a murmur.

Two `state` blocks were also corrected at the repair: they quoted local Lean's CLI tags
`error(lean.synthInstanceFailed):` and `error(lean.dependsOnNoncomputable):`, and the reader's
checker renders only `error:` plus the message text (`lean-runtime.js`, `parseMessages` — it reads
Lean's JSON `data` field and never sees a tag). The texts are otherwise identical in both kernels;
re-verified.

Everything else on the page — every `illustration` block, all of them — was extracted and compiled
through the reader's Lean as one file: clean. Nothing else in the unit relied on `rfl` seeing
through a `def`. The `example`s that prove `addNat`'s and `orDefault`'s equations by `rfl` are safe
**because they are `example`s**, and the page now says so in as many words rather than leaving it to
luck.

| shown | snippet compiled |
|---|---|
| `inductive Nat` / `inductive Option` / `inductive Decidable` | the three `#print` blocks themselves |
| `` Tactic `rfl` failed … ⊢ addNat 0 n = n `` | the `addNat 0 n` sketch above it |
| x07 deep: `⊢ n + n = 0 + n + n` residue | `example … := by simp only [double]` |
| main line: `Not a definitional equality … n + n` **+ its `Note:`** | `theorem double_unfold … := rfl`, in the browser |
| x07 deep: `Not a definitional equality` + `Type mismatch` pair, **and no `Note:`** | `double_zero_left … := rfl`, in the browser |
| `rw_demo` trace (2 steps) | `trace_state` around each `rw` |
| x07 deep trace (2 steps) | `trace_state` around `simp only [double]` |
| x08 deep trace (2 steps) | `trace_state` around `intro h` / `cases h` |
| x08 deep: `Function expected at Option.some_inj … ↔ …` | `Option.some_inj h` |
| `Nat.decEq : (n m : Nat) → Decidable (n = m)` + `synthInstanceFailed` | the `funHeap` sketch |
| `dependsOnNoncomputable … propDecidable` | the `open Classical in` sketch |
| the `cmp`'s two `case some` contexts | `cases hl : h l with` and `cases h l with`, `trace_state` in the `some` branch of each |
| x09 deep trace (3 steps) | `trace_state` at every step |
| x09 deep: the two `Application type mismatch` errors | the same proof with `hl :` deleted |
| x07 `variants` (seven claims: `double` → `double'`; `theorem` → `example`; `n + 0 + n` on each of the two; `n * 2`; `n * 2 = 0 + n + n`; the dropped bracket), x08 `variants` (`none ≠ some v`; `cases h` on `h : v = w` giving `case refl`), x09 `pitfall` (swapped `absurd`) and `variants` (`none ≠ h l`; the empty heap) | one snippet each, all compiled; the two error texts quoted in x09 are verbatim |

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

**Three rows moved or added at the two-kernel repair**, and this is the one place the repair touched
`ledger.json` — reported here rather than done silently:
- `double_three` **renamed to `double'_three`**, same unit, same slot, notes rewritten. The old name
  is gone from the Lean, so leaving the row would have been an orphan that `--audit` reports as
  “declared in no fragment, and no reason recorded”.
- `double'` and `double'_unfold` **added** (`kind: internal`, unit `03-compute`), because `--sweep`
  flags any declared name with no row as invisible to the order check.
- `double_unfold`'s notes rewritten: it is still declared, but its proof is now `by simp [double]`.

No *tactic* or *keyword* row moved. `simp [f]` and `abbrev` are both booked at `00-aliasing`, which
is before this unit, so the repair needs nothing to arrive early. `ledger.mjs` is 0/0 with a clean
sweep; `--audit` goes from 15 disagreements to 11.

## Deviations from COURSE-PLAN.md
0. **§D's x07 is now four theorems, not three, and one of them is on an `abbrev`.** §D specifies
   “`def double n := n + n`; close `double n = n + n` and `double 3 = 6` by `rfl`; then meet a
   sibling `rfl` cannot close”. The first half of that is not true in the Lean the reader runs; see
   ERRATA §28. The exercise keeps §D's shape — classify before you run — and gains a second reason
   for `rfl` to be refused, which is the more interesting of the two and the one that explains the
   model's own declarations. **Plan defect, not a plan deviation.**
1. **58 non-`ex` blocks against §D's ~28 and §C's 16–40 band.** §D's New Lean list here is 26 items,
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
- **`:= rfl` after a plain `def` is a trap, and `check.sh` will not catch it.** ERRATA §28. Run
  `node --stack-size=60000 site/tools/e2/wasm-check.cjs` before you hand your unit on.
- **`example` and `theorem` are not interchangeable in the reader's Lean.** An `example` exports
  nothing and may unfold anything; a `theorem` may not unfold a plain `def`. Two illustrations on
  this page (`addNat`'s equations, `orDefault`'s) are `example`s for that reason and must stay
  `example`s. The page says so out loud, so do not “tidy” them into named theorems.
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

## What the two-kernel repair changed
The defect: `def double … ; theorem double_unfold … := rfl` and `theorem double_three … := rfl`
compile in local Lean 4.32.2 and are **rejected by the Lean in the reader's browser**, which does
not expose a plain `def`'s body to an exported `theorem`. They were the only two errors in the
2281-line corpus under that kernel, and they sat in the shared context prefix, so 43 of 49
end-to-end exercise runs failed behind them. Full statement of the divergence: ERRATA §28.

What was done, and why this repair rather than the alternatives:

- **`double` stays a `def`.** Making it an `abbrev` would have fixed both lines with no other edit,
  and would have destroyed the third part of the exercise: with a reducible `double`, bare `simp`
  closes `double n = 0 + n + n` on its own (compiled, both kernels), so “`simp` has to be *told*
  that `double` is an equation it may use” — hint 3, and the `walk`'s last line — becomes false.
  `04-funext` also spends `double_zero_left` on a `#print axioms` audit that wants a `simp` proof
  and `[propext]`; that theorem and its proof are byte-identical to what they were.
- **An `abbrev double'` with the identical body joins it**, and the two `rfl`s move onto it. That
  makes the exercise a controlled comparison instead of a workaround: `double'_unfold` and
  `double_unfold` are the *same statement*, one closes by `rfl` and the other does not, and the only
  difference between them is the keyword. `twice` was the obvious name and is taken — `04-funext`
  declares `def twice (f : Nat → Nat)`.
- **The failure is shown, with the real message**, including the `Note:` line that names the
  mechanism. And a second exhibit, `double_zero_left … := rfl`, is shown *without* a `Note:` — Lean
  emits it when, and only when, exposing the definition would have fixed the goal. That gives the
  reader a discriminator between the two blockers that costs one line of reading, and it is why the
  `note kind:'key'` can now state a two-part rule instead of a one-part rule that was wrong.
- **`show`'s illustration moved from `double` to `double'`.** It compiles either way, but `show`
  restating `double n` as `n + n` two screens after the page says `rfl` may not unfold `double`
  would have read as a contradiction. `unfold double` stays on the `def`, where it belongs: it is
  one of the two ways of *asking by name*, which is the page's answer to the whole problem.
- **Not used: `@[expose]`.** It works in the browser and warns in local Lean (“`@[expose]` has no
  effect outside a `module` file”), and `verify.sh` treats any output as failure.

One thing a successor should know and the page does not say. The refusal is on **term-mode `rfl`
against a `theorem`'s stated type**; the tactic spelling `by rfl` currently slips past the same
check and closes `double n = n + n` (compiled). That is an inconsistency in the compiler, not a
distinction worth teaching, and nothing on the page depends on it either way — but a reader who
experiments may find it. If a future Lean tightens it, this page gets *more* true, not less. If one
loosens the export rule instead, the page's exhibits stop reproducing and x07 should be revisited;
`wasm-check.cjs` is what will notice.

## Checks — all green
`node --check` · `lint.mjs` 61 blocks, 0 errors, 0 warnings · `ledger.mjs 03-compute` 0/0 and
`ledger.mjs` over every e2 file 0/0, sweep clean · `render-check.js` 0 problems · `verify.sh` with
no argument clean (2286 lines, 312 declarations) · `gen-contexts.mjs --prove` 38/38 ·
**`wasm-check.cjs` over the whole corpus clean, and over x07's own spliced context clean** ·
every `illustration` block on the page compiled through the reader's Lean, clean ·
banned-phrase grep clean.
