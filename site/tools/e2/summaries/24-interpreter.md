# Unit 21 · `interpreter` · LAB — an interpreter, proved to agree (OPTIONAL)
`site/content/24-interpreter.js` · 89 blocks (86 non-`ex`), 3 exercises, 6 traces, ~2380 main-line
words (≈5500 counting captions, `anat` parts, `tbl` rows and `trace` commentary) plus ~5200 inside
the three exercise panels. Fragment extended by three declarations.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean fragment was edited**,
by the author or by review.*

## One job
Build a fuelled interpreter, prove it agrees with `Exec` both ways, and say plainly that nothing
later depends on any of it.

## The hook I left (verbatim, final block; word for word from §D)
> Two descriptions of the same partial function, and neither says anything about what *should be
> true* before or after a run. Nothing in this course so far mentions both a command and an
> assertion.

Opens on `23-induction`'s hook in six words ("Offer an answer and ask whether it agrees").
`25-hoare` opens on this one in four ("So write one down"), so **the final block is load-bearing
and must not be reworded.**

## Introduced
**Tactics:** `simpa … using` · `simp only [f] at h ⊢`, and `⊢` in a location list ·
`induction hle with | refl | step`.
**Syntax / library:** fuel-indexed recursion · **equation lemmas** (`#check @run.eq_4`, displayed) ·
`max`, `Nat.le_max_left`, `Nat.le_max_right` · `Nat.le` and its constructors (`#print Nat.le`) ·
`Option.map`, `Option.isSome` (inside `#eval` only, and now explained in the caption that uses
them).
**Concepts:** fuel · soundness/completeness of an implementation · **`none` is ambiguous** (fault vs
exhaustion) · iota reduction of a `match` on a constructor, and the fact that the *display* does not
reduce · **`cases h : e with` substitutes into the goal and never into a hypothesis**.
**Names now usable:** `run`, `run_sound`, `run_mono`, `run_le`, `run_complete`, `spin`,
`run_spin_none`, `spin_diverges`, `demoProg`, `demoStart`. Illustration-only: `runIf`.

## Exercises
`x47` **run_example** [D 1] — one `rfl` on a closed run; the payoff, before the hard proofs.
`m5-3` **run_sound** [C 4, hard] — nine branches; a hypothesis displaying an unreduced `match`
already *is* the equation you want.
`m5-4` **run_mono, run_le, run_complete** [C 5, hard] — `simp only … at h ⊢`, induction on a proof
of `≤`, `max` + `run_le`.

## Lean I added
Between `run` and the `m5-3` marker: `def demoProg`, `def demoStart`, and under
`/- ex x47 run_example -/` an anonymous `example : run 6 demoProg demoStart = some ⟨…⟩ := by rfl`.
Corpus 2322 lines / 318 declarations (`verify.sh 24` alone: 1257 lines, 195 declarations).
Ledger: rows for `demoProg`, `demoStart`, `Nat.le` (fenced); `run_example` and `runIf` moved
`todo` → `display`; **review added `Option.isSome` and `Option.map`, both fenced** (they had no row
at all and appear nowhere else in `site/lean/e2` or in any e2 page). **`≤` deliberately not rowed** —
§E.6 fences exactly four items and a fifth would bind every later author for a glyph §1 assumes.

## ERRATA §12 — resolved by option (a)
`runIf` **is written**: all 27 lines with `if` in both guard clauses, plus the `ite` and `loop`
soundness cases under it, compiled. **Nothing breaks** — `if true = true then _ else _` reduces, so
`exact ih c₁ s s' h` closes either way. What changes is display: Lean coerces the `Bool` to
`b = true` and inserts a `Decidable` instance. The `detail` says so, with re-derived states.

## Warnings — all compiled
1. **`theorem … := by rfl` over plain `def`s is ACCEPTED by the reader's Lean; `theorem … := rfl`
   is not.** ERRATA §28's table has only the term-mode row. Measured through `wasm-check.cjs`.
   **A new row for §28.**
2. **A multi-statement `goal` needs `sorry` under every statement but the last.** `21-language`
   says "under the first"; with three statements that left `run_le` on a bare `:= by`, so the editor
   opened on `unsolved goals`. `--prove` cannot see it — it tests the `sol`. Splice `context.lean`
   at `context-index.json[id]` and run Lean on the starter.
3. **`cases h : e with` rewrites the GOAL, not hypotheses.** In `run_mono`'s `ite` branch the goal
   becomes `(match true with …)` while `h` still says `match BExpr.eval s.store b` — hence
   `rw [hb] at h` and not `rw [hb]`.
4. **`simp [run]` and `simp only [run]` differ at exactly three branches** — `zero`, `skip`,
   `assign`, the clauses answering without a `match`, and exactly the three the corpus writes with
   `simp [run]`. All nine were run both ways; all four rows of the comparison `tbl` were
   re-extracted at review and match Lean byte for byte, `assign`'s record included.
5. **`+` works wherever `max` does** in `run_complete`; the page argues `max` on meaning and bound
   size, not necessity, and says so.
6. **Sweep noise not mine:** `and_assoc_iff`, `and_comm_iff` (`14-assertions`), `emp_iff_all_none`
   (`15-pointsto`) have no ledger row. Those fragments changed under me.
7. **`ledger.json` is uncommitted shared state and `git checkout` on it destroys other units' rows.**
   Review did exactly that and restored all five lost rows by hand (see below). Do not run
   `git checkout site/tools/e2/ledger.json`; if you must revert your own edit, edit the entry back.

## Not explained (previous summaries say it is known)
`induction`/`ih`/`generalizing`, `cases` in all its forms (I add only its effect on the goal),
`obtain`, `refine … ?_`, `subst`, `absurd`, `Option.some.inj`, `▸`, `by …` in a term argument, `✝`,
structure eta, `;;`, `Bool` vs `Prop`, `fail to show termination`, **and the shrinking condition for
a recursive `def`** — stated as a rule in `21-language`, met again in `22-exec`, so review cut this
page's third statement of it and left only what is specific to the loop clause.

## Deviations from §D
1. **86 non-`ex` blocks against ~22** (ERRATA §18). Optional unit: the cost of §C.1's mandatory lab
   shape plus two `hard` exercises, not licence. Main-line paragraphs are ~2380 words, about four
   screens against §D's three; the block count is carried by 20 `code`, 9 `state` and 6 `trace`.
2. **The worked example is the `load` branch lifted out as a standalone `example`** — it uses
   nothing from the induction (five of eight command branches do not), and extraction cuts six
   context lines. §6.1's `show` does not help here: spelling the `match` out makes the state
   *longer*, so two steps still run to ten lines. The `match` is the object of study.
3. **§D's `cmp` "relation versus interpreter" is not on the page** — its content is the opening
   `#eval Exec …` failure and the optional-unit note.
4. **§D's `detail` on `simp` vs `simp only` is a `tbl` plus main-line prose**, because the rule
   decides six of nine branches of the next exercise; folding it leaves a hole (§5's test).
5. **§C.1's "at most one sentence of prose between the exercises" is not met and cannot be.**
   The three exercises are separated by whole sections, because §D's own objectives 5–7 require
   `simp` versus `simp only`, `simpa`, `Nat.le`, `run_le` and `max` to be taught *between* `m5-3`
   and `m5-4`. Recorded rather than repaired: the alternative is asking for `run_sound` before the
   page has said what to induct on. A plan-level conflict between §C.1 and §D for this unit.

## Provenance and checks
Every `state`/`trace` is `check.sh 24 <snippet> --incl` output, or output from a prelude of
fragments 00–23 plus `def run` alone (used where `--incl` would put `run_sound` in scope);
`trace_state` for mid-proof states; position prefix dropped. **Where a state shows fewer hypotheses
than Lean printed, the dropped ones are unchanged and the block says which** — stated in the first
`state` caption and in three trace titles; line order is Lean's throughout. **Every displayed goal
now carries its `⊢` line**; review put back six that had been dropped silently in two traces, since
the stated convention covers hypotheses and did not cover the goal.
Re-verified at review, from Lean, all of it: the `Decidable (Exec …)` synthesis failure; the three
`#eval` outputs; `run.eq_4`; `#print Nat.le`; the six-step `load` trace; both `seq` contexts in the
`intro`-order `detail`; the four-step `run_sound` `seq` trace; the `run_mono` `skip` residue; the
`run_le` trace; the three-step `max` trace; the four-step `run_mono` `seq` trace; the
`run_spin_none` pair; every row of the `simp` versus `simp only` `tbl`; `x47`'s wrong-arithmetic
`rfl` failure; `m5-4`'s `simpa` type mismatch and its one-name `| step ih =>` application mismatch;
`m5-3`'s `loopFalse` metavariable mismatch; and `x47`'s `variants` arithmetic (`run 2` gives the
same answer as `run 6`; the countdown loop needs 3, is `none` at 2, and agrees at 7).
The 8 `illustration`s compile silently as one file and every quoted `#eval`/`#check`/`#print`
matches byte for byte; the 4 `sketch`es are one `#eval` whose error is quoted (minus a captioned
`Hint:` line), one clause extract, two `cmp` context lines.

Green: `node --check`; `lint.mjs` **0/0** (89 blocks); `ledger.mjs 24-interpreter` **0/0**, full-tree
`ledger.mjs` **0/0**, `--audit` 13 (all pre-existing), sweep 3 (none mine), `frags` clean, **no
waivers**; `render-check.js` 0; `verify.sh 24` (1257 lines, 195 decls) and bare `verify.sh`;
banned-phrase grep 0. `--prove` **83/83** and `wasm-check.cjs` were run by the author before review;
review changed no Lean and no exercise `goal` or `sol`, so neither was re-run.

## Weakest part, honestly
`x47` is one `rfl` whose rung-4 hint is the answer, so the unit is measured by two exercises, both
`hard`. `simpa … using` ships barely examined and is fenced, so nothing downstream will exercise it.
The `runIf` comparison ends in "nothing breaks" — true, and a weaker payoff than §D expected. And
`run_complete` is the hardest thing on the page while being the only theorem here with no branch
worked in the main line: the reader gets its statement, the `max` step that closes its `seq` case,
four hint rungs and a full `walk`, but the first complete branch they see is in the solution.

## What review changed
**No Lean fragment, no exercise `id`, `name`, `goal`, `sol` or hint rung was touched.**

- **The argument that no total interpreter exists was invalid as written.** It read: such a function
  "would answer, for every program and every input, whether that program halts. The language has
  genuine non-terminating programs … so no such function exists." Having non-terminating programs
  does not make halting undecidable — a language whose only loop is `while true do skip` has both.
  And a total function of that type *does* exist as a mathematical object; what cannot exist is a
  Lean `def`, because those compute. The paragraph now says both missing things: every `def` runs,
  and the store's unbounded naturals plus a loop are enough to encode any computation, so the
  procedure would decide the halting problem.
- **`x47`'s `why` claimed it is "the only exercise in the course whose whole content is that a
  definition *computes*".** `x07` (Unit 02) and `x40` (Unit 18) are exactly that. It now names both
  and claims what is true: this is the first where the thing that computes is a whole program run.
- **`m5-3`'s `setup` mis-counted its own solution.** "Seven of the nine branches are one or two
  lines" — three are one line, five are four, and `loop` is thirteen. Counted against the `sol` and
  corrected.
- **Six goal lines had been dropped from trace states without the convention covering it.** The
  `load` trace and `m5-3`'s `seq` trace showed steps with no `⊢` at all, while the stated convention
  names only unchanged *hypotheses*. All six restored from Lean; both traces now show the goal.
- **The retrospective's `max`-versus-`+` answer restated the main-line paragraph point for point** —
  same three claims, different words, which is PEDAGOGY §4's last row at paragraph scale. Cut from
  two paragraphs to one that answers the question and keeps only what the main line does not say
  (a thousand commands nested to depth ten need ten units).
- **One banned-phrase construction:** "It is worth seeing that the display is the only obstacle" —
  the §4 row is "It is worth noting/noticing that"; this is the same sentence with a different verb.
- **The `anat`'s first row contradicted itself**, saying the fuel comes first "because that is the
  argument the recursion runs on, and Lean looks for the shrinking argument across all of them".
  Lean's search is exactly why the order is *not* forced. It now names the ordering as a choice and
  gives its two payments, the second of which is the `intro n` that the proof section turns on.
- **`run_complete` was never stated in the main line.** The reader was told two theorems would be
  proved, shown soundness' statement, and then met completeness for the first time inside a
  difficulty-5 exercise panel. Its statement is now a `code` block where completeness is introduced.
- **Three smaller cuts:** the optional-unit note's closing sentence was addressed to a future author
  rather than to the reader; `x47`'s introduction justified its own placement; and the third
  statement in the course of the shrinking condition for a recursive `def` is gone.
- **`Option.isSome` and `Option.map` were used with no ledger row and no explanation.** The caption
  that runs them now says what each does; both have fenced rows.
- **Damage done and repaired at review:** `git checkout site/tools/e2/ledger.json` was run against
  what turned out to be uncommitted shared state, destroying five rows — `++ (list append)` and
  `List.length` (added by `23-induction`'s review) and `Nat.le`, `demoProg`, `demoStart` (added by
  this unit's author) — and reverting `runIf` and `run_example` to `todo`. All seven were restored
  by hand and the file is back to 543 rows plus the two new ones; `ledger.mjs`, `--audit` and
  `--sweep` all report exactly what they reported before. The notes on `++ (list append)` and
  `demoStart` are reconstructions and say so in the row itself; their content is taken from the two
  summaries, only the original wording is lost.
