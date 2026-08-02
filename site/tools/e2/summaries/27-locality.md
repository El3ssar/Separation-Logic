# Unit 24 · `locality` · What "local" has to mean
`site/content/27-locality.js` · 61 blocks (57 non-`ex`), 4 exercises, 84 KB, 4 `trace`, 8 `state`,
4 `detail`, 1 `svg`, 1 `anat`, 1 `cmp`. **Lean fragment untouched**; one `ledger.json` row edited.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**;
every claim re-derived from Lean, and the whole prelude-27 plus all illustrations re-run through
`wasm-check.cjs`.*

## One job
Discover *both* hypotheses of the frame rule by starting its proof with the textbook locality
condition and reading the two goals that will not close.

## The hook I left (verbatim, final block)
> Two definitions, both justified, and the frame rule they were designed for still unproved.
> Locality is a claim about `Exec`, and `Exec` has ten constructors. The three whose commands hand
> the heap back as they found it are done. The two that change it are where the argument has
> content, and each of them is a `funext` over a union.

**§D's wording is repaired twice.** "neither yet proved of a single command" contradicts §D's own
next sentence (`m8-1` proves three); and `load` *touches* the heap, it just does not change it.
Opens on `26-small-footprint`'s hook in four words ("Question (ii) is the one…").

**All three inherited questions are answered on the page**, in the order the page can take them:
(i) at the frame-rule `txt` — the conjunct the load's postcondition had and the free's precondition
did not want *is* an `R`; (ii) is `HeapLocal`; (iii) immediately after the `svg`, with
`x := allocated?(l)` — a command that reports whether an address is mapped, which breaks the
`r.store = s'.store` clause and nothing else. **`alloc` is deliberately not the example**: §D gives
allocation-breaks-locality to Unit 38, whole.

## Introduced
**Tactics and syntax: none**, as §D specifies — with one exception found at review and now
explained on the page: **term-level `show T from e`** appears in `x51`'s `sol`
(`rw [show … from by simp [Store.set]] at e0`) and occurs **nowhere else in the whole e2 corpus**.
`ledger.mjs` cannot see it, because `show` has a row at `03-compute` as a *tactic*. `x51`'s `walk`
now names the form and says why `rw` forces it. `sorry` gets its only displayed appearances.
Definitional-restatement `have h' : T := e` is used twice without ceremony — `25-hoare` spent it
already. **`28-local-heap`: you still own `.trans`.**
**Names now usable:** `HeapLocalWeak`, `HeapLocal`, `Preserves`, `HeapOnly`, `preserves_of_heapOnly`,
`heapOnly_pointsTo`, `heapOnly_emp`, `heapOnly_star`, `heapLocal_skip`, `heapLocal_assign`,
`heapLocal_load`, `not_heapOnly_pure`, `frame_needs_preserves`. Illustration-only, no fragment, no
row, collision-checked: `HeapLocalPair`, `heapLocal_pair_iff`, `PreservesBad`,
`same_assertion_two_spellings`.
**Concepts:** locality as a simulation property of the semantics · the commuting square (`svg`) ·
why the frame rule is a theorem about `Exec`, not an axiom · non-interference on the store as a
second, independent obligation · semantic versus syntactic side conditions, and why the syntactic
one is *unstatable* at `Store → Heap → Prop`.
**Rejected alternatives, all compiled:** `HeapLocalWeak` itself · `HeapLocalPair`, the
existential-free form, **proved equivalent** — so "no final state to compute" is only half the
reason; the real one is that consumers want `r` and its equations separately · `PreservesBad` and
its `Application type mismatch` · the syntactic condition (`cmp`) · dropping the disjointness
hypothesis from `HeapLocal`.

## Exercises (page order `m8-1`, `x51`, `x49`, `x50`)
`m8-1` **heapLocal_skip/_assign/_load** [C 2] — the shape three times; `union_of_some` is all of
`load`. `x51` **the store counterexample** [**G** 4] — state and refute the framed assignment.
`x49` **heapOnly_pointsTo/_emp/_star** [D 2] — two identity terms and a six-way rebuild; covers a
frame of any size. `x50` **not_heapOnly_pure** [C 4] — where the free route stops, at the same
assertion `x51` broke the rule with.

## Warnings — all compiled
1. **Downstream citations, grepped.** `HeapLocal` 9 (`28`,`29`,`30`,`34`); `Preserves` 4;
   `preserves_of_heapOnly`+`heapOnly_pointsTo` **4, always paired**; `heapLocal_load` **1**
   (`32-symbolic:77`). **ZERO: `heapOnly_emp`, `heapOnly_star`, `heapLocal_skip`,
   `heapLocal_assign`, `not_heapOnly_pure`, `frame_needs_preserves`, `HeapLocalWeak`.** The `why`
   fields say so. Do not upgrade any into a promise.
2. **The stranded proof carries TWO `sorry`s.** `HeapLocalWeak` leaves `⊢ s'.heap.disjoint hR`
   *and* `⊢ R r.store hR`; the repaired proof leaves the second. `wasm-check.cjs` reports
   `the corpus contains sorry` on any file holding them — the same file without them is clean.
3. **The disjointness gap is not refutable inside this language**: every `Cmd` satisfies the strong
   form, so there is no counterexample command. The page argues it from a compiled fact about heaps
   (writing where you do not own destroys disjointness) plus `Exec.write`'s premise.
4. **The three easy proofs never *consult* `hd` but must be *given* it.** Delete the hypothesis and
   keep the conjunct: ``don't know how to synthesize placeholder for argument `left` ``.
5. `HeapLocal` (commands) and `HeapOnly` (assertions) are two names beginning `Heap` in one unit.
   There is no `heapLocal_star`.
6. **`ledger.json`:** `HeapLocalWeak`'s stale `status: "migrate"` cleared, note rewritten (it said
   the def lives in `content/09-m8.js`). Re-dumped at `indent=1`; one hunk, still 545 rows.
7. `lint.mjs` no longer warns on a [G] placeholder `goal` that has a `sol` (ERRATA §22 says it
   does): 0/0.

## Not explained
Everything through Unit 23, in particular `Exec` and inversion, `⟨…⟩` flattening, the six slots of
`∗`, `_root_.pure`'s display, and the unreduced projection `{ store := σ, heap := h }.heap` that
`exact` accepts anyway (`01-goalstate`).

## Deviations
1. **Exercise order.** §D's objectives run counterexample (5) → `Preserves` (6) → discharge (7), and
   its `x51` row says *`Preserves` is earned, not asserted*; its table order defines it first. I
   followed the objectives. Fragment untouched, so contexts still cut at their own markers.
2. Two displayed `sorry`s, not §E.1's one (warning 2). **Both are tagged `sketch`** — the second
   was `illustration` and was retagged at review: a proof with a hole is deliberately incomplete,
   whichever hole it is, and one page cannot spell the same thing two ways.
3. 57 non-`ex` blocks against ~30 (ERRATA §18: 40 is a summit unit's floor). Below `25-hoare` (65).
4. 4 `detail`s against 2 — exactly one before the first exercise. The `HeapLocalPair` fold moved to
   *after* `m8-1` to keep that rule and to let the reader feel the cost it prices.
5. §D's `code` of `HeapLocalWeak` is an `anat`; its five callouts carry four design decisions.

## Provenance
Every `state`/`trace` step is `check.sh 27 <snippet> --incl` output byte for byte, `trace_state` for
mid-proof states, position prefix dropped. **Three main-line states show fewer lines than Lean
printed**; the convention is stated in the first `state` caption and the full text sits in the
adjacent `detail`. The 4 `illustration`s compile as one file, clean through `wasm-check.cjs`; the
`sketch` reports exactly `declaration uses \`sorry\``. Every `pitfall`/`variants` claim compiled
separately, including both `absurd … (by simp)` failures (one `` `simp` made no progress ``, one
`unsolved goals`), `¬ HeapOnly (emp ∗ pure …)` in six lines, and `frame_other_var` — the six-line
proof that framing `y = 0` onto `x := 1` **is** sound.
Green: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` unit and edition-wide **0/0**, `frags`
clean, sweep 3 (pre-existing), **no waivers**; `render-check.js` **0**; `verify.sh 27` (1460 lines,
225 decls) and bare `verify.sh` (2327/319); `--prove` **98/98**; banned-phrase grep 0.

**Re-verified at review, from scratch.** Every `state` and `trace` step in the unit was regenerated
with `trace_state` through `check.sh 27 … --incl` and diffed against the page: **all match byte for
byte**, including the two stranded goals, the 31-line `x51` state and the 18-line `assign` fold.
Every quoted error message was reproduced by breaking the real proof: the two `Application type
mismatch`es in `m8-1`'s `pitfall`, `Exec.load hl`, the `` synthesize placeholder for argument
`left` `` from dropping the disjointness hypothesis, the frame-on-the-left `Type mismatch` **and**
its `rw [union_comm (disjoint_symm hd)]` repair, `PreservesBad`'s mismatch, `x49`'s two, `x50`'s
`` `simp` made no progress ``, and `x51`'s `unsolved goals` down to the trailing `h₂`. All five
`illustration`s and the two `sketch`es recompiled. **`wasm-check.cjs`** over prelude-27 (1460 lines):
*clean*; over prelude-27 plus all five illustrations: *clean*; with the `sketch`es added it reports
only `the corpus contains sorry`, as expected. That is the check that clears `m8-1`'s four `rfl`s
and `x49`'s two identity terms against ERRATA §28, since every one of them unfolds a plain `def`.

## Weakest part, honestly
`m8-1` and `x49` are five short proofs whose rung-4 hints hand over most of the answer, so the unit
is measured by `x50` and `x51`. The commuting square is drawn once and never used again. And the
central claim — that nothing in the context reaches `⊢ s'.heap.disjoint hR` — is argued rather than
proved, because inside this language it is not refutable (warning 3). The `x := allocated?(l)`
answer to question (iii) is prose about a command that does not exist, so it is the one thing on
the page a reader cannot check in the editor; it is where it is because §D gives allocation to
Unit 38 and this unit may not spend it.

## What review changed
No Lean, no ids, no names, no hook. Two blocks added, thirteen fields rewritten.

**Contract.**
- **Question (iii) was never answered** (added `p`, after the `svg`) and **question (i) was never
  answered** (one clause added to the `p` above the frame-rule `txt`). The opening says "take
  [question ii] first", which promises the other two; the page did not keep it. (iii) also carries
  §D's *New mathematics* line — *whether locality holds depends entirely on which commands the
  language has* — which the page previously asserted in half a subordinate clause with no example.
- **The reader was dropped mid-proof.** The repaired frame proof ends on a `sorry` and the page cut
  straight to a `sec` about `Exec`'s constructors, with no sentence saying why the hole is being
  left standing. Added one `p`; it also supplies the motive for `m8-1` — a definition nothing
  satisfies is not yet a definition.

**Facts that were wrong.**
- `Assertion`'s shallow embedding was sourced to **Unit 22**; it is **Unit 12**'s
  (`14-assertions.lean:3`), which is also where `25-hoare` sources it.
- `orient.payoff` said the counterexample is a **two-line program**; `youWill`, four lines above,
  says one command, and `x51` is one command.
- **Three line-counts were invented.** The `load` state after `cases` is **15** lines (7 of them
  goal), not eighteen — eighteen is the *`assign`* state, in a different fold; and the goal goes
  from 3 printed lines to 7, not "quadrupled".
- *"no tactic removes it"*, of the projection bloat in the `assign` goal — false, and it contradicts
  PEDAGOGY §6.1, which is a rule about using `show` to do exactly that. Replaced with the true
  statement: the term is written from the definition and never reads the display.
- **`Preserves` was "a third hypothesis" in the prose and "the second hypothesis" in the `dod`.**
  Rewritten to count once and to say what kind of thing it is instead of where it sits.
- *"the first of the two places in this course where a displayed proof carries a `sorry`"* — every
  exercise `goal` is a displayed proof carrying a `sorry`. Now says "exercise stubs aside".
- **Control flow "belongs to a later unit because their premises are runs of other commands"** —
  `Exec.loopFalse`'s only premise is `b.eval s.store = false`. Re-justified on what is true of all
  five: none touches memory, and each is proved from the locality of the commands inside it.
- `frame_other_var` "in seven lines" → **six**, which is what compiles.
- `m8-1`'s `setup` said each of the three proofs is `intro`, one `cases` and one term; `load` is
  four lines, as its own rung-3 hint says.

**Reader stumbles.**
- The stuck-goal `state` shows `refine_1` and `refine_3` and never said where `refine_2` went.
- **`show T from e`** — see *Introduced*.

**Tag.** The repaired frame proof was `illustration` with a `sorry` in it; now `sketch`, like the
one four blocks above it.
