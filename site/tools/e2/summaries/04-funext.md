# Unit 03 · `funext` · Functions as values
`site/content/04-funext.js` · 67 blocks (64 non-`ex`), 3 exercises, ~1780 words of main-line
paragraph prose (~2550 including captions, trace commentary and the two folds).
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Install the three-move pattern — `funext`, split on the point, close both branches — and present
function extensionality as an extra principle, by showing what it costs and what a course without
it would pay.

## The hook I left (verbatim, final block)
> You now have every tactic the next page needs. The theorems there are about updating a function
> at one point — which is, with one type changed, exactly what writing to memory will be.

The unit opens on `03-compute`'s hook (“two heaps are two *functions*, and nothing on this page can
prove two functions equal”) by **testing** it rather than accepting it: reduction turns out to close
`twice (fun n => n + 1) = fun n => n + 2` on its own, because it goes under the binder. The obstacle
is then located precisely — two different failures, only one of them new.

## Introduced
**Tactics:** `funext` (term *and* tactic) · `by_cases h : p`, with `case pos` / `case neg` ·
`<;>` · `#print axioms`.

**Library:** `congrFun` · `if_pos` / `if_neg`, whose argument is a *proof of the condition* ·
`Ne`, and that `a ≠ b` is `Ne a b`, a term recording which side is which · `Ne.symm`, also as
`hax.symm` · `propext`, `Quot.sound` and `Classical.choice`, **named only**, as what an axiom
audit reports.

**Concepts:** function extensionality as a principle reduction does not have · reduction goes
**under the binder**, so `twice (fun n => n+1) = fun n => n+2` really is `rfl` · a *family* of
equations versus one equation, and why only the second can be `rw`n with · what an axiom audit
measures · `by_cases` needs no `Decidable` instance — the `if` does — and the audit prices the
difference · `<;>` is the move to reach for exactly when the same **text** closes every branch ·
the `simp` residue `⊢ x = a → f a = f x` as an undischarged obligation.

**Course names now usable:** `twice`, `twice_succ`, `function_extensionality`, `apply_eq`,
`funext_drill`, `if_drill`, `by_cases_drill`.

## Page order (so a successor can find things)
`twice` → the `rfl` that *works* on a function equality → reduction under the binder →
**failure 1**: `0 + n` under a lambda (Unit 02's failure, wearing a lambda) → **failure 2**:
`f = g` from a pointwise hypothesis, which no lemma can reach → `defn` function extensionality →
`function_extensionality` + `anat` → **why a family is not an equation**: `rw [h]` fails,
`rw [function_extensionality h]` works → `funext` as a tactic on `twice_succ` + `trace` →
`congrFun` / `apply_eq` → `#check @funext` / `@congrFun` → the four-line `#print axioms` audit →
`detail`: type theories that leave the principle out → **x10** → the overwrite goal →
`funext x` → `by_cases`, both goals printed → `detail`: does the condition have to be decidable? →
`if_pos` / `if_neg` → `Ne`, `Ne.symm`, the wrong-way-round rewrite → **x11** → the five-line
three-move proof (`anat` + `trace`) → `simp [h]` and `<;>` (`cmp`, `note`, the divergence failure) →
the `simp` residue and the unused-argument warning → **x12** → `dod` → hook.

## Exercises
- `x10` **funext_drill** [D 2] — `funext n; simp`; that this is *not* `rfl`, and that a bare `simp`
  also passes (`deep` says why, and where that stops working).
- `x11` **if_drill** [D 2] — `constructor`, `rw [if_pos rfl]`, `rw [if_neg (Ne.symm hab)]`.
- `x12` **by_cases_drill** [C 2] — `by_cases h : y = x <;> simp [h]`; the `pos` branch needs `h`
  on the *goal*.

## Not explained (a previous summary says it is known)
`✝` (ERRATA §15) · `;` on one line and the focus dot `·` (ERRATA §17(a)) · `rw`'s silent trailing
`rfl`, `Decidable`, `Nat.zero_add`, the blocked-reduction rule (`03-compute`) · `constructor`, `∀`
as a function type, implicit binders, dot notation (`02-terms`) · `¬P` as `P → False`, `≠`, `if`,
`have`, `intro`, `simp … at h` (`00-aliasing`, `03-compute`).

## Lean and provenance
`lean/e2/04-funext.lean`: `function_extensionality`, `twice`, `twice_succ`, `apply_eq`, and the
three ⧗ exercises `funext_drill`, `if_drill`, `by_cases_drill`, each with its `/- ex … -/` marker.
**Unchanged by review.** `verify.sh 04` clean (142 lines, 38 top-level declarations); bare
`verify.sh` clean (2263 lines, 310 declarations); `gen-contexts.mjs --prove` 17/17.

**Every `state` and `trace` field is `tools/e2/check.sh 04 <snippet> --incl` output byte for byte**,
`trace_state` where a mid-proof state was wanted, the `snippet:L:C:` prefix dropped (the first
caption says so). At review **every code block was re-extracted from the finished file and re-run,
and every `state` and `trace` re-diffed against the output; all matched.**

| shown | snippet compiled |
|---|---|
| the two `` Tactic `rfl` failed `` blocks | the two `sketch` blocks above them |
| `` rewrite failed … pattern f ?x `` | `rw [h]` on `twice f = twice g` |
| `twice_succ` trace (2 steps) | `trace_state` around `funext n` |
| `@funext` / `@congrFun` signatures | the `#check` block itself |
| the four-line axiom audit | the `#print axioms` block itself |
| `split_on_nats` / `split_on_anything` audit | the `detail`'s own block |
| `⊢ (if x = a …) = f x` after `funext x`; both goals after `by_cases` | one file, `trace_state` at each point |
| `` pattern if a = x … `` (no `Ne.symm`) | the `sketch` above it |
| x10 deep: `0 + n` is not `n`; `` `simp` made no progress `` | two snippets |
| x11 trace; x11 deep's `case right` failure; the `case left.hc` pitfall | three snippets |
| the three-move `trace` (5 steps) | one file, `trace_state` at every step |
| `` pattern if ¬x = a `` after `<;> rw [if_pos h]` | the `sketch` above it |
| the `simp [hax]` residue + unused-argument warning | the `sketch` above it |
| x12 trace; the bare-`simp` residue; the compiled refutation | three snippets |
| x10 `variants` (`n + 0` is `rfl`; both sides `n + 0`), x10 deep's `[propext, Quot.sound]` claim, x11 `variants` (drop `hab`; reverse to `b ≠ a`), x12 `pitfall` (split on `x = y`), x12 `variants` (`f y` in both arms), `hax.symm`, `funext _` | one snippet each, all compiled |

Elisions, both captioned: the `Hint:`/`Note:` tail of the `unusedSimpArgs` message, and the
`file:line:column` prefix throughout. **One convention, worth stating:** where `by_cases` or
`constructor` leaves two goals, a `trace` step shows only the goal Lean would work on next; the
`state` block that *introduces* `by_cases` prints both, with a caption saying the blank line
separates them and every later tactic sees only the first. `No goals.` is the infoview's wording,
not Lean output.

## Deviations from COURSE-PLAN.md — three are plan bugs
1. **§D's `funext_drill` statement is wrong.** `(fun n => n + 0) = (fun n => n)` **is** `rfl` —
   `+` splits on its second argument. Compiled and confirmed. Changed to `0 + n`; `n + 0` becomes
   the exercise's `variants` counterexample.
2. **§D objective 6 is wrong.** `#print axioms function_extensionality` reports `[Quot.sound]`
   only — `funext` is a *theorem*, derived from quotients. `propext` appears instead on
   `double_zero_left`, a `simp` proof. The page shows a four-line audit and explains the split.
3. **§D objective 2 says “split on a decidable proposition with `by_cases`”. `by_cases` does not
   need decidability** — found and fixed at review; see below. The `if` needs it, `by_cases` does
   not, and the difference is now a `detail` with the axiom audit as evidence.
4. **`;` and `·` are not introduced here** (ERRATA §17(a)) though §D lists them.
5. **64 non-`ex` blocks against §D's ~24 and §C's 40 ceiling.** Paragraph prose is *under* budget
   (~1780 words ≈ 3 screens) and the rendered page is 88 KB, the same size as `03-compute` and
   smaller than `02-terms`. The count is 35 `code`/`state` blocks — 20 compiled exhibits, 9 of them
   failures — because this unit's method is exhibit pairs, which is what PEDAGOGY §7 asks for
   (“every rule that could be broken gets broken”). Review went looking for cuts and found three
   (below); everything else deletes a compiled exhibit or an objective. **The one thing a future
   editor could still cut** is the `#check @funext` / `#check @congrFun` pair, which costs the
   `ledgerAllow: ['Sort']` — it is kept because this unit owns both lemmas, because the two types
   side by side are the clearest statement that they are converses, and because `02-terms` dropped
   the same exhibit for the same reason, leaving the gap here. ERRATA §18 covers the count; its
   warning about early units borrowing from the summit is acknowledged.
6. `ledgerAllow: ['Sort']` — one `#check` block, caption says to read `α`, `β` as `Nat` and names
   `14-assertions` as the owner. `ledgerForward: ['update']` — `x10`'s `why` says the same opening
   heads the `update` proofs in Unit 04; no block on the page contains `update`.

## Ledger
`ledger.mjs 04-funext` 0/0; sweep clean. **Three rows added at review** to `tools/e2/ledger.json`,
all first met on this page and all previously invisible to the checker (ERRATA §19's class):
`propext`, `Quot.sound`, `Classical.choice`, all `library`, all at `04-funext`. Each is *named*
in an axiom audit and explained there; none is ever written by the reader.

## Warnings to successors
- **`03-compute`'s `x07` has a broken editor starter.** `starterFor` appends ` := by\n  sorry`
  unless `goal` ends `:=` or `:= by`; x07's ends `:= rfl`, so the reader gets
  `… := rfl := by sorry`. Not mine to fix, but it ships.
- **`lean/context.lean` and `context-index.json` are Edition-1 artefacts from July.** `--prove`
  passes but I did **not** `--write`: that installs the Edition-2 corpus over the live Edition-1
  build. Someone owns this at integration.
- **Author of `05-update`:** the residue `⊢ x = a → f a = f x` and the unused-simp-argument
  warning are both on this page with the `Ne.symm` fix beside them, so your objective 2 can start
  from recognition. `simp` alone on a lambda containing an `if` gives
  `` `simp` made no progress ``; that exhibit is here too. The five-line hand-driven proof of
  `(fun x => if x = a then f a else f x) = f` and its two-line `<;> simp [h]` twin are both on the
  page, in a `cmp`, so your objective 5 (*which style, and why*) has its two specimens already.
- **Do not write “`by_cases` needs a decidable condition”.** It does not: it falls back on the
  excluded middle and the proof then depends on `Classical.choice`. Compiled both ways; the
  `detail` on this page shows the audit. Every condition in this course *is* decidable, so nothing
  downstream changes — but the claim is false, and it was on this page until review.
- **Intra-unit ordering is not checked by anything.** `ledger.mjs` books a name to a *unit*, so a
  token introduced late in your own page may be used early in it and nothing fires. One such case
  was found here by hand (`<;>` in `x11`'s `variants`). Read your own page in order.
- **Weakest part, honestly:** `x11` and `x12` are the same conditional with and without a
  hypothesis. I made that the lesson (`x11`'s `variants`: dropping `hab` leaves a true statement
  needing `x12`'s proof), but it can be read as one exercise set twice.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **A false claim about `by_cases`.** “The condition must be decidable, which for an equation
  between `Nat`s it is, by the instance Unit 02 printed.” `by_cases h : p` on an opaque `p : Prop`
  compiles clean; the sentence was also redundant, because the paragraph two blocks earlier already
  said the *`if`* needs a decidable condition. Replaced by an accurate account of what `by_cases`
  does, plus a new `detail` — “Does the condition have to be decidable?” — whose evidence is
  `#print axioms` on two `by_cases` proofs, `[]` versus
  `[propext, Classical.choice, Quot.sound]`. That is the axiom thread returning with something new,
  which PEDAGOGY §2 requires of a returning thread.
- **`<;>` was used one exercise before it was introduced.** `x11`'s `variants` said the second
  branch “has to become `by_cases h : b = a <;> simp [h]`”, and `<;>` is not introduced until after
  `x11`. Reworded to name the two tactics in prose.
- **Two `cmp` columns were tagged `illustration`.** They are proof bodies with no theorem header
  and do not compile alone. Retagged `sketch`, matching `02-terms` and `03-compute`.
- **A `detail` paragraph duplicated the main line.** The fold's second paragraph (“every heap law
  would read `∀ x, h₁ x = h₂ x`, none could be used by `rw`…”) restated the main-line paragraph
  four blocks above it. Cut; the fold is now the genuine digression only, and retitled for it.
- **A ledger order error**: `<code>update</code>` in `x10`'s `why`. Waived by name with
  `ledgerForward`, per ERRATA §10 — the sentence openly says “in Unit 04”.
- **An overreaching claim**: “this is the only place in this course where Lean's equality and a
  mathematician's come apart”. Unverifiable and probably false. Cut.
- **A sentence restating its predecessor** (§4's last row): “…which is precisely why it is a safe
  place to watch the tactic work. **You can see what it changed without also wondering whether the
  proof depended on it.**” Merged into one clause.
- **Banned-phrase family:** “Reversing the conclusion **is worth doing once**” (the `worth …-ing`
  family that `02-terms` and `03-compute` both flagged). Rewritten. A literal §4 grep is clean;
  the widened sweep (`obvious`, `worth …-ing`, `of course`, `simply`, `just`) is clean too.
- **Grammar:** “a course in which no heap law can be rewritten with” → “in which `rw` can never be
  aimed at a heap law”.
- **A gap a beginner would stall in:** the `txt` block showing the overwrite goal named `f` and `a`
  without saying where they came from; its caption now says both are arbitrary.
- **An overstatement:** “Every function this course cares about is built with an `if`” — heaps are,
  and that is all the sentence needed. Rewritten around the heap.
- **`quotient types` was named with nothing said about it.** One clause: a construction this course
  never has to build.
- Minor: `orient.needs` listed `simp only`, which the unit never uses; the `<;>` note said the
  combinator “is available exactly when…” where it means *is the right move*; `x12`'s hint 3 said
  “the tactic that **decides** a proposition nothing in the context **decides**”; `x11`'s `deep`
  had a paragraph whose only content was announcing the `state` block under it, now folded into
  that block's caption (which also says which line produces it); `orient.youWill` and the `dod`
  both said “split on a **decidable** condition”.

## Checks — all green
`node --check` · `lint.mjs` 67 blocks, 0 errors, 0 warnings · `ledger.mjs 04-funext` 0/0 and
`ledger.mjs` over every e2 file 0/0 · `render-check.js` 0 problems (88 KB, 5 traces) ·
`verify.sh 04` and bare `verify.sh` clean · `gen-contexts.mjs --prove` 17/17 · banned-phrase grep
clean · every `code` block re-extracted and recompiled through `check.sh 04`, every `state` and
`trace` re-diffed against the output.
