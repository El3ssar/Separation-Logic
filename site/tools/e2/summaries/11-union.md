# Unit 09 · `union` · Union, and why it must be total
`site/content/11-union.js` · 42 blocks (38 non-`ex`), 4 exercises, ~1545 words of main-line prose,
5 traces, 1 `detail` (after `m2-4`). Lean fragment **untouched**.
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Define combination of heaps, confront that the honest partial operation is unusable in a total type
theory, and hand over the three lookup lemmas without which every later proof drowns in unreduced
`match` expressions.

## The hook I left (verbatim, final block; word for word from §D)
> We have an operation and a unit. Whether they form anything worth a name depends on associativity
> and commutativity — and those two behave *completely differently*, one needing no hypothesis and
> the other false outright without one. That asymmetry has a name.

Opens on `10-disjoint`'s hook in its first sentence: "The operation that combines two heaps is
already on the page … text, and not one fact about it."

## Introduced
**Tactics:** `rwa`. First load-bearing use of `cases hl : e with`, of `by …` in a term (both
spellings, in `x21`'s `sol`), and of the implicit-vs-explicit binder *choice*.

**Syntax owned here:** **why a `match` blocks reduction** — it computes only when its scrutinee is a
constructor application. `10-disjoint` displayed the `match` and left this to me.

**Names now usable:** `union_of_none`, `union_of_some`, `union_eq_none`, `union_empty_left`,
`union_empty_right`, `union_self`. Sketch only: `unionOf`, `union_of_none_i`, `uer_bad`.

**Concepts:** left-biased total union with the discipline attached · **the register shift**
(`note kind:'key'`, contractual) · idempotence as an awkward fact about a *resource*, handed to
Unit 14 · the Unit 06 interface rule extended to `Heap.union`.

**Rejected alternatives, compiled:** `Option Heap` as the result (prose) · the proof-carrying
`unionOf` — **a different argument from `10-disjoint`'s**: theirs is that associativity cannot be
*stated*; mine is that `rw [he]` under `unionOf h₁ h₂ d` fails with `motive is not type correct`,
because `d`'s type names `h₁`. Not one theorem breaking — every rewrite.

## Exercises
- `x20` **union_of_none / union_of_some** [D 2] — rewrite the scrutinee, let the `match` compute; the
  `deep` also settles why `h₂` is explicit (all-implicit fails: `don't know how to synthesize h₂`).
- `x21` **union_eq_none** [C 3] — the only one with content; first `rwa`; traces for `mp` and `mpr`.
- `m2-4` **union_empty_left / union_empty_right** [C 2] — one is `rfl` pointwise, its mirror is not.
- `x22` **union_self** [D 1] — `m2-4`'s right law with `h` for `Heap.empty` in *both* branch lines;
  the `none` branch then ends `exact hl`, not `rfl`. That divergence is the exercise.

## Not explained (earlier summaries say it is known)
Everything in Modules 0 and 1, plus `obtain`, `absurd`, `some_ne_none`, `defined_of_ne_none`,
`Heap.disjoint` and the `unionOf` exhibit.

## Deviations from COURSE-PLAN.md
1. **38 non-`ex` blocks against §D's ~26**, inside §C's band; prose *under* budget (~2.6 screens
   against ~4). The excess is compiled exhibit pairs; §D asks for 1 `state` and there are 3, each
   half of a compiled failure. ERRATA §18.
2. `12-pcm`'s commutativity counterexample and `13-splits`'s `union_not_comm` are **not** pre-empted:
   the page shows one address where the two orders disagree (two `rfl` lines), draws no conclusion
   about commutativity, and leaves it to the hook.
3. `ledgerForward: ['disjoint_union_left']` — one named forward reference in `x21`'s `why`, whose
   sentence says outright that Unit 10 owns it. ERRATA §10's legitimate kind.

## Warnings to successors
- **`rwa` occurs exactly ONCE in the whole corpus** (`11-union.lean:18`), not twice as §E.1's note
  says. The page states the true count.
- **`Heap.union` appears in a `simp` bracket in exactly two places, both in this fragment** — grepped
  across all 39, so the closing discipline `note` is a fact.
- **`rw`'s trailing `rfl` will not unfold `Heap.empty`**, so `rw [union_of_none Heap.empty hl]`
  leaves `⊢ Heap.empty l = none` and needs a separate `rfl`.
- **`union_empty_left` needs no `funext`**: `Heap.union Heap.empty h = h := rfl` compiles (reduction
  under the binder, then eta). I quote the corpus and put the fact in `variants`.
- **`union_of_none h₂ hb` with the wrong hypothesis** reads `h₁` off `hb` and hunts for
  `h₂.union h₂ l` — an error naming a pattern the goal never held. In `x21`'s `pitfall`.
- **Author of `12-pcm`:** `union_eq_none.mpr` is promised by name as what associativity needs, and
  `x20`'s `why` promises your unit proves associativity, commutativity *and* cancellation with the
  two lookup lemmas. **Author of `16-star`:** `x22`'s `why` promises your duplication (`starNoDisj_dup`)
  is a single `exact` once `union_self` exists.
- **Counts that were checked, not estimated, and that a later edit must keep true:**
  `union_of_none`/`union_of_some` occur **42** times after this fragment (12-pcm 12, 28-local-heap 11,
  33-swap 6, 16-star 1, 27-locality 1 — by occurrence, not by line); `union_eq_none` is used in
  **two** theorems of `12-pcm`, once in `union_assoc` and three times in `disjoint_union_left`;
  `union_empty_left`/`_right` close **four** of `17-star-algebra`'s nineteen theorems (the two `emp`
  laws and their two intro forms). The page states each of these; none is rounded up.
- **Unit 10 does NOT carry a disjointness hypothesis everywhere.** `union_assoc` and
  `disjoint_union_left`/`_right` have none; only `union_comm` and `union_cancel_left` do. The
  register-shift `note` used to claim otherwise and now does not — see "What review changed".
- **Unit 06's unfolding ban covers three operations, not four.** `Heap.empty` is carved out
  (`08-heap-laws`'s summary; `15-pointsto.lean:22` and `22-exec.lean:44` unfold it). The closing
  `note` names the three.
- **Weakest part, honestly:** `x22` is `m2-4`'s right law with one substitution, so the unit is
  measured by `x20` and `x21`; and `x20`'s rung-4 hint is the whole proof.

## Provenance and checks
Every `state` and `trace` step is `check.sh 11 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so). Two captioned
elisions: everything Lean prints after `motive is not type correct` (the `Explanation:` paragraph,
the `Possible solutions:` line and the unchanged goal), and the follow-on errors after the
implicit-`h₂` failure. All ten `code`/`anat` blocks were re-extracted by script and re-run:
`anat` reports only `has already been declared`, three `illustration`s silent, six `sketch`es giving
exactly the quoted errors. Every `pitfall`/`variants` claim was compiled separately.

**Re-checked at review, independently.** All twenty-nine Lean-bearing fields (`code`, `anat`, `state`,
`trace`, `goal`, `sol`) were re-extracted by script and re-run through `check.sh 11 --incl`; all five
`trace` blocks were regenerated with `trace_state` and diffed against the page — **identical, byte for
byte, including the context reordering in `case mp.some`, where `v : Val` prints after `h` before the
rewrite and before `h` after it**. Every
`pitfall`/`variants` claim was recompiled as its own snippet: `simp only [hl]` and `simp [hl]` both
report `` `simp` made no progress ``; `simp [hl, Heap.union]` compiles; the altered `union_of_some`
reduces to `⊢ False` at address 4; `union_of_none h₂ hb` hunts for `h₂.union h₂ l`; `by_cases` in
`x21`'s `mp` leaves `hl : ¬h₁ l = none` and the untouched goal; all three `x21` alternative endings
(`some_ne_none v`, `cases h`, the reversed conjunction) compile; `cases h l with` gives
`Unknown identifier \`hl\`` on **both** branch lines; `Heap.union Heap.empty h = h := rfl` compiles;
`x22` at a fixed `l` compiles without `funext`; the `Heap.singleton 0 1` refutation of the left law
compiles.

All green: `node --check`; `lint.mjs` 0/0 (42 blocks, 4 ex, 57 KB); `ledger.mjs 11-union` 0/0 and
edition-wide 0/0, sweep and `frags` clean; `render-check.js` 0 problems; `verify.sh 11` (451 lines,
86 declarations); banned-phrase grep and the widened sweep (`obvious`, `worth …-ing`, `just`,
`simply`, `essentially`, `it turns out`, first person plural) clean apart from the hook's
contractual "worth a name" and its contractual "We have an operation".

## What review changed
Recorded so a successor does not reintroduce any of it. The Lean was not touched; every fix is prose.

- **The register-shift `note` contradicted the unit's own hook.** It said "every lemma from Unit 10
  onwards carries an explicit `hd : Heap.disjoint h₁ h₂`", while the closing block promises that
  associativity needs no hypothesis — and `12-pcm.lean` bears the hook out: `union_assoc` and
  `disjoint_union_left`/`_right` carry none. The note now says a lemma that *genuinely needs* the two
  heaps not to overlap carries one, that the caller discharges it, and that making the requirement
  visible is what lets you ask of any theorem whether it has one. The clause about the six theorems
  on this page is unchanged and still true.
- **`x20`'s `setup` described the second theorem wrongly**, and contradicted its own `variants`:
  "the first with `none` replaced by `some v` throughout". `union_of_none` concludes `= h₂ l`,
  `union_of_some` concludes `= some v`, and `variants` exists to say that stating the second with
  `h₂ l` on the right makes it **false**. The setup now describes the two theorems as the two
  branches of the `match`.
- **Three overstated forward claims.** `x20`'s `why`: "Units 24, 25 and 30 do almost nothing else" —
  Unit 24 cites the lemmas **once**; now Unit 25 and Unit 30, with Unit 10's cancellation added,
  which is real. `x21`'s `why`: "Unit 10 needs it twice — once in the middle branch of associativity"
  — it is the branch where *both* left-hand heaps are silent, and `disjoint_union_left` uses it three
  times; both corrected. `orient.payoff`: "close half the assertion laws of Unit 15" — four of
  nineteen; now "four of Unit 15's assertion laws". (`emp` was **not** used as the name: it is
  Unit 13's notation.)
- **"hundreds of citations ahead"** for the binder discussion. Forty-two. Counted.
- **A cost claimed twice over.** The `by_cases` column said `defined_of_ne_none` plus `obtain` is
  "two extra lines, in every proof"; it is one line (`obtain ⟨v, hv⟩ := defined_of_ne_none h l hl`),
  and the second cost is the goal-rewriting the value split does for free. Compiled both the
  six-line and a five-line compact `by_cases` proof to check. The illustration's caption and the
  `dod` both said "two lines" and now name what is actually spent — the `obtain` line and the
  trailing `, hl` / `, hv` rewrite entries.
- **A wrong count in a `solNote`:** "One line against five". The proof bodies are one and **four**.
- **A false statement in the opening paragraph:** "no tactic you have will move it". `rw [hl]` moves
  it the moment the definition is open, which is the whole exercise four blocks later. Cut; the
  accurate version ("`simp only`, `rw` and `unfold` all leave that same goal") was already on the
  page where it belongs.
- **Unit 06's unfolding ban was mis-stated** as covering "the four heap operations". `Heap.empty` is
  carved out of it (`08-heap-laws`'s summary is explicit, and two later fragments unfold it). The
  closing `note` now names `Heap.write`, `Heap.erase` and `Heap.singleton`.
- **A counterexample stated in the wrong direction.** `x22`'s `variants` said replacing "one of the
  two heaps" by an unrelated `h'` falsifies the theorem, then compared against the right-hand
  argument — but `Heap.union (singleton 4 3) (singleton 4 7) = singleton 4 3` is **true**. Now
  stated as `Heap.union h h' = h'`, with the orientation named.
- **`x22`'s `setup` said "exactly one line differs"** from `union_empty_right`. Both branch lines
  differ; only one *stops closing*. Rewritten to say that, which is also a better exercise.
- **The `detail` re-derived `m2-4`'s `expl`, and `m2-4`'s `variants` re-derived the `detail`.** The
  fold's first two paragraphs restated "`Heap.empty l` is `none`, so the `match` takes its second
  branch"; `variants` separately re-derived reduction-under-the-binder. Merged: the fold now owns the
  under-the-binder argument (and says it is why the term-mode `rfl` compiles), `variants` states the
  fact and points at the fold.
- **`simp`'s bracket was explained a fourth time**, in `x20`'s rung-3 hint, for a reader who has used
  `simp [f, h]` since Unit 00. Cut to naming the tactic and the one property that is load-bearing
  here. "Unit 02's saved-equation form" appeared three times; the two in hints are gone, the
  main-line introduction stays.
- **Three sentences restating their predecessors**, cut or merged: the "three things to settle"
  roadmap in the second paragraph (whose third item is not a section of this page); the tail of the
  left-biasing paragraph ("a convenience with a discipline attached, and the discipline is the
  disjointness hypothesis carried at every use site" — the `note` two blocks later says exactly
  that); and the reason clause in "Firing it at the goal *before* the definition is unfolded does
  nothing, because …", which the state block's own caption supplies.
- Minor: "visible in the arithmetic" said of two lookups; `orient.needs` booked `intro` with a
  pattern to Unit 01 (the `⟨…⟩` intro-pattern ledger row is at Unit 00).
