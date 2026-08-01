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
- **Author of `12-pcm`:** `union_eq_none.mpr` is promised by name as what associativity needs.
  **Author of `16-star`:** `x22`'s `why` promises your duplication counterexample is one line.
- **Weakest part, honestly:** `x22` is `m2-4`'s right law with one substitution, so the unit is
  measured by `x20` and `x21`; and `x20`'s rung-4 hint is the whole proof.

## Provenance and checks
Every `state` and `trace` step is `check.sh 11 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so). Two captioned
elisions: the `Explanation:` paragraph after `motive is not type correct`, and the follow-on errors
after the implicit-`h₂` failure. All ten `code`/`anat` blocks were re-extracted by script and re-run:
`anat` reports only `has already been declared`, three `illustration`s silent, six `sketch`es giving
exactly the quoted errors. Every `pitfall`/`variants` claim was compiled separately. All green:
`node --check`; `lint.mjs` 0/0; `ledger.mjs` 0/0 here and edition-wide, sweep and `frags` clean;
`render-check.js`; `verify.sh 11` and bare `verify.sh` (310 declarations); `--prove` **38/38**;
banned-phrase grep and the widened sweep clean apart from the hook's contractual "worth a name".
