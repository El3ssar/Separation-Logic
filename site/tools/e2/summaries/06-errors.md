# §`errors` · When Lean says no
`site/content/06-errors.js` · 99 blocks, 0 exercises, ~2500 words of `p`/`note` prose (~3400 with
captions and the three folds). Support page, badge `§`. No Lean fragment; none needed.
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Twelve real Lean messages indexed by their opening words — what Lean printed, what it means, the
commonest cause, broken/fixed — plus three diagnostics and the rule that the tactic index, not the
compiler, decides what exists here.

## What I left (no hook — off the path)
Unit 04's hook passes to Unit 05 unchanged. The first block says the course does not pass through
this page. Final block, verbatim:
> Nothing on this page needs remembering. Come back to it with a message in front of you. The
> course itself resumes at Unit 05, with the thing Unit 04 said `update` could not do: give a cell
> up.

That last clause is Unit 04's own hook handed back, not a fresh preview of Unit 05 — the same move
`01-goalstate` makes with Unit 00's. **Author of `07-heap`:** the page therefore promises you
nothing except deallocation. It does *not* say memory stops being a total function (an earlier
draft did, and it contradicts `00-aliasing`'s argument that the `Option` codomain keeps it total).

## Introduced
**Diagnostic only, never in a solution:** `simp?` · `exact?` · `set_option pp.explicit true in` ·
`set_option pp.numericTypes true in` · reading `Try this:` and its `[apply]` marker.
`#print axioms` is **not** introduced here — it belongs to `04-funext` (§E.2) and is used without
ceremony; this page only says when the instrument is worth reaching for.

**Reading skills:** `Unknown identifier` vs `Unknown constant` · `Type mismatch` vs
`Application type mismatch` (whole term vs one argument) · the `?m.3 = ?m.3` twin of a failed `rfl` ·
`Invalid field` vs `Function expected` as two reports of one misplaced bracket · the *motive*, and
why an `if`'s `Decidable` instance breaks it · `ite` as what `if _ then _ else _` abbreviates, and
`rw`'s acceptance of an `↔` (one clause each, in entry 6, because both first occur there) ·
`rw` matches text, `exact` matches meaning · an eight-step stuck-reader procedure ending
"open the solution".

**No new mathematics, no new course names.** Appearing but NOT taught, waived by name: `Heap.write`
(the "does not exist yet" exhibit), `induction`/`generalizing` (one fold titled "Unit 20, not now"),
and the banned tactics quoted to show them failing.

**The twelve, numbered 1–12 in the headings and in the index table:** `Unknown identifier` ·
`Type mismatch` · `Not a definitional equality` · `Invalid field` · `unsolved goals` ·
`motive is not type correct` · `` `simp` made no progress `` · `Did not find an occurrence` ·
`Function expected` · `don't know how to synthesize implicit argument` ·
`Application type mismatch` · `has already been declared`.

**Page order.** framing + the read-the-first-message `note` → index `tbl` → `sec` The twelve →
entries 1–12, each `state` / `p` / `cmp`, with folds on 6 (the `Explanation:` paragraph), 8 (the
already-unfolded goal, and `rw` vs `exact`) and 11 (Unit 20's `generalizing`) → `sec` Three
questions (`simp?`, `exact?`, `#print axioms`) → `sec` When two terms print the same
(`pp.explicit`, `pp.numericTypes`) → `sec` Tactics that do not exist here (the `set` exhibit, the
five-row table, the `note`) → `sec` What to do when you are stuck (`steps`, eight items) → close.

## Exercises
None, per §D.10.

## Provenance
All from `tools/e2/check.sh 06`. **At review every `code`, `cmp` side and `state` was re-extracted
from the finished file by script (55 blocks), every snippet recompiled, and every `state` diffed
against that run; all matched byte for byte.** Two conventions, stated in the first caption: the
`snippet:L:C:` prefix is dropped, and a blank line separates messages one mistake produced
separately. Only entry 6's `Explanation:` paragraph is moved, into the adjacent fold, unedited.

Prose claims that carry no block, all compiled at review: bare `symm` → *identifier*; `Foo.bar` →
*identifier* but `Nat.zero_addd` → *constant*; `:= by rfl` reports as ``Tactic `rfl` failed``;
`cond_true` → `has already been declared`; and every row of the banned-tactic table (`omega`,
`decide`, `simp_arith`, `Function.funext_iff`, `linarith`), each on the goal the row now names.

## Deviations
1. **§D's message 3 does not exist as described.** "`Type mismatch` … `exact` would have worked, you
   used `rw`" in fact yields the *rewrite* message. It is entry 8's second cause, in a fold, with the
   `exact` fix. The freed slot went to `Not a definitional equality` (`rfl` on `update f x v x = v`),
   the commonest Module-0 failure and missing from the plan.
2. **§D's fixes for messages 10 and 6 are off-ledger.** `(l := 0)` needs named arguments (unit 22) —
   `@` is used instead; `subst` (unit 08) is replaced by `simp`/`by_cases`, which is what Lean's own
   "Possible solutions" line recommends.
3. **The index is a `tbl`, not a `dl`**; 99 blocks against "~40" (twelve entries × four blocks = 48
   before anything else, ERRATA §18); three `detail`s with no exercise to sit after.
4. **§D's specimen `exact?` answer is not what this prelude produces.** The plan quotes
   `Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm h))) a)`; against Units 00–04
   today the same goal answers `some_inj b a (congrArg some (id (Eq.symm h)))`. Equally absurd,
   equally correct, and it uses a course lemma, which makes the point better. Quoted from the run.

**§D's cross-reference "see §H.3" for the stuck-reader list is dangling** — §H.3 is about the
engineering load of 44 files. The procedure is mine; its last two steps quote PEDAGOGY §8.

## Warnings to successors
- **`omega` COMPILES.** PEDAGOGY §9 and §E.1 say it "does not exist here". It is Lean core, not
  Mathlib, and closes `n + 0 = n` today; `decide` closes closed propositions; `simp_arith` closes
  the goal and *then* reports the deprecation as an **error**, so the declaration still fails. Only
  `set`, `linarith`, `ring`, `aesop` give `unknown tactic`. **The ban is a course rule, not a
  compiler fact** — the page says so in a `note kind:'warn'`. `42-tactics` should copy that framing;
  whoever marks exercises should know a reader *can* submit `omega`.
- **`Unknown constant` vs `Unknown identifier` is not about the dot** — *constant* means the
  namespace resolves and the member does not. Compiled four ways.
- **`cond_true` is taken by Lean core**; a demo here had to be renamed. Short names collide with the
  library, not only the corpus.
- **`ite` and `instDecidableEqNat` first occur in the whole course on this page**, inside entry 6's
  verbatim message. Both are glossed there, in one clause. A later unit showing `pp.explicit` output
  need not re-gloss them.
- **Every `ledgerAllow` entry fires** (0 stale-waiver warnings): `Heap.write`, `update_othr`,
  `cond_true`, `induction`, `induction … generalizing`, `set`, `omega`, `linarith`, `ring`,
  `simp_arith`, `aesop`, `decide`, `Function.funext_iff`.
- **Weakest part, honestly:** entry 6's hypothesis `(y = x) ↔ True` is contrived — the page admits it
  — because nothing a Module-0 reader writes naturally produces `motive is not type correct`. If a
  later unit hits a natural one, replace this exhibit. Entry 11's induction fold is the page's only
  forward reference and gives a Unit-04 reader nothing.

## What review changed
Recorded so a successor does not reintroduce any of it.

- **A false claim about the exhibits.** "Every message on this page was produced by taking a theorem
  you have already proved and breaking it in one place" — six of them (`pointwise_symm`,
  `apply_symm`, `zero_add_fun`, `update_when_true`, `same_unfolded`, `step_down`) are theorems
  written for this page. `orient.needs` repeated the claim. Both now say what is true: the proofs are
  built out of Units 00–04, some of them theorems the reader has done.
- **The closing block invented a preview of Unit 05** — "memory stops being a total function" — which
  contradicts `00-aliasing`'s argument that the `Option` encoding keeps the function total, and
  displaced Unit 04's hook. Replaced by Unit 04's hook handed back.
- **Two things used before they existed, both in entry 6.** `@ite` appears in the quoted message and
  was not glossed until the `pp.explicit` section 200 lines later; and the broken proof rewrites with
  an `↔`, which no earlier unit shows `rw` accepting. One clause each.
- **A tag that was a false truth claim.** The three-goal `exact?` block was `illustration`; its third
  theorem does not compile, which is the whole point of it. Retagged `sketch` (the course convention
  — every other error-producing block on the page already was), and the caption says so.
- **`↓reduceIte` was re-explained.** `05-update` introduces it and says what it collapses; the
  `simp?` paragraph said it again. Cut to the two words the section needs.
- **Two table rows overstated.** `omega` "Runs, and closes the goal" reads, next to the `set_demo`
  exhibit, as a claim about `update f x v x = v` — which `omega` cannot touch. Each row now names its
  goal, and the `omega` row says what it will not do. `simp_arith` "runs, and warns" was wrong on the
  severity: the deprecation is an **error**, and the declaration fails.
- **A paragraph whose content was that another paragraph follows** (§4): "…which is the reason for the
  rule in the next paragraph." Rewritten.
- **A self-contradiction in the stuck-reader list.** The lead-in said "most of the time you never
  reach step four" while step four is *check every orientation* — which the page has just called the
  commonest mistake in the course. Now "the first two settle most of it".
- **Three statements of one rule.** Read-the-first-message was argued in the top `note`, again at the
  end of entry 10, and again as step 1. Entry 10 keeps it (it is the worked instance, four messages
  from one cause) minus its generalising clause; step 1 now points at entry 10 instead of re-arguing.
- **Banned-phrase family** (`worth …-ing`, flagged by three earlier unit reviews): "it is worth
  taking", "It is worth reading once", "the difference is worth holding on to", "most goals worth
  setting". All four rewritten. A literal §4 grep is clean and so is the widened sweep.
- **The index did not index.** Twelve rows and twelve headings with nothing tying a row to a heading.
  The entries are now numbered 1–12 in both, and the caption says the order is the same.
- **A structural mis-nesting:** "When two terms print the same" was an `h3` under the `sec` "Three
  questions you can ask Lean", so the in-page TOC showed four items under a heading that says three.
  Promoted to a `sec`.
- Minor: "the echo of something **four lines** above it" (invented precision) → "above it"; "Read the
  two blocks of text **underneath**" pointed below the paragraph when it meant inside the message
  above; five `cmp` sides carried `h:''`, which renders an empty `<p>` — four dropped, the fifth
  (entry 8's fix) given the clause it wanted; entry 6's longest sentence split in two.

## Checks — all green
`node --check` · `lint.mjs 06-errors` 99 blocks, 0 errors, 0 warnings · `ledger.mjs 06-errors` 0/0 ·
`ledger.mjs` over every e2 file 0/0 · `--sweep` clean · `render-check.js` 0 problems (76 KB) ·
`verify.sh 06` clean (180 lines, 44 declarations — no fragment was touched) · banned-phrase grep
clean · all 55 extracted blocks recompiled through `check.sh 06` and every `state` re-diffed against
the output.
