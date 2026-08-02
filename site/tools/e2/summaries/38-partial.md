# Unit 35 · `partial` · Partial correctness, and conditionals
`site/content/38-partial.js` · 69 blocks (65 non-`ex`), 4 exercises, ~2220 words of main-line `p`,
72 KB. 11 `illustration`, 3 `verified` `code`, 1 `sketch`, 7 `state`, 5 `trace` (all in `deep`),
4 `detail`, 6 `sec`, 1 each `txt` `svg` `cmp` `note key` `note info` `dod`.
**Lean fragment untouched** — by the author and by review; §D's four exercises, `hoare_ite` and
`wp_ite` were all already there. One waiver: `ledgerForward: ['hoare_while_variant']`.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**,
and no exercise `id`, `name`, `goal`, `sol`, `walk` step or `trace`/`state` `src` was touched.*

## One job
Make the partial/total distinction real, and prove the conditional rule in both readings, so Unit 36
can be about one thing.

## The hook I left (verbatim, final block; §D word for word)
> Every rule so far was proved by looking at one derivation, or by building one. A loop's derivation
> has unknown height, and the command it is about is *fixed* while the induction wants to generalise
> it. That mismatch has a standard fix, you saw it once in Unit 26, and now it is compulsory.

Opens on `37-wand`'s hook in three words ("Use them, then").

## Introduced
**Tactics: none new.** First used inside a triple proof: `cases hbv : b.eval σ with | true | false`
— the saved-equation form, booked at `03-compute`; every earlier use in the corpus is on a heap
lookup (checked: `03-compute`, `11-union`, `12-pcm`, `28-local-heap`; the only later one is
`40-variant`, which is `x71`'s own move).
**Names now usable:** `partial_of_total`, `bTrue`, `bFalse`, `partialHoare_skip`, `partialHoare_seq`,
`partialHoare_consequence`, `partialHoare_ite`, `hoare_ite`, `wp_ite`.
**Page-only, collision-checked against all 39 fragments and every e2 page:** `spinSkip`, `ExecND`
(constructors written `.keep`/`.wipe`, warning 3), `HoareND`, `PartialHoareND`, `PartialHoareLate`,
`hoare_ite_bycases`, `iteNotVariant` (the page's one `sketch`).
**Concepts:** the two readings as `∃ x, A x ∧ B x` against `∀ x, A x → B x` · **no run ⇒ every
partial triple**, proved, with the faulting `load` discharged as an instance and the looping one
stated as the page's single un-Leaned claim · determinism as the exact hypothesis of
`partial_of_total` · **build versus invert** (`cmp`) · guards as assertions · a case split saving no
equation discovers nothing.
**Rejected alternatives, all compiled:** `bTrue` as `fact (…)` (equal by `rfl`, named anyway) ·
`∗` for `aAnd` · `bTrue (.not b)` for `bFalse b` (equivalent by `simp`, refused by `rfl`, breaks the
`iteFalse` branch) · `by_cases` and bare `cases b.eval σ` for `cases hbv :` · reversed
`exec_deterministic` arguments · `subst` for `rw` · underscores for `rename_i sMid` ·
`PartialHoareLate`, the other binder order · `ExecND`, a two-rule `skip` making `partial_of_total`
**false** · the `wp` equation for a loop, true and useless, closing the coda.

## Exercises
`x70` **partial_of_total** [D 2] — the corpus's only use of `exec_deterministic`.
`m13-1` **partialHoare_skip / _seq / _consequence** [C 2] — one quantifier flipped; `intro σ h hp`
binding a `State` is the pitfall. `m13-2` **partialHoare_ite** [D 2] — inversion hands over the
conjunct. `x71` **hoare_ite** [C 3] — the saved equation, spent twice per branch.

## Not explained (earlier summaries own them)
`Exec` and inversion · `rename_i`, `✝` · the unreduced `{store := σ, heap := h}.store` · `⟨…⟩`
flattening · `⊢`/`⊣⊢` · `wp` and its angelic reading (`34-wp`) · `pure` versus `fact` under `∗`
(`19-pure` and `26-small-footprint`) · why `induction` needs a variable index and the
constant-command idiom that repairs it (`29-local-compose` — **named, not shown; see review**).

## Warnings
1. **§D's "Inherits" is wrong**: it says the two readings coincide for the loop-free fragment. A
   faulting `load` separates them — `25-hoare`'s opening exhibit, and its summary flagged this. The
   page says they differ wherever a run may fail to exist.
2. **`ledger.mjs` does NOT fire on `partialHoare_while` cited from this unit**, while
   `loop_invariant` and `hoare_while_variant` in the same block do — verified by a controlled probe.
   The `partialHoare_` prefix is shared with three rows introduced here. So `m13-1`'s citation is
   unwaived and unpoliced. **Ledger maintainer: a real blind spot**, hitting any unit that cites a
   name extending one of its own. Do not add it to `ledgerForward`: with the checker silent the
   waiver would be reported stale (ERRATA §1).
3. **`ExecND.keep`/`ExecND.wipe` spelled out DO fire** a coverage warning; an illustration's
   inductive constructors get no row. `.keep`/`.wipe` compiles and is clean. Do that instead.
4. **Downstream, grepped and re-grepped at review: only `bTrue` and `bFalse` have consumers**
   (`39-invariant` 2/2, `40-variant` 2/3). `partial_of_total`, all four `partialHoare_*`,
   `hoare_ite`, `wp_ite`: **zero**. The `why` fields therefore claim shape, not use, except for the
   four promises that are cashable and were each re-verified against the fragments at review:
   - `39-invariant.lean:31` — `partialHoare_while` opens `intro σ h s' hI hex`, five names
     (`m13-1`'s `why`);
   - `39-invariant.lean:28–29` — its premise is `aAnd I (bTrue b)` and its conclusion
     `aAnd I (bFalse b)` (`m13-2`'s `why`);
   - `40-variant.lean:15` — `hoare_while_variant` opens `cases hbv : b.eval σ with` and spends
     `hbv` in `⟨hI, hbv⟩` and in `Exec.loopTrue hbv` (`x71`'s `why`, and the `ledgerForward`);
   - `exec_deterministic` occurs exactly once after `23-induction`, at `38-partial.lean:8`
     (`x70`'s `why`).

   If any of those four proofs changes, this page changes.
5. **Weakest part:** three of four exercises are difficulty 2, none is `hard`, and `partialHoare_ite`
   is two lines the paragraph above it predicts. §D prescribes the set.

## Deviations
65 non-`ex` blocks against §D's ~24 (ERRATA §18), prose at §D's ~4 screens; 72 KB against
`37-wand`'s 81 and `34-wp`'s 121 · 5 `trace` against §D's 2 — one per exercise plus a second for
`partialHoare_seq`, whose branch genuinely differs from `partialHoare_skip`'s (PEDAGOGY §7); all are
trimmed to new hypotheses with the title saying so, since every context here is 11–13 lines (§6.1)
and the untrimmed states sit in adjacent `detail`s · warning 1, the "loop-free fragment" claim is not
made · the coda gained three blocks (the loop `wp` equation) so the hook is earned rather than
asserted.

## Provenance and checks
Every `state`/`trace` step is `check.sh 38 <snippet> --incl` output byte for byte, `trace_state`
for mid-proof states, `snippet:L:C:` dropped, errors de-line-broken. Every quoted error came from
breaking a real proof; every `pitfall`/`variants` claim was compiled separately, both refutations
included. **All of it was re-derived from scratch at review** — the three main-line `state`s, the
four nested ones, all five `trace`s step by step, the `sketch`'s error, and every falsifiable
`pitfall`/`variants` claim (thirteen snippets), all identical to the page including metavariable
numbers (`?m.11`).

Green at review: `node --check`; `lint.mjs` **0/0** (69 blocks, 4 ex, 72 KB); `ledger.mjs` **0/0**,
sweep 3 (pre-existing: `and_assoc_iff`, `and_comm_iff`, `emp_iff_all_none`), `frags` clean;
`render-check.js` **0 problems** (5 traces); `verify.sh 38` **OK** (2189 lines, 303 declarations);
the 11 `illustration`s recompiled as one file against prelude-38 `--incl`, silent; banned-phrase
grep **0**; ERRATA §7 `<code>` grep returns `emp`, `fact`, `pure`, `subst`, `wp` only, all genuine.

## What review changed

**A forward promise the course does not keep — and a third telling of Unit 26's story.** The page
defined `spinSkip`, attempted `induction hex` on `¬ Exec spinSkip s s'`, printed the
*Invalid target: Index in target's type is not a variable* refusal, and said "**Unit 36 pays it**".
Three things wrong at once:
- **Unit 36 does not pay it.** Nothing in the corpus proves `spinSkip` diverges; `39-invariant`
  proves `loop_invariant` and `partialHoare_while` and nothing else. Checked by grep.
- **The refusal is its third appearance.** `29-local-compose`'s summary books "why `induction` needs
  a variable index" as a Unit 26 concept and `heapLocal_loop_aux` is the cure in full, eight
  `intro heq; cases heq` branches included; §D then gives *reading that error* to Unit 36 as its
  objective 1. This page was doing a successor's job with a predecessor's material.
- **It displayed `sorry` twice.** §E.1 books the displayed `sorry` at unit 24 with the note
  *"appears once, in the stranded frame proof"*.

Four blocks (`p`, `sketch`, `state`, `p`) are replaced by one `p` that states the claim, says in one
clause what a proof would take and whose move that is, and says nothing below depends on it. The
`spinSkip` definition and its always-true guard stay: the unit needs a concrete divergent command
and nothing else supplies one. **Author of `39-invariant`: the refusal and its error message are
yours, unspent.**

**An internal contradiction about when the readings agree.** The transposition paragraph says the
two "agree exactly when there is precisely one run"; four blocks later the page said "in a language
where a command has at most one run, having one good run and having no bad ones **are the same
condition**". They are not — that is precisely the case the whole page turns on. The paragraph now
reads "Determinism gives a command at most one run, so a good run is the only run there is, and the
total reading should imply the partial one", which also removes two sentences that restated the
transposition paragraph verbatim.

**Three more over-claims, each contradicted elsewhere on the page.**
- "Their proofs do not survive the change" of all three structural rules — but `m13-1`'s own `expl`
  says consequence's proof works "exactly as the total version does". Now "two of the three proofs
  turn inside out; the third does not move at all".
- "For a loop whose guard never goes false … the triple you are being asked to prove is false" —
  two blocks later the page is careful that the total triple is only refutable when something
  satisfies the precondition. The clause now says so.
- "The bottom two rows of that picture are one theorem" — they are two, one per column. Now "the two
  ticks in the bottom rows".
- `dod` claimed the reader can say of each partial structural rule "whether it builds a derivation,
  takes one apart, or never looks at one". None of the three builds one; that is the total
  counterpart. Reworded.

**Two counts that were wrong.** "Every symbol typechecks on paper and **three** of them do not
typecheck here" — the paragraph then names two (`∧` and `¬`). `m13-1`'s `solNote` said "**eight**
tactic lines"; the solution is nine.

**A banned construction (PEDAGOGY §4).** *"Three decisions are packed into those two lines, and each
has an alternative that was available."* — a paragraph whose only content is that three paragraphs
follow, which is §4's `"Two remarks about X, both important."` row. Cut; the three bolded
*Why X rather than Y* headings signal themselves.

**Lean friction in the running argument (PEDAGOGY §6.2).** A main-line paragraph explained why
`rename_i sMid` is written and what underscores would cost instead. `m13-1`'s `walk` and `variants`
already carry both, compiled. Cut.

**Two things said twice.** `x70`'s `deep` closed with the `Type mismatch: hq has type …` error and
the moral "a faithful report of a mathematical gap" — both already on the main line, four blocks
above, in better words. `m13-1`'s `deep` compared its trace's middle line with the total proof's
`obtain` — which is exactly what the main-line paragraph under the `cmp` does. Both cut; the two
`deep`s keep their traces and their compiled alternative.

**A `cmp` panel marked `kind:'good'`.** The left column is the *total* proof and the right the
partial one; neither is right-or-wrong, and the badge said otherwise. Removed.

**Three smaller repairs.** "That is the standard transposition, and it is **worth reading** as one"
— §4's `worth noting` row in disguise; now "Read it as the transposition it is". "`hbv` … is also,
**character for character**, a proof of `bTrue b σ h`" — it is not, and `x71`'s own `deep` says the
two displays differ and only the elaborator reconciles them; now "because that is what `bTrue b`
unfolds to". "Here is the equation." — a sentence announcing the block below it; cut.

**Three header fields.** The `blurb` said the readings "come apart the moment the language can fail
to finish", which is the claim the page spends its first section refuting (a faulting `load`
separates them already). `orient.payoff` called the partial reading "the reading the rest of the
course works in" — Unit 37 is total; now "the reading Unit 36 is written in". `orient.needs`
promised Unit 26's error message, which the page no longer shows.

**Checked and left alone.** All four `sol`s and `goal`s against the fragment (`m13-1`'s `goal`
carries two `sorry` stubs, which is the established multi-theorem pattern — `25-hoare` `m6-2`,
`37-wand` `x68`/`x69`, `29-local-compose` `x53`); the `cmp`'s left panel against
`25-hoare.lean`'s `hoare_seq`, byte for byte including its round brackets; the eight-line rule;
the one `detail` before the first exercise; the four-rung hints; the `wp` coda, which §D asks for;
and the exercise set, which §D fixes.
