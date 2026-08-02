# Unit 36 · `invariant` · The invariant rule
`site/content/39-invariant.js` · 64 top-level blocks (62 non-`ex`), 2 exercises, 65 KB source /
93 KB rendered, ~1905 words of main-line `p`. Top level: 33 `p`, 9 `code`, 9 `state`, 5 `sec`,
2 `ex`, 1 each `svg` `anat` `steps` `detail` `note key` `dod`; folds and `deep` add 4 `p`, 4 `code`,
3 `state`, 2 `trace`, 1 `detail`. `code` tags: 8 `illustration`, 3 `sketch`, 2 `verified`.
**Lean fragment untouched** — by the author and by review. Waivers:
`ledgerForward: ['hoare_while_variant', 'countdown_spec']`.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**,
and no exercise `id`, `name`, `goal`, `sol`, or `trace`/`state` `src` was touched.*

## One job
One theorem, `partialHoare_while`, and the technique it needs: induct on a derivation whose index
must be kept general, by adding an equation that constrains it.

## The hook I left (verbatim, final block; §D word for word)
> Partial correctness is silent about termination — and a loop that never runs satisfies every
> partial specification you can write. Buying termination back costs one natural number.

Opens on `38-partial`'s hook in three words ("Generalise, then constrain"). Checked at review:
`40-variant`'s first block opens "One natural number, and it does not go in the program", and its
`needs` cites "Unit 36: the invariant rule, and what the exit conjunct is for". The join holds.

## Introduced
**Tactics: none new.** The index-equation idiom (booked at `29-local-compose`) at full scale.
**Names now usable:** `loop_invariant`, `partialHoare_while`, `counterGuard`, `countdown`,
`countdown_keeps_cell`.
**Page-only, collision-checked against all 40 fragments and every e2 page:** `whileByCases`,
`whileDirect`, `cmdOnly` (all sketch), `guardAlwaysTrue`, `whileWeakPost`, `whileStrongBody`,
`invariantFlat`, `spinSkip_stuck`.
**Concepts:** **loop invariant** · the exit fact as what makes the rule usable · a *dead* induction
hypothesis, and the rule's premise as its replacement · generalise-then-constrain, in three moves.
**Rejected alternatives, all compiled:** `cases hex` (closes `loopFalse`, strands `loopTrue`) ·
direct `induction hex` · quantifying the command alone (**same error, other index —
`{ store := σ, heap := h }`**) · quantifying without the equation (**refuted at `skip`**) ·
reversed equation `.loop b₀ c₀ = cmd` · the folded conclusion (ruins ten branch displays) ·
`invariantFlat`, all `intro`d up front · `whileWeakPost`/`whileStrongBody`, each conjunct dropped
and each derived *from* the rule.

## Exercises
`m13-3` **loop_invariant and partialHoare_while** [C 5, `hard`] — the rule; 20 lines across the two
theorems, 20 `walk` rows.
`x72` **countdown_keeps_cell** [C 3] — four lines; `l ↦ v` reads only the heap, so the assignment
cannot move it and the guard conjunct is never spent.

## Not explained (earlier summaries own them)
`Exec`, inversion, `cases … with | ctor`, constructor no-confusion (Unit 20) · **why `induction`
needs variable indices** (Unit 26 — *named and used, not re-derived; see review*) · `✝` ·
`PartialHoare`'s binders · `bTrue`/`bFalse`, `aAnd` versus `∗` (Unit 35) · `refine` · `(I := …)` ·
structure eta and unreduced projections · `⟨…⟩` flattening.

## Warnings — every one compiled
1. **`| load =>` with no placeholder COMPILES.** A short alternative list leaves the surplus
   inaccessible; only *too long* errors (`load` expects 1, `assign` expects **0**). An early draft
   said the underscore was required. It is not. Extends `29-local-compose` warning 5.
2. **`refine partialHoare_while ?_` without `(I := …)` compiles** — `aAnd ?I (bFalse ?b)` matches.
   Do not claim Lean cannot infer it (`29-local-compose` warning 3's defect class).
3. **`cases h` on `h : c₀ = Cmd.loop b₀ c₀` succeeds** (occurs check), so that equation is
   refutable, not merely unprovable. The page claims only that `rfl` will not discharge it — which
   is the true statement about the dead IH, since the IH has arrow type and cannot be `cases`d.
4. **`cases heq` reorders the `loopFalse` context** — `hI` ends up above `hb`. Re-extract traces.
5. **Unit 35's debt is paid here**: `spinSkip_stuck` (illustration) uses `loop_invariant` with
   `I := aTrue` and an always-true guard to prove the loop has no run. Page Lean, not a fragment.
   `guardAlwaysTrue` is byte-identical to `38-partial`'s `spinSkip` guard, so
   `.loop guardAlwaysTrue .skip` *is* `spinSkip`; the caption now says so. `spinSkip` itself is
   page-only in `38-partial` and cannot be named in Lean here.
6. **`trivial` as a *tactic* has no §E.1 row.** It is used twice in this page's illustrations
   (closing `⊢ aTrue …`, i.e. `True`). Precedent: `22-exec` uses it on the page, `17-star-algebra`
   uses it as a term in the corpus. Left alone — the Lean is verified and the reader has met it —
   but **ledger maintainer: `trivial` deserves a row at 22.**
7. **Downstream, grepped:** `counterGuard`/`countdown` are consumed by `40-variant`; the three
   theorems have **zero** consumers, since `hoare_while_variant` inducts on a `Nat` and shares no
   line with this proof. Both `why` fields say that rather than promising a citation.
8. **Weakest part:** `x72` is four lines and `m13-3`'s statement is given — the reader assembles the
   strengthening rather than inventing it (`29-local-compose`'s `x53` gap; §D fixes the set).
   Nothing asks the reader to *find* an invariant, which is the skill Unit 37 needs.

## Deviations
1. 62 non-`ex` blocks against §D's ~22 (ERRATA §18); the lightest unit in the module (93 KB rendered
   against `38-partial`'s 109 and `40-variant`'s 112).
2. **§D's `trace` of the two surviving cases sits in `m13-3`'s `deep`, not the main line**, which
   shows the branch goal states and stops before the closing terms, so the full proof is not above
   the exercise asking for it (ERRATA §27). §D's failing-induction `state` and `steps` of the idiom
   are both on the main line.
3. **A second `Invalid target` exhibit added** (`cmdOnly`): after `intro σ h` the initial state is
   also a non-variable index, and §D names only the command.
4. Three main-line displays drop whole lines (captions say so; none rewritten); untrimmed forms in
   the pre-exercise `detail`. One `deep` trace step shows an 11-line goal in full.
5. `spinSkip_stuck` and the two weakenings are extra to §D — PEDAGOGY §7's rejected alternatives.
6. Three displayed `sorry`s, in the three `sketch` blocks. §E.1's note on that row ("appears once,
   in the stranded frame proof") describes unit 24; it is not a cap. `29-local-compose` ships
   `heapLocalWeak_seq_stuck` and `loopBad` the same way, and a refusal cannot be shown without one.

## Provenance and checks
Every display is `check.sh 39` output byte for byte (`--incl` where needed), `trace_state` for
mid-proof states, `snippet:L:C:` dropped (said in the first caption). The five quoted compiler
messages came from breaking real proofs; every `pitfall`/`variants` claim was compiled separately.

**Re-derived from scratch at review, all identical to the page including metavariable numbers:**
the nine main-line `state`s (probe `pA` for the `cases hex` branch, `pB` for the ten-branch induction
with `trace_state` at seven points, `pC2` — `have hmid := ihbody rfl hI` — for the `?m.303`
mismatch), the three untrimmed `state`s in the `detail`, both `trace`s step by step (`pB`, `pD`),
and fourteen falsifiable `pitfall`/`variants` claims: three-name `loopTrue`
(`Function expected at ihrest`), bare `hI` to `hbody` (`?m.303 ?m.304`), no underscores
(`Var → Val is not an inductive type`), `ihrest rfl hI`, `cases heq` before `intro heq`
(`Unknown identifier` + `?m.42`), `| assign _ =>` and `| load _ _ =>` (`Too many variable names`),
`| load =>` compiling, the reversed equation and the folded conclusion (both compiled as whole
proofs), `emp` as invariant, `exact hpre` and the skipped `cases hex` in `x72`, the `.write` body at
`v = 1` (`congrFun` at `l`) and at `v = 0` (needs `funext` + `simp`), the `whileWeakPost` route for
the dropped `bFalse` conjunct, and the increment loop proving the same triple.

Green at review: `node --check`; `lint.mjs` **0/0** (64 blocks, 2 ex, 65 KB); `ledger.mjs` **0/0**,
sweep 3 (pre-existing: `and_assoc_iff`, `and_comm_iff`, `emp_iff_all_none`), `frags` clean, no stale
waivers; `render-check.js` **0 problems**; `verify.sh 39` **OK** and bare `verify.sh` **OK**
(2327 lines, 319 declarations); the eight `illustration`s recompiled as one file against prelude-39
`--incl`, silent, and prelude-39 plus that file through `wasm-check.cjs` — **"clean — the reader's
Lean accepts all of it"** (ERRATA §28: the two `rfl` lines are `example`s, which is why they pass);
banned-phrase grep **0**. `validate.js` reports 41 pre-existing "not in the baseline" errors, one
per e2 chapter — not this unit's.

## What review changed
No ids, no names, no exercise `goal`/`sol`, no `state`/`trace` `src`, no fragment edit. Two blocks
cut, sixteen fields rewritten.

**Three claims that were false.**
- **"the first rule in the course that could not have been written the other way round."**
  `40-variant` proves `hoare_while_variant`, a *total* loop rule, and this page's own hook promises
  it two screens later. The paragraph now says the precise thing: the one premise available says
  what a single turn preserves and nothing about how many turns there are, so nothing in it builds
  a run — and *the same statement* in the total reading is not a harder theorem but a false one,
  which is what Unit 37 repairs. `40-variant` refutes exactly that statement, so the two pages now
  agree instead of contradicting.
- **An internal contradiction about where the equation lives.** The `steps` block said the equation
  "is a hypothesis of the theorem, not a side condition on the induction"; `m13-3`'s rung-1 hint
  says, correctly, "premises of the conclusion, **not** hypotheses of the theorem". The `steps`
  item now says it goes inside the statement being generalised, to the right of the derivation.
- **"taking them now would put them behind the tactic's back"** (`walk` row 1, of the equation and
  the invariant) — contradicted by this page's own `invariantFlat` fold, which `intro`s all six up
  front and compiles because `induction` auto-reverts. Both the `walk` row and the `steps` item now
  say what is true: where `intro` stops is a matter of what the `induction` line displays, not of
  what compiles. Same defect class as `29-local-compose` warning 4.

**Two counts and one tense.**
- The `skip`-branch caption said "the **four** omitted lines are the statement's binders". Five
  lines are omitted: the four binders and `cmd`. Re-counted against Lean.
- `orient.youWill` promised the `Invalid target` error "off a **third** proof". `38-partial`'s
  review deleted its `sorry`-and-refusal exhibit, so the reader has seen it once (Unit 26) and sees
  it on two proofs here. Reworded, and the main-line sentence that said "Unit 35 **met** it again"
  now says "named it again", which is what `38-partial` actually does.
- "`ihrest` … the first argument is the equation, which **at this point** is an identity" — at the
  point of the display above it, it is not; the branch's own `cases heq` makes it one. Said so.

**Three things explained twice** (PEDAGOGY §2; `29-local-compose` owns all three).
- Why `induction` needs variable indices, re-derived from "it proves a statement about every
  derivation by proving it once per rule…". Cut to the use: `Exec` has three indices and
  `induction` wants all three variable.
- Constructor no-confusion, spelled out for the third time ("two distinct constructors are never
  equal and `cases` on such an equation produces no branches at all"). Now named, with both prior
  sightings cited in one clause.
- Constructor injectivity in the `loopFalse` branch, and the `b₀`/`c₀` subscript convention. Both
  trimmed to the concrete instance; the general rule stays where Unit 26 taught it.

**Two blocks cut.**
- *"Two guards appear in that argument, and each is doing a job that shows up as a conjunct in the
  rule."* — PEDAGOGY §4's "Two remarks about X, both important." row: a paragraph whose only content
  is that two paragraphs follow, both of which open with a bold heading that signals itself.
- *"The other branch is where the loop has actually run."* — a paragraph announcing the `state`
  block whose caption already names the branch. Folded into the sentence above it as a clause.

**A solution sitting above its exercise.** The paragraph before `x72` walked the whole four-line
proof: invert the run, the heap component is unchanged, `↦` reads only the heap, the guard conjunct
is never used, two lines, no heap lemma. That is rungs 2–4 and the `expl`, printed before the reader
is asked for anything (`29-local-compose`'s repaired defect, ERRATA §27). It now states the
obligation and stops. `x72`'s rung 3 was also rung 4 with the named argument deleted; it now names
`partialHoare_while` and `refine` without arranging them, which is what §8 asks of rung 3.

**Prose.** Two "worth …-ing" constructions (PEDAGOGY §4's family, the one `29-local-compose` cut to
zero): "is worth testing rather than believing", "is worth unpacking". One "just" (§3's list).
"the same four lines prove **the same triple**" of a *different* command. "Nothing in the proof
looked" — at what. "Unit 35's **conditional theorem**", which on a page that has just proved a
conditional rule reads as `partialHoare_ite`; it is the pair of theorems about a command with no
run. "the whole of what partial correctness can say about a loop" narrowed to "as much as partial
correctness has to say", since `38-partial`'s coda exhibits a true (and useless) `wp` equation for a
loop. `m13-3`'s `why` claimed "the one theorem in this course that says something about an
unbounded computation" — `heapLocal_loop` (Unit 26) is one too; narrowed to the last rule the
partial logic is missing.

**Checked and left alone.** Both `sol`s and `goal`s against the fragment; the three `sketch` blocks
and their two error messages; all twelve `state` bodies and both `trace`s; the `anat`; the
eleven-line and sixteen-line display counts in the `detail`'s captions; the four-rung `hints` of
`m13-3`; the `pitfall` and `variants` of both exercises; the `dod`; and the exercise set, which §D
fixes.

## Weakest part, honestly
The unit's centre is a manoeuvre Unit 26 already performed in full, on a proof of the same shape
with the same eight dead branches — §D assigns it here anyway, as objectives 1–4, and the retelling
is only legitimate because of what it adds: the *second* bad index, the compiled refutation of
generalise-without-constrain, and the dead induction hypothesis whose replacement is the rule's own
premise. Those three are new and they are the best pages here. The rest of the induction is a second
telling, and a reader who did `x53` will feel it. `x72` remains four lines whose shape the page has
just argued for, so the unit rests on `m13-3`; and since `m13-3`'s statement is handed over, nothing
on this page asks the reader to invent either a strengthening or an invariant — which is exactly the
skill `40-variant`'s capstone opens by demanding.
