# Unit 32 · `listrep` · Lists in the heap
`site/content/35-listrep.js` · 52 blocks (48 non-`ex`), 4 exercises, 73 KB / 101 KB rendered.
4 `trace` (all in `deep`), 3 `state`, 7 `code` (5 `illustration`, 2 `sketch`), 2 `detail` (one main
line, the one PEDAGOGY §5 allows before the first exercise; one inside `m10-3`'s `deep`), 1 each
`svg` `anat` `txt` `note key` `dod`.
**Lean fragment untouched — by the author and by review.** One `ledger.json` row added at review.
*Reviewed and revised — see "What review changed" at the bottom. **No Lean was edited at review**;
all four traces, all three `state` blocks and all six quoted compiler errors were re-derived from
Lean and diffed against the page (0 unmatched), the five illustrations were recompiled as one file
through local Lean **and** through the reader's Lean, and every falsifiable `pitfall`/`variants`
claim was compiled.*

## One job
Define a recursive assertion, and make the reader see that it says *shape* and *ownership* in one
breath.

## The hook I left (verbatim, final block; §D word for word)
> A predicate for a <i>complete</i> list. A traversal splits a list into the part already visited
> and the part remaining, and neither of those is a complete list.

Opens on `34-wp`'s hook in four words ("Take the obstruction literally"), counting cells off the
text: *n* copies of `↦` constrain *n* cells, so the assertion must be produced by a function.

## Introduced
**Tactics, notation: none.**
**Syntax:** recursive `def` returning an `Assertion`, with `List` patterns (my §E.2 row) · the
**bracket list literal** `[10, 20, 30]`, which no earlier page writes — see warning 9 and the new
ledger row.
**Names now usable:** `node`, `listRep`, `listRep_nil`, `listRep_cons_unfold`, `listRep_cons_fold`,
`listRep_cons_ne_zero`, `node_cells_distinct`, `concrete_list`.
**Illustration/sketch-only, collision-checked:** `listRepAnd`, `listRepLoop`, `walkStep`; every
other page snippet is an anonymous `example`.
**Concepts:** recursive predicates · **the double reading** (`note kind:'key'`) · null as address 0
as a modelling convention · least fixed points, and why the question does not arise when the
recursion is over an already-inductive object (`detail`).
**Rejected alternatives:** `Option Loc` for the next field (prose — it changes `Heap`'s codomain) ·
length-indexing instead of contents (prose) · `aAnd` for `∗` (`listRepAnd`, duplicated in one
line) · non-structural recursion (`listRepLoop`, real error) · an *equation* rather than three
entailments as the fold/unfold interface (`m10-1`'s `variants`, with the browser's refusal quoted).

## Exercises
`m10-1` **the three fold/unfold lemmas** [D 1] — three `entails_refl _`; naming an identity buys
diagnosis, not proof. `x65` **listRep_cons_ne_zero** [D 2] — the seven-slot `intro`; a `fact`
travels between heaps for free. `m10-2` **node_cells_distinct** [D 1] — Unit 17's promise kept, one
line, no arithmetic. `m10-3` **concrete_list** [C 4, hard] — five cuts, and the rhythm.

## Not explained (earlier summaries say it is known)
`∗`'s slots and `intro` pattern · why the non-null conjunct is `pure` and not `fact` (Unit 23) ·
`_root_.pure` in displays · `✝` · `refine` · `subst` · `⟨…⟩` flattening · `union_empty_left`
reducing (Unit 15, and its page says so in as many words) · `Ne`/`Ne.symm` (Unit 03).

## Warnings — every one compiled or grepped
1. **ZERO downstream citations for all six declarations here** (word boundaries, `36-*`…`41-*`).
   `node` occurs once and `listRep` three times, all in `36-lseg.lean`. `m10-1`'s `why` says so.
   **Do not upgrade any into a promise.** `36-lseg`'s `lseg_listRep` uses the `cons` reduction
   *silently*, without citing `listRep_cons_unfold`; the page says that rather than pretending.
   At review three fields that contradicted this (`solNote`, a `walk` step, a `variants` bullet, all
   saying the fold and the unfold are "cited in different places") were rewritten to say they are
   *for* different jobs.
2. **ERRATA §28 does not bite `entails_refl _`, and does bite `:= rfl`.** Prelude-35 `--incl` plus
   all five illustrations is clean through `wasm-check.cjs`. The same identity stated as an
   **equation** and proved `:= rfl` is **rejected** in the browser and accepted locally — recompiled
   at review, message quoted in `m10-1`'s `variants` byte for byte. §28 covers term-mode `rfl`
   against a `theorem`'s stated `Eq`; do not generalise it.
3. **§D's stated pitfall for `m10-3` is wrong.** Without the `subst`s the proof compiles, two lines
   shorter, with `hu`/`hu'` in the equation slots; `union_assoc` never appears. Shipped as a
   `detail` in `deep`. What `subst` buys is the goal *display*.
4. **§D objective 2 credits the `∗`s with excluding a lasso.** Both halves do it, by different
   routes, and the page says both — and, since review, says *which* second: the `∗`s stop an address
   recurring, and the `pure`s make the last next field's target both `0` (the `nil` clause) and
   non-zero (the `cons` clause that produced it).
5. **A wrong node layout shows up as vacuity, not a failed proof.** `(p ↦ v) ∗ (p ↦ n)` still
   admits `two_cells_distinct p p x next`, concluding `p ≠ p`, and it **compiles**.
6. `rfl` fills all three left-hand equation slots of `m10-3` and fails on the one right-hand slot
   (`h₄ = h₄.union Heap.empty`, metavariable `?m.212`). Both recompiled at review.
7. **Author of `41-beyond`:** the page exhibits `Cmd.load`'s literal `Loc` (a `.plus` there reports
   `Unknown constant Loc.plus` **and** `Unknown constant Nat.plus` — two lines, both quoted) and
   promises your unit the one-line `Cmd` change and the argument that everything between survives it.
8. **`fail to show termination` is NOT displayed here for the first time.** `22-exec` shows it in
   full for `runBad`, with parameters #1 and #2 dissected. A pre-review caption on this page said
   Unit 19 "named and did not need" it; it needed it — the message is why the semantics is a
   relation. The caption now says this is the same complaint about different arguments.
9. **The bracket list literal was used before it was introduced.** `23-induction` teaches `List`,
   `[]` and `::` and writes no multi-element literal anywhere (grepped across all e2 pages); this
   page opens with `listRep [10, 20, 30] p` in `orient`, and `orient.needs` claimed the literal was
   "met there". Both repaired: one clause in the main line gives `[10, 20, 30]` = `10 :: (20 :: (30
   :: []))`, `needs` says the literal is new here, and `ledger.json` gains a `check:false` `syntax`
   row at `35-listrep`. **`check:false` is not laziness** — no regex separates a list literal from
   `simp [f, h]` or `rw [hu, he]`, which are on every page from unit 00.
10. **Weakest part, honestly:** three exercises are difficulty 1–2 and two are one-term proofs whose
    rung-4 hint is the answer, so the unit is measured by `m10-3` alone. The double reading, its real
    content, is measured by no exercise; §D's table prescribes the set, so it cannot be fixed here.
11. **§D says "five cuts" and the proof makes six** (three empty-on-the-left, two node-versus-tail,
    and the `nil` case's empty-on-the-right). The page follows §D's count throughout — `why`,
    `solNote`, the section intro and the trace title all say five — and the `walk` names the sixth
    as "the only cut in the proof that puts the empty heap on the right". Left alone at review
    rather than contradict §D; a successor renumbering this should renumber all four places.

## Deviations
1. **48 non-`ex` blocks against §D's ~26** (ERRATA §18); 101 KB rendered, mid-pack for Modules 7–8
   (88–141 KB). Review read the whole main line against PEDAGOGY §4 looking for cuts and removed one
   announcing clause; everything else earns its place as a rejected alternative, a compiled
   refutation or a required objective.
2. §D asks 1 `trace`; there are 4, all in `deep`. `m10-3`'s shows **goal lines only**, the 14-line
   context printed once in an adjacent `state`, the elision stated in the trace title
   (`33-swap`'s precedent). Every line is real.
3. §D's `m10-3` pitfall replaced — warning 3.
4. Two `detail`s, not one: the second is inside `m10-3`'s `deep`, so PEDAGOGY §5's "at most one
   before the first exercise" holds.

## Provenance
Every `state`/`trace` step is `check.sh 35 <snippet> --incl` output byte for byte, `trace_state` for
mid-proof states, `snippet:L:C:` dropped, in-sentence errors de-line-broken. The `listRepLoop`
message is truncated by **five** lines and its caption now says five (it said three; the dropped
block is a two-line legend, a two-line table and the `termination_by` suggestion, and the table row
carries a prelude line number). Illustrations were re-extracted from the shipped page and compiled
as one file; both `sketch`es give exactly the errors beneath them.
**Every `pitfall`/`variants` claim was compiled separately** — eleven, including all six quoted
messages, all re-derived at review.

Green after review: `node --check`; `lint.mjs` **0/0** (52 blocks); `ledger.mjs` **0/0** for this
file and edition-wide, sweep 3 (pre-existing) and `frags` clean, no waivers; `render-check.js` **0**;
`verify.sh 35` (1974/276); `wasm-check.cjs` on prelude-35 `--incl` + all 5 illustrations **clean**;
banned grep **0**.

## What review changed
**No Lean, no exercise `id`, `name`, `goal`, `sol` or hint rung, no `trace`, no `state` `src`.**
One `ledger.json` row added (warning 9). Everything else is prose: one `needs` item, two captions
and nine fields.

**Facts that were wrong.**
- **"Replace each `∗` by `aAnd`, keep everything else"**, directly above a `listRepAnd` that also
  replaces both `pure`s by `fact`. The prose contradicted the code under it. It now says what the
  change costs and why: with `pure` under a conjunction that never divides, the `emp` half forces
  the whole heap empty and the `cons` case becomes uninhabited — compiled at review as
  `listRepAndPure … ⊢ aFalse`.
- **"Change the layout of a node … and these three statements stop typechecking."** They do not:
  `listRep_cons_unfold` writes `node p x next` on *both* sides, so any body for `node` reduces
  identically. Replaced by three changes that really do break them — moving the non-null conjunct,
  reordering the two stars, re-aiming the existential.
- **"The `pure` conjuncts … keep the chain finite"**, contradicted two blocks later by the
  `detail`, which derives finiteness from `List` being inductive. The paragraph now claims what the
  `pure`s actually do (they say where the chain ends) and gives the lasso argument in full instead
  of gesturing at it.
- **`x65`'s `why`: "where the choice of `pure` over `fact` in the definition pays".** Backwards —
  a bare `fact` in the definition would make the extraction *easier*. What `pure` buys is exactness;
  what makes the one-line proof work is that the *conclusion* is `fact`. Both now said, in one
  sentence each. The matching sentence in `variants` ("the whole reason the non-nullness claim is
  stated with `pure`") was repaired the same way.
- **`m10-1`'s `variants` misattributed Unit 12's objection to equality** and then gave a reason that
  argues the other way ("an equation is rewritten with, and rewriting under a `∗` is what
  `star_congr` … exist for"). Unit 12's objection has two parts; the page now names both and says
  which one bites here — the `funext`/`propext` bill does not, because this equation is a
  definitional identity, and the "you only ever want one direction" half does.
- **Three fields said the fold and the unfold are "cited" in different places** while `m10-1`'s
  `why` says, correctly and checkably, that nothing in the course cites either. Warning 1.
- **"Unit 19 named and did not need" `fail to show termination`.** Warning 8.
- **`orient.needs` claimed the bracket literal was met at Unit 20.** Warning 9.
- **The `walkStep` `state` caption explained one of the two errors it quotes.** Lean tries
  `Loc.plus` and then `Nat.plus`; the caption now says both.
- **"the last three lines" of the `listRepLoop` message.** Five.

**Prose.** The opening's third sentence was a roadmap ("The rest of this page is about…") and is
gone. "The illustration above proved a three-step unfolding" pointed past three intervening
illustrations; it now names the unfolding. "Everything so far reads a list apart" was false of
`m10-2`; now "Every proof so far has consumed a `listRep`". "Unit 18 chose that on purpose and said
so: address expressions buy nothing…" — Unit 18 says what they *cost*, at length; the clause now
states the cost in one line rather than paraphrasing a whole page.

**Not changed, and why.** The 52-block size stands (ERRATA §18; rendered size is mid-pack for this
phase and review found no padding beyond the one clause cut). All four exercises keep their
§D-prescribed ids, names, kinds, difficulties and Lean. The five-versus-six cut count stands —
warning 11. The `detail` on least fixed points stays open-and-first: §D's size line asks for it and
closing it leaves no hole, since the main line never needs the fixed-point vocabulary.
