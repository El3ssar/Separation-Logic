# Unit 11 · `splits` · LAB — splitting a heap
`site/content/13-splits.js` · 47 blocks (43 non-`ex`), 4 exercises, ~1450 words of main-line prose
(≈2.4 screens), 5 traces, 4 `detail` (none before the first exercise; three are the retrospective).
Fragment extended by one theorem (`union_not_comm`).
*Reviewed and revised — see "What review changed" at the bottom.*

## One job
Turn `Heap.splits` from unused text into a usable relation and prove its associativity — Unit 16's
associativity of the connective with every trace of assertions removed.

## The hook I left (verbatim, final block; word for word from §D)
> `(Heap, union, empty, disjoint)` is a partial commutative monoid, and you can split a heap and
> re-bracket the pieces. Not one line of this module has mentioned truth, or a proposition about
> memory, or a program. The logic starts now.

Opens on `12-pcm`'s hook in its first sentence.

## Introduced
**Tactics: none.** First *load-bearing* use of `obtain`, as §E.1 predicts.

**Syntax owned here:** `⟨…⟩`, `constructor`, `intro ⟨_,_⟩` and `obtain` **against a folded `def`
that is a conjunction** — Lean unfolds the name to find the field count; `show` makes it visible.

**Names now usable:** `splits_empty_right`, `splits_empty_left`, `splits_comm`, `splits_assoc`,
`union_not_comm`.

**Concepts:** the splitting relation, and **why a relation and not a partial operation** — you can
quantify over cuts, not over the results of an operation · a heap has many splittings (compiled) ·
**associativity of a partial operation = associativity of the total one + definedness**, which is
what the existential carries · a `refine` read as four obligations (`tbl` + folded 24-line state) ·
one disjointness *extracted* with `disjoint_union_left.mp`, one *built* with
`disjoint_union_right.mpr` · validity-composition is **not** a `PCM` field, so `splits_assoc` does
not generalise.

**Rejected alternatives, all compiled:** `rfl` in the equation slot, and dropping `.symm` — both
accepted on the left unit law, refused on the right · `rw` in the wrong order · `rw … at he` ·
`disjoint_union_left.mp` before `subst` · `subst he₁` too · the witness `Heap.union hR hQ` ·
`x26` stated with `∀` outside `¬`.

## Exercises
- `x25` **splits_empty_right** [D 1] — two quotations; the lesson is that `rfl` fills the equation
  slot on the left unit law and not on this one. The main line now *poses* that trap and stops;
  the error message lives only in this exercise's `pitfall`.
- `m2-8` **splits_empty_left / splits_comm** [D 2] — the first is the worked example, transcribed
  (`x06`'s precedent); `splits_comm`'s body is `17-star-algebra.lean:26` with four fewer components.
- `m2-9` **splits_assoc** [C 4, `hard`] — the checkpoint; `deep` carries a two-part compiled
  refutation of the theorem with `hd₁` dropped.
- `x26` **union_not_comm** [G 2] — ⧗ in the plan; written, compiled, added to the fragment, using
  ERRATA §22's placeholder-`goal` pattern. Its `ledger.json` `status: todo` has now been cleared.

## Not explained (earlier summaries say it is known)
All of Modules 0 and 1; every tactic above; the three lookup lemmas; the unfolding ban; the
reduction asymmetry between the two unit laws.

## Deviations from COURSE-PLAN.md
1. **43 non-`ex` blocks against §D's ~14**; prose at budget. The excess is 9 compiled `code`
   blocks, 2 `state`s, 5 traces, 1 `tbl`. ERRATA §18.
2. **The lab rule "one sentence between exercises" is broken once**, between `m2-8` and `m2-9`,
   where a `sec` and nine blocks set up `splits_assoc`. §D objectives 3–5 all live there, and §D's
   own size line asks for the `txt` diagram and the `refine ⟨w, ⟨_, ?_⟩, ⟨_, rfl⟩⟩` shape by name.
   The three lines §D calls the exercise (`disjoint_union_left.mp`, `disjoint_union_right.mpr`,
   `union_assoc`) are exactly the three the setup does **not** supply.
3. **§D's worked example is also half of `m2-8`**, handled as `02-terms` handled `x06`.
4. **`↦` unused** (§E.5 books it at unit 13). 5. §D asks 1 trace; there are 5, per PEDAGOGY §7.
6. **Two §D claims are false against the verified Lean and the page does not repeat them.**
   §D objective 2 says "Prove `splits_comm` and `splits_empty_left` as one-line term proofs";
   `splits_comm`'s corpus proof is two tactic lines, so `orient.youWill` says so instead.
   §D's `x26` row says the reader "writes a negated statement from scratch for the first time";
   Unit 06's `x15` already asks for `¬ ∀ (h : Heap) (l l' : Loc) (v : Val), …`, and `x26` is the
   **third** [G] exercise (`x13`, `x15`, `x26`), not the second. Its `why` now says so.

## Warnings to successors
- **`Heap.splits` and all four theorems have NO downstream consumers.** `splits` occurs only in
  `10-disjoint.lean` and `13-splits.lean`; `16-star.lean` defines `star` with `Heap.disjoint` and
  `Heap.union` inline. The page promises only that the *proofs* recur. Do not upgrade that.
- **Authors of Units 15 and 16:** `splits_comm` and `splits_assoc` are your `star_comm` and
  `star_assoc_left` stripped — identical `subst`, `obtain … disjoint_union_left.mp hd₁`,
  `disjoint_union_right.mpr ⟨hd₂, hPR⟩`, `rw [_, union_assoc]`. This page tells the reader so, and
  the counts it states were re-checked at review: `star_comm` has **four** extra tuple components
  and `hu` for `he`; `star_assoc_left` is **six** lines of which **four** are these, and its
  `intro` does the work of both `obtain`s.
- **`⟨…⟩` flattening reassociates rightwards and never flattens the first field.** `⟨w,a,b,c,d⟩`
  for `∃ hQR, splits ∧ splits` fails; `⟨w, ⟨a,b⟩, c, d⟩` compiles. Both compiled.
- **`agreePCM` has no ledger row and is in no fragment** (ERRATA §19's blind spot). Unit 10's
  definition is reproduced inside a closed retrospective `detail` so the block runs standalone.
  **Author of `41-beyond`:** two copies exist; consolidate rather than write a third. That
  retrospective also tells the reader, with `agreePCM` as the compiled counterexample, that generic
  associativity is the thing your unit leaves undone — which `41-beyond.lean` bears out.
- **The PCM operation is never written `·` anywhere the reader has been** — `12-pcm.js` uses
  `Heap.union`/dot notation throughout and has no `a · b` in prose. A `b · c` that had crept into
  this unit's third retrospective fold was removed at review. Do not reintroduce the symbol without
  a ledger row.
- **Two of the four unit laws are `PCM` fields, not three.** `unit_left := union_empty_left` and
  `valid_unit := disjoint_empty_left`; `union_empty_right` and `disjoint_empty_right` are what
  Unit 10 *derives* for an arbitrary `PCM`. Both symmetry facts (`op_comm`, `valid_comm`) are
  fields. The four proofs on this page cite **nine** laws in total.
- **Weakest part, honestly:** `x25` is a two-quotation drill and `m2-8`'s first theorem is
  transcription, so the unit is measured by `m2-9` and `x26`; and `m2-9`'s rung-4 hint gives away
  the one line that is hard to find. `x26` is also the third negated-universal the reader writes,
  so its novelty is the *fact*, not the *form*, and its `why` no longer pretends otherwise.

## Provenance and checks
Every `state`/`trace` step is `check.sh 13 <snippet> --incl` output byte for byte, `trace_state`
where a mid-proof state was wanted, `snippet:L:C:` dropped (first caption says so); the inline
error quotes have line breaks removed and say so. All `code`/`anat` blocks were re-extracted by
script and re-run: `verified` ones report only `has already been declared` (or, for the two
statement-only quotes, the `unsolved goals` a bare `:= by` gives), the `illustration`s are silent,
the `sketch` gives exactly the four-goal `unsolved goals` its caption claims. Every
`pitfall`/`variants` claim was compiled separately.

All green: `node --check`; `lint.mjs 13-splits` **0/0** (47 blocks); `ledger.mjs 13-splits` 0/0 and
edition-wide 0/0, sweep and `frags` clean, **no waivers of any kind**; `render-check.js` 0 problems;
`verify.sh 13` (581 lines, 98 declarations) and bare `verify.sh` (2302 lines, 315 declarations);
`gen-contexts.mjs --prove` **52/52, 0 failed**, all four exercises included;
**`wasm-check.cjs` over the whole corpus clean** — which is what covers the §28 risk that
`⟨…⟩` and `obtain` have to see through the plain `def Heap.splits` inside an exported `theorem`;
`check-all-exercises.cjs splits` 2/2 (only `m2-8`/`m2-9` are in the installed `context-index.json`;
`x25`/`x26` land there when `gen-contexts --write` is next run at integration);
banned-phrase grep and the widened sweep clean. A whole-directory `lint.mjs` reports `m2-8`/`m2-9`
as duplicate ids against Edition 1's `03-m2.js` — one of 21 such collisions, clearing at integration.

## What review changed
Recorded so a successor does not reintroduce any of it. **The Lean was not touched**; every `sol`
was re-checked against `13-splits.lean`, every `state` and every `trace` step was regenerated with
`trace_state` through `check.sh 13` and diffed against the page (identical, byte for byte), and
every `pitfall`/`variants` claim was recompiled as its own snippet. One `ledger.json` row changed
(`union_not_comm`'s dead `status: todo`). Every other fix is prose.

- **Three arithmetic claims were wrong.** The brief said the finished algebra was "nine laws, two
  bridges" — there is no count under which that is nine; it is **seventeen theorems** across
  `10-disjoint`, `11-union` and `12-pcm`, and the sentence now says that. It said `Heap.splits` was
  "three lines of text"; it is **two** (`10-disjoint.lean:12–13`). The third retrospective fold said
  the four proofs cite "six laws" and that "three of the unit laws" are `PCM` fields; the citations
  number **nine** and the fields number **two** (see the warning above).
- **A false attribution:** "it is why `disjoint_union_left` and `disjoint_union_right` were called
  Unit 10's workhorses". The word *workhorse* appears nowhere in `12-pcm.js`. Now they are named
  as Unit 10's two bridges, which is what that page calls them.
- **A false count in the lead-in to `m2-8`:** "reversing a split is one rewrite". It is two
  (`rw [he, union_comm hd]`), one of them paid for with a disjointness proof. The same sentence
  also called `splits_empty_left` one of "the two facts that make a split symmetric", which it is
  not.
- **A false description in `m2-9`'s `variants`:** with `subst he₁` added, it is the **equation**
  component that becomes `union_assoc hP hQ hR`, not "the last component" — the last component is
  still `rfl`. Recompiled to confirm.
- **A wrong location claim in the `txt` caption:** choosing the witness "is the first move of the
  proof", contradicted three blocks later by the paragraph that says the hypotheses must be opened
  and `hPQ` eliminated first. Now: until it has been chosen there is nothing in the goal to work on.
- **An over-claim before `x26`:** "the only place in the algebra where a hypothesis is
  load-bearing" — `union_cancel_left` carries two, and the first retrospective fold says so.
  Restricted to *laws*, matching that fold.
- **Two §D claims contradicted by the verified Lean, both repeated on the page** — the one-line
  term proof of `splits_comm` and "the first time the statement is a negation". See deviation 6.
- **The same Lean error printed twice, in both cases once in the running argument and once in the
  `pitfall` that owns it.** PEDAGOGY §6.2 puts that material in `pitfall`, not the main line.
  Removed from the main line: the `⟨disjoint_empty_right h, rfl⟩` mismatch (kept in `x25`), and the
  `(Heap.union ?m.20 ?m.21).disjoint ?m.22` metavariable message (kept in `m2-9`). Both main-line
  passages now *pose* the difficulty and stop, which is also what gives `x25` and `m2-9` their
  point back. Two blocks fewer; `x25`'s `deep` trace no longer re-derives the stuck-`match`
  explanation its own `pitfall` gives four lines later.
- **A forward reference to something below this row.** "the one-line spelling is the normal one,
  because an entailment is a function and its proof is a lambda" — entailment is Unit 12. Cut; the
  paragraph now says only what §D's *Worked example* line asks it to.
- **Two re-explanations of ledgered material**: what `show` does (Unit 02, load-bearing since
  Unit 07) and that Lean prints `Heap.disjoint a b` as `a.disjoint b` (Unit 05). Both reduced to
  the one clause that is load-bearing here.
- **The "a heap has many splittings" argument was made twice** — once in the main line ("a two-cell
  heap has four") and again in the caption of the two-splittings exhibit. The caption now says only
  what the exhibit adds.
- **A paragraph that announced another paragraph:** "Two consequences, in two lines, that show why
  the relation had to be a relation" — PEDAGOGY §4's banned shape, and the reason had already been
  given. Replaced by the claim the exhibit actually proves.
- **`b · c` in the third retrospective fold**, a notation with no ledger row and no appearance in
  Unit 10. Written out in words.
- Minor: "This lab proves four things" followed by a list of three; "it costs two rewrites
  **because** `union_assoc` needs no hypothesis" (a non-sequitur — it costs *no more than* two);
  a `pitfall` cross-reference by block count ("three blocks above") replaced by one that survives
  editing.

**Not changed, and why.** `x26`'s four hint rungs still walk through where the `¬` sits relative to
the `∀`, even though Unit 06 taught the same distinction — a [G] exercise has no goal to restate at
rung 1, and this is the substitute. The `agreePCM` definition is still reproduced in full inside the
closed retrospective fold: the block is a compiled truth claim and has to run standalone, and its
caption says why it is a repeat. **47 blocks against §D's ~18 stands** — the prose is 1,450 words
against a ~2-screen budget, so the overrun is compiled exhibits, goal states and traces, and reading
every block against PEDAGOGY §4's test found nothing else that could come out without deleting an
argument. It is well under `12-pcm`'s 63 and should not creep back up.
