# §`ref` · Notation, theorems, discipline
`site/content/43-ref.js` · 37 blocks, 0 exercises, 49 KB source / 55 KB rendered. 4 `tbl`
(18 + 18 + 37 + 21 rows), 1 `dl`, 2 `code` (**both `illustration`**), 2 `state`, 1 `steps`, 1 `ol`,
2 `note`, 1 `quote`, 1 `dod`, 7 `sec`, 15 `p`.
**No `ledgerAllow`. Lean fragment and `ledger.json` untouched.** Last file in the course.
*Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review.*

## One job
Be the second tab: every symbol with the keystrokes that make it and the definition it abbreviates,
all 239 theorems with the unit that proves them, twenty-one goal shapes with the lemma family that
settles each, and five rules about laying a development out.

## Hook
**None — last page.** Opens on `42-tactics`' handover in nine words: *"§ `tactics` sent you here for
the other half, and this is not a unit either."* Closes with a `dod`; the last prose block deep-links
Unit 38 for the ideas worth keeping and the three projects, and suggests a fourth — instantiate
`PCM` with permissions or tokens.

## Introduced
**Nothing.** No tactic, syntax, notation, lemma or concept; every row names the unit that owes the
explanation. No exercises, per §D.10.

## Where the numbers came from
- **239 theorems**, `grep '^theorem' site/lean/e2/*.lean`. **319 named decls in 2327 lines**
  (`verify.sh 43`) = 239 + 67 `def` + 7 `abbrev` + 2 `structure` + 4 `inductive`; 12 unnamed
  `example`s make up the gap to 331 declaration lines.
- **112 `simp`** (comments stripped, `simpa` excluded): 32 in Unit 21; 13 across Units 13–17, every
  one a `(by simp)` on a numeric disequality in a counterexample or a `simp [Heap.empty]`; **no law
  of `∗` uses `simp`**; seven of the last eight units have none.
- The **theorem index was generated** from the fragments and pasted. A new theorem needs a new name
  in its unit's row and nothing checks that. Deep links are `data-go="N"`, N = file prefix.
- **All four tables were re-checked against the corpus at review by script**: the 37-row theorem
  index matches the fragments name for name *and in order*, per unit and per count; the `dl`
  inventory lists exactly the 80 non-theorem declarations, no more and no fewer.

## Provenance
No `trace`. Both `code` blocks were extracted from the shipped file and recompiled with
`check.sh 43` **exactly as printed** (again at review, after edits): precedence/associativity
(4 `rfl`s) and the definition-table check (8 `example`s, incl. `Hoare P c Q = (P ⊢ wp c Q) := rfl`).
Both `state` blocks are real `check.sh 43` output from broken snippets, re-derived byte for byte at
review, `snippet:L:C:` dropped and elisions named in the caption: `P ⊢ Q ∧ R`, `P ⋆ Q`, `P * Q`.
Prose only: `P -* Q` → `unexpected token '*'`. The `simp`-orientation failure in the closing `warn`
was compiled at review and the leftover goal it quotes is Lean's.

## Warnings
1. **`⊣⊢` cannot be typed in the course editor.** `site/assets/editor.js`'s `ABBREV` has no key for
   `⊣` or `⊣⊢` and neither is on `PALETTE`. Harmless in ordinary exercises (`starterFor` prefills
   the statement) but it bites any **design [G]** exercise whose intended statement is an `⊣⊢`. The
   page says so and tells the reader to copy the glyph. A one-line fix exists — add `'dashv': '⊣'`,
   put `⊣⊢` on the palette — but it touches a shared asset, so it was left. Someone should do it.
2. **No claim about VS Code**: no `abbreviations.json` on this machine, so every keystroke claim is
   about the editor on these pages and says so. Do not promote it — in real vscode-lean4 `\star` may
   produce U+22C6, not U+2217. Relatedly, **`-∗` is a hyphen plus U+2217**, not one glyph, and
   U+22C6 `⋆` has no notation, yielding the bare `expected token`.
3. **Units 00 and 07 have no index row**: they prove everything as unnamed `example`s (2 and 3).
   Said in the caption; name those statements and the table needs two more rows.
4. `--sweep`'s three unrowed names (`and_comm_iff`, `and_assoc_iff`, `emp_iff_all_none`) are still
   open — inherited from `41-beyond`, not this page's.
5. **Weakest part.** The goal-shape table's 21 rows are the only hand-written judgements here. Every
   name is in the corpus and every unit citation was checked, but "reach for this" is opinion.
6. **The notation table's "introduced" column is now `ledger.json`'s**, not first-heavy-use. Three
   rows moved at review (below). If a later edit re-books a glyph in `ledger.json`, this column must
   follow; nothing checks it.

## Deviations from §D.10
1. **"The ideas worth keeping" is not reprinted here.** §D assigns that list to Unit 38 *and* to
   this page; `41-beyond` shipped it as a seven-item `ul` that closes the narrative, so repeating it
   would be the looping the client rejected. The closing paragraph now **deep-links** Unit 38 for it
   (`data-go="41"`) rather than only naming it, so the page still does its navigational job.
2. **"What comes next" is one paragraph** — §D.10 itself moves that material into Unit 38's
   Projects, and Unit 38 shipped all three with scope estimates.
3. **Added: "Finding it by the shape of the goal"** (21 rows). Edition 1's most useful reference
   section; the theorem index alone is searchable only if you know which unit to look in.
4. No size budget given, as for `42-tactics`.

## What review changed
No block was added or removed; fifteen fields were rewritten. **Nine were false or
self-undercutting.**

- **`\ne` row: "Lean prints it back as `¬ a = b`."** False, and it is the exact claim `42-tactics`
  had already been corrected on. Lean prints `≠` in hypothesis and goal position; `simp` is what
  unfolds `Ne`. Verified with `trace_state` before and after `simp at h ⊢`. Row now says that.
- **"Nothing on it is argued and nothing on it is new"** (opening), on a page whose `steps` block
  argues five rules at length. Replaced by what is actually true: nothing here introduces a tactic,
  notation or name the reader has not met, and no section depends on any other.
- **"The theorem index was generated from the Lean fragments, so it cannot drift from them."** It
  can — the file's own header comment says a new theorem needs a new name added by hand. Now: it was
  generated rather than transcribed, so every name in it is a name Lean has accepted.
- **`∧` booked at Unit 01, `⟨ ⟩` at Unit 01, subscripts at Unit 01.** `ledger.json` books `∧` and
  `⟨…⟩` (as an `intro` pattern) at `00-aliasing`, and `₁` occurs in Unit 00's content and nowhere in
  `02-terms`. The row for `∧ ∨ ↔` was split; three rows moved to Unit 00 and the table is still in
  first-sighting order.
- **Rule 3: "arrives as a named lemma from Units 05, 06 and 09."** `disjoint_empty_left`, one of the
  five lemmas named in the same sentence, is Unit 08. Now "05, 06, 08 and 09".
- **Rule 5: "`lseg_append`'s `cons` case is four `star_assoc_left` and `star_mono` steps in a row
  and nothing else."** It is seven steps, and the first three are `star_mono_left`,
  `star_exists_left` and `aExists_mono`. Also "all four are the same picture: a heap in three
  pieces" — `hoare_frame` cuts a heap in two, not three. Both rewritten to what the proofs do.
- **The closing `warn` attributed its own example to § `errors`.** § `errors` gives the
  disequality-orientation lesson for `rw [if_neg hne]` and for a lemma argument, never for `simp`.
  The note now states the `simp` case itself, with the goal Lean actually leaves
  (`⊢ x = l → some v = h x` when the hypothesis is `l ≠ x`), and says § `errors` covers the other
  two spellings.
- **`dl`: "`update` … defined seventeen units before there is a store."** `Store` is defined in
  Unit 00; `update` is Unit 04 and `Store.set` is Unit 18. Now "fourteen units before the language
  that needs it".
- **`dod` and `orient.youWill`: "type every symbol the course uses"**, contradicted two screens
  earlier by the `⊣⊢` warning; and "unfold any of them to the `Store → Heap → Prop` underneath",
  which is not what `Hoare` unfolds to. Both repaired.

**Two overclaims of coverage.** The definitions table was captioned "Every notation and every
derived assertion" while omitting `aTrue`, `aFalse`, `starNoDisj`, `listRep`, `lseg` and six more;
it now says what it contains and points at the inventory for the rest. The `rfl` check below it was
introduced as though it checked the table; it checks eight of the eighteen rows, and both the
lead-in and the caption now say eight.

**One count.** "one of the twenty shapes below" of a 21-row table.

**Three prose repairs.** The proof-discipline lead-in announced the block that follows it
(PEDAGOGY §4). `orient.payoff` restated the opening paragraph's second sentence. "everything in the
course is a predicate on a store and a heap" → "every assertion".

**Checked and left alone.** Every precedence and associativity against the six `infix*` declarations
in the corpus; the three error messages, re-compiled; `star_comm`/`star_mono`/`star_assoc_left` at
two, two and six tactics; `write_with_frame`'s exact shape; "not one `funext` in Unit 23's six
theorems"; all four `simp` counts and their placements; `hoare_iff_entails_wp := Iff.rfl`;
`@Store.set = @update := rfl`; every `data-go` against `ledger.json`'s `order`; `Sort`, `.mp`/`.mpr`,
`Iff.rfl` and precedence numbers all booked at or above this file.

Green: `node --check`; `lint.mjs` **0/0** (37 blocks, 0 ex); `render-check.js` **0 problems**;
`ledger.mjs` **0/0** (sweep 3, pre-existing); banned-phrase grep **0**; both `illustration`s through
`check.sh 43`; `verify.sh 43` clean (2327 lines, 319 declarations, fragment unmodified).
