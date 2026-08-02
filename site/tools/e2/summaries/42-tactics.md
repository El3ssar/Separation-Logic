# §`tactics` · The tactic index
`site/content/42-tactics.js` · 28 blocks, **6 `tbl` carrying 117 rows**, 0 exercises, 46 KB
rendered. 1 `code` (`illustration`), 2 `note`, 7 `sec`, 12 `p`. No Lean fragment; **none touched**.
11 `ledgerAllow` — six banned tactics, one banned lemma name, four fenced items — every one firing.

## One job
List every tactic, keyword, syntactic form and library term the course uses — one line each, with a
clickable link to the unit that introduced it — and carry the standing rule that anything missing
does not exist here.

## What I left (no hook — off the path)
Opens on `41-beyond`'s handover in seven words: *"Unit 38 sent you here, and this is not a unit."*
(`41-beyond.js`'s last block does send the reader here, and its badge is `38`, so the number reads.)
Final block, verbatim:
> § `ref` is the other index: the notation table with how to type each symbol, every theorem the
> course proves and the unit that proves it, and the five rules of proof discipline.

**Author of `43-ref`:** I took the **library** names (`congrFun`, `absurd`, `if_pos`, `propext`,
`max`, …) into a table here — neither corpus theorems nor notation, so they would otherwise fall
between us. Keep your theorem index course-internal. The notation table is yours entirely:
`⊢ ⊣⊢ ↦ ∗ ;; -∗` appear here only inside the one `infix:n` row, with no "how to type it" column.

## Introduced
**Nothing.** Every row points at the unit that owns the explanation.

**Deep links.** The unit cell is `<button style="all:unset;…" data-go="N">badge · id</button>`, `N`
being the file's index in `ledger.json`'s `order` — which is the file prefix, and is the order
`integrate.mjs` emits the `<script>` tags in. Both identities checked; all 117 unit cells were
re-checked against `ledger.json` in review and every one is right. `app.js` needs no change;
`href="#id"` would have been wrong twice (no `hashchange` listener, and `render-check.js` rejects an
anchor with no matching id on the page).

**Mind the offset.** The badge in a unit cell is the §D **unit number**; `data-go` is the **file
index**. They differ by one from `02-terms` on and by two from `07-heap` on. Row `03 · funext` has
`data-go="4"`.

## Exercises
None, per §D.10.

## Provenance
No `trace`, no `state`. The one `code` block is `illustration`, three declarations, compiled by
`check.sh 42`: `omega`, `decide` on a closed proposition, `apply` and `assumption` all accepted in
silence. Compiled and reported in prose with no block: `set`, `linarith`, `ring`, `aesop` and
`Function.funext_iff` → `unknown tactic` / `Unknown identifier`; `simp_arith` → the deprecation
reported **as an error** (`lean` exits 1; note `check.sh` exits 0 on it); `decide` on a goal with a
free variable → `Expected type must not contain free variables`. Counts grepped from `lean/e2`:
**22** tactics in the corpus (`rwa` and tactic-`rfl` once each — the 22 named in the second
paragraph are exactly the tokens that appear in tactic position); `unfold` 5; `rename_i` 4;
`show … from` 1 (`27-locality.lean:85`); `infix*` declarations **6**; 319 declarations and 2327
lines, from `verify.sh 42`.

## Fixed in review (six factual defects, all now checked against Lean 4.32.2)
1. **`¬ P, P ≠ Q` row said "Lean prints `x ≠ 4` back as `¬ x = 4`."** False. Lean prints `x ≠ 4` in
   both hypothesis and goal position; it is **`simp`** that unfolds `Ne` and leaves `¬x = 4` — which
   is what `00-aliasing` actually shows. The row now says that.
2. **The `infix` row said the course declares *five* notations and listed six.** Six `infix*`
   declarations in the corpus; the row now says six and groups `↦` and `;;` at 60.
3. **The `✝` row said "Explained at 03".** `04-funext.js` contains no `✝` at all — ERRATA §15 moved
   the explanation to § `goalstate`. The row now points there and keeps `rename_i` at 19.
4. **`abbrev` said "the five types of the model"** where the corpus has seven `abbrev`s. The row now
   names `Loc`, `Val`, `Var`, `Store`, `Heap`.
5. **`rw` said "It matches text".** Replaced with "matches the term as it stands and will not unfold
   a `def` to find one", which is the lesson without the false mechanism.
6. **The diagnostics lead-in said "the first of them" produced every goal state** — `#check` is
   first, `trace_state` is fifth. Lead-in now names `trace_state`; the `trace_state` row was
   rewritten to say something else (it is a tactic and goes inside the proof).

Also in review: `Function.funext_iff` added to the "what is not here" section — §E.1 bans it by name
and nothing on the page had said so; it is Mathlib's spelling and Lean answers `Unknown identifier`,
while core's `funext_iff` does exist. `decide` added to the illustration so all four accepted
tactics are exhibited rather than three asserted and two shown. The library table reordered
alphabetically (it was in no order) and the lead-in says so. One `cases` sentence added to the
tactics lead-in giving the taxonomy, which `orient.youWill` promises. The one-sentence paragraph
announcing the "what is not here" split folded into the paragraph it announced. The `sorry` row no
longer repeats its own table caption; it names where `sorry` is displayed (24, holding open the
frame proof) instead.

## Warnings to successors
1. **The `cases` rows disagree with `ledger.json` on purpose, and the page is right.**
   `ledger.json` books every `cases` token at `03-compute` because a regex cannot tell inversion
   from a value split; its own `notes` say so. The page prints the unit the reader *meets* each form
   in, which is §E.1's table: saved-equation and value-split at 02, inversion and `with | ctor` at
   19. `Bool` is that case reversed (ledger `17-star-algebra`; §E and the page 21-language, the
   earlier sighting named in the row). Every other row agrees with `ledger.json`, including the
   four that disagree with §E and where `ledger.json` overruled it: `;` at 02-terms, `match … with`
   at 10-disjoint, `by …` in a term at 11-union, `structure` at 07-heap.
2. **`True.intro` and `False.elim` have no ledger rows**, though `14-assertions`' summary says they
   were given some. They are on the page at 12 · `assertions`; `ledger.mjs` misses them because the
   coverage check skips dotted uppercase names. A gap in §E, not mine to close. **`show … from` has
   no ledger row either** (it is in no §E table); the page books it at 24 · `locality`, which is
   where its single corpus occurrence is.
3. **The ban is a course rule, not a compiler fact** — `06-errors`' warning, copied and extended.
   That page covers the tactics that fail; this one covers the four that **succeed** (`omega`,
   `decide`, `apply`, `assumption`). Whoever marks exercises should know a reader can submit any of
   them and be accepted.
4. **An index must name a fenced item after the fence** — listing is not relying. That is what four
   of the waivers are for, and the file's header comment says so.
5. **Weakest part, honestly.** The 117 descriptions are the only hand-written thing here and nothing
   checks them; review found five wrong and could not read all 117 against their units. Where a
   form's *lesson* lives later than its first sighting (`structure`, `match`, `Bool`, `.trans`) the
   row names both.
6. **`case pos` / `case neg` are never typed in the corpus.** The row calls them labels, not
   tactics. If a later edit uses `case … =>` to select a goal, that row must change.
7. **`Nat.le` has a ledger row (24-interpreter) and no row of its own here** — `≤` occurs once in
   the whole corpus, in `run_le`, inside the optional unit, and the `induction hle` row names it.
   The Unicode-abbreviation row of §E.2 is also absent by agreement: how to type a symbol is
   § `ref`'s column.

## Deviations
1. §D asks for one alphabetical list. It is six tables — tactics, combinators, declarations, terms
   and types, library terms, diagnostics — each alphabetical (the "terms and types" table is
   explicitly grouped and says so), because one flat list of 117 rows is not a page you keep open in
   a second tab.
2. §D says "generated mechanically from §E". The unit column is generated; the third column is
   hand-written, and warning 5 is the price. The file's header comment carries the rule that keeps
   it true.
3. §D gives no size budget.
