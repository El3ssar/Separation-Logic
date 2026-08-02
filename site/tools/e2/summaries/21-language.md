# Unit 18 · `language` · A language that can get memory wrong
`site/content/21-language.js` · 71 blocks (68 non-`ex`), 3 exercises, ~4300 words of main line
(captions, `anat` parts and trace commentary counted) plus ~3660 inside the three exercise panels,
3 traces, 2 `anat`, 3 `note`, 1 `cmp`, 2 `txt`, 1 `detail`. Fragment extended by **one `example`**.
*Reviewed and revised — see "What review changed" at the bottom. No Lean was edited at review.*

## One job
The smallest syntax that can commit a memory error, written as inductive types, with each design
decision costed on the page.

## The hook I left (verbatim, final block; §D's wording)
> We have syntax and no meaning. Nothing on this page says what `Cmd.write 3 (.const 7)` *does*, and
> nothing can, because "the command writes to memory" is not yet mathematics. Making it mathematics
> means choosing what kind of object the semantics is — a function from states to states, or a
> relation between them — and that choice is not a matter of taste. It decides what "the program
> crashed" will mean.

Opens on `19-pure`'s hook in three words ("A command, then").

## Introduced
**Tactics: none** — everything used is ledgered ≤ 17.

**Syntax:** `inductive … where` with recursive constructors · `deriving Repr`, `Repr` · structural
recursion, with the shrinking condition stated as the rule Lean checks · `structure State` with data
fields, `State.mk`, `⟨σ, h⟩`, `.store`/`.heap`, **structure eta** · `infixr:60 " ;; "` and `;;` ·
`==`, `!` · `decide` (the *function*; the tactic is named and refused) · truncated `Nat` subtraction.

**The display rule, exact, used five times:** Lean prints `f a b c` as `a.f b c` when `a` is the
**first explicit argument** whose type names `f`'s namespace. `Store.set` qualifies (`σ.set x v x`);
`Atom.eval`/`BExpr.eval` do not, so **every later goal state spells out `Atom.eval σ a`**.

**Names now usable:** `Atom`, `Atom.eval`, `Atom.size`, `Store.set`, `storeSet_same`,
`storeSet_other`, `State`, `BExpr`, `BExpr.eval`, `Cmd`, `;;`. Illustration/sketch-only, no ledger
row: `Store.disjoint`, `PExpr`, `Cmd8`, `Triple`, `Atom.leafCount`.

**Concepts:** abstract syntax · the price of a constructor added later · **expressions cannot fail,
commands can** · the store is not a resource · `Bool` vs `Prop`, with the guard shape
`hb : b.eval σ = true` and the coercion producing it.

**Rejected alternatives, all compiled:** `Val := Int`; `Store.disjoint` (**does not typecheck**);
store and heap kept separate; a `Store → Prop` guard (`PExpr`); an `Atom` address;
`ite`/`loop` added later; `deriving Repr` on `Cmd`.

## Exercises
`x39` **@Store.set = @update + the two store lookup laws** [D 1] — the store *is* `update`.
`x40` **Evaluating a compound expression** [D 1] — two `rfl`s; truncated subtraction. Its `goal`
carries `sorry` under the **first** statement as well as the last: with two statements in an editor,
anything else fails to parse before the reader types. Check yours.
`x41` **Atom.size** [C 2] — structural recursion; clause heads given, bodies not.

## Lean I changed — one line
Under the existing `/- ex x40 -/` marker (§D's x40 is two parts; only the second existed):
`example : (Atom.plus (.var 0) (.minus (.var 1) (.const 2))).eval (Store.set (fun _ => 0) 1 9) = 7 := rfl`.
Corpus now 316 declarations / 2314 lines.

## Warnings — all compiled
1. **§D's two naming traps are false.** `while`, `if`, `do` are accepted as constructor names, and
   `⦃ ⦄` notation compiles and applies (**author of `25-hoare`: it is yours if you want it**). The
   real trap is `{ }`. My notes use traps I reproduced: `| rec` colliding with the generated
   recursor, and `open Cmd` shadowing core's `ite`.
2. **Application binds tighter than `;;`** — `Triple P c₁ ;; c₂ Q` parses as
   `Cmd.seq (Triple P c₁) (c₂ Q)`. Hence the double brackets on every triple.
3. **`storeSet_same`/`storeSet_other` have ZERO downstream consumers**; later proofs write
   `show Store.set …` then `simp [Store.set]`. §D's "the first four theorems stay useful" is true of
   the *shape*, not of a citation. The page says so. **Do not upgrade it into a promise.**
4. **`storeSet_same := update_same σ x v` passes the reader's kernel** despite unfolding a plain
   `def` under a `theorem`: ERRATA §28 bites on term-mode `rfl` against a stated type, not on
   unification. `Store.set σ x v x = v := rfl` **is** refused by both, with **no `Note:` line**.
5. **A non-structural recursion gives `fail to show termination`** (booked at `22-exec`). `x41`'s
   `variants` describes it without quoting it; the exhibit is unspent.
6. **`Repr` derives structurally** — `deriving Repr` on `Cmd` fails at `Repr BExpr`.

## Deviations
**68 non-`ex` blocks against ~26, ~4300 main-line words against ~4 screens** (ERRATA §18): level
with the largest unit so far on blocks, and the longest main line in the course — roughly 1.7× its
screen budget. Reviewed a second time for padding and none was found beyond the four sentences cut
below; the length is five type-level declarations each carrying its rejected alternative. **Not a
precedent for a Module-4 opener, and Module 5 should not read it as one.** Naming traps replaced
(warning 1). Two `txt`s, not one. §D's "`ite`/`loop` unused until Unit 35": rules at 19, used at 26,
specifiable at 35 and 36 — the page says that, and says it the same way in all three places since
review. §D says Unit 38 "discharges" the literal-address restriction; §D's own Unit 38 objective 6
only states it with the one-line change and the reason every theorem survives, which is what the
page promises.

## Provenance and checks
Every `state`/`trace` is `check.sh 21 <snippet> --incl` output byte for byte, `trace_state` for
mid-proof states, `snippet:L:C:` dropped (first caption says so). All 24 Lean-bearing fields were
re-extracted by script and re-run: 10 `illustration`s match their quoted output, 4 `sketch`es give
exactly the errors beneath them, 7 `verified` report only `has already been declared`, 3 `sol`s are
fragment text. Every `pitfall`/`variants` claim compiled separately. Two captioned elisions: the
`Hint:` tail of `Neg Val`, and the `in the application` line of the `;;` error.

Green: `node --check`; `lint.mjs` **0/0**; `ledger.mjs` 0/0 unit and edition-wide, sweep and `frags`
clean, **no waivers**; `render-check.js` 0 problems; `verify.sh 21` and bare `verify.sh`; `--prove`
**73/73**; **`wasm-check.cjs` over the prelude through 21, over that plus all ten illustrations, and
over each exercise's own spliced context — all clean**; banned-phrase grep clean.

## Weakest part, honestly
All three exercises are near-giveaways at rung 4, and `x41` hands over the clause heads. Structure
eta and the guard proof `simp [BExpr.eval, hb]` are compiled on the page but unexercised. The main
line runs ~4300 words against §D's ~4 screens — the longest main line in the course so far, and
review found no fat worth cutting: five type-level declarations each carrying a rejected
alternative is simply that long. Treat the figure as a warning to Module 5, not a precedent.

## What review changed
**No Lean was edited. No exercise `id`, `name`, `sol` or hint rung was touched.** One `goal` was
repaired (below); everything else is prose.

- **`x40`'s starter did not parse.** Its `goal` gave two statements and put `sorry` under neither,
  so `starterFor` appended one `sorry` to the *last* and the reader's editor opened on
  `error: unexpected token 'example'; expected term` before they typed anything. Now `sorry` under
  the first, per the house convention `x39` and `19-pure`'s `m4-8` already follow. All three
  starters were then compiled in the reader's own spliced context (fragment cut at the `/- ex … -/`
  marker): three `sorry` warnings, no errors.
- **`orient.payoff` said `Exec` "has one rule per constructor of `Cmd`".** It has **ten** rules for
  eight constructors — `ite` and `loop` get two each (`22-exec.lean:3–23`), and §D's own corpus line
  says "all ten constructors". Reworded. The same field claimed both design decisions are "still
  visible at Unit 34"; nothing in §D's Unit 34 (`37-wand`) touches either. Replaced by what is
  checkable: expressions-cannot-fault keeps every Module 5/6 rule to one case, literal addresses are
  why Unit 33's segments describe memory no program here can walk.
- **Three distance/counting claims were wrong.** `x40`'s `why` said truncation is met "seventeen
  units before" Unit 37 — it is nineteen. The opening said two commands are for "a construct nothing
  will touch for another seventeen units" and the `seq` `anat` part said "nothing builds one for
  another seventeen units": both false in both directions — `29-local-compose` (Unit 26) proves
  `heapLocal_ite`/`heapLocal_loop`, and the optional `24-interpreter` (Unit 21) *builds* `spin`, a
  concrete `.loop`. Both now say "no specification reaches either until Units 35 and 36", which is
  what `38-partial` and `39-invariant` actually deliver. The prose also said "buried under nine
  copies of itself"; the number was invented and is gone.
- **"From Unit 25 on" for structure eta → Unit 26.** §E books eta's first use at `29-local-compose`
  and `heapLocal_seq` is where it closes something (`r₁ = ⟨sMid.store, …⟩` under two rewrites).
  `28-local-heap` builds states but never leans on eta.
- **"Lean checks the cases are exhaustive and disjoint."** Lean checks exhaustiveness; overlapping
  patterns are legal and resolved first-match-wins. "and disjoint" removed.
- **"elaborator", twice** — the word has no ledger row and `19-pure`'s summary asks successors not
  to use it. `x39`'s `pitfall` now says what Lean is doing (it never settles what `rfl` was to prove);
  the `Cmd8.rec` note says the collision is caught when the finished declaration reaches the kernel,
  which is a word `03-compute` introduced. One caption's "after elaboration" went too.
- **`Cmd`'s `anat` glossed `load` and `free` and skipped `write`** — the memory command every later
  unit uses most. A part was added: it fails on the same condition `load` does, because nothing in
  this language makes a cell.
- **Unit 00 was credited to Unit 05.** `orient.needs` sourced `Store := Var → Val` from Unit 05
  while the page's own caption sources it from Unit 00, which is where `00-aliasing.lean:3–7`
  declares all five abbreviations. Split into two rows, in unit order.
- **The opening claimed the language must "commit the error Unit 00 opened on", then argued about
  faults.** Unit 00's error is a write felt through another name; the fault is a second, sharper
  failure. Both are now named, and the three forced operations follow from the pair.
- **Four announcing or restating sentences cut**, per PEDAGOGY §4: "There is nothing left to
  disambiguate" (restates the clause before it), "One thing about the arithmetic has to be said
  before it can surprise anybody", "One asymmetry in the declarations is explained here rather than
  left as a puzzle", and the trailing "and the rest of this section is those two" on a `state`
  caption. The `ite`/`loop` paragraph re-listed, item for item, the price already itemised on the
  first page; it now cites it instead. Net effect on length: about zero, because the `write` gloss
  and the opening repair cost what the cuts saved.

## Independent re-verification at review
Everything Lean-bearing was re-run rather than taken on trust, against `check.sh 21 --incl`:
all **10 `illustration`s as one file** (silent; every quoted `#check`/`#eval`/`#print` line matches
byte for byte), all **4 `sketch`es** (each gives exactly the error printed beneath it, including the
two `Type mismatch none` reports and `could not synthesize a Repr or ToString instance`), and every
`state`/`trace` regenerated from `trace_state` — `⊢ Store.set = update`, `⊢ σ.set x v x = v`,
`⊢ σ.set x v y = σ y`, the `Atom.eval (Store.set (fun x => 0) 1 9) …` opener, `⊢ 0 + (9 - 2) = 7`,
`⊢ ((Atom.const 1).plus (Atom.var 0)).size = 3`, `⊢ 1 + 1 + 1 = 3` and the `BExpr.eval σ b = true`
context: **identical byte for byte to the page**. Every `pitfall`/`variants`/prose claim compiled
separately: the two `rfl` refusals with their `?m.3`/`?m.7`/`?m.9` twins, the `hne`-reversed
`Application type mismatch`, the four-line `Store.set` refutation, the two re-pointed `= 6` / `= 0`
trees, `Missing cases: (const _) (var _)`, the unused-binder warning, `simp only [Atom.size]`,
`Neg Val`, `Atom.eval a σ`, `Triple P c₁ ;; c₂ Q`, `open Cmd`, `Cmd8.rec`, `| if`/`| while`/`| do`
accepted, and `deriving Repr` on a copy of `Cmd` failing at `Repr BExpr`.

Green after the edits: `node --check`; `lint.mjs 21-language` **0/0** (71 blocks); `ledger.mjs
21-language` **0/0**, sweep and `frags` clean, no waivers; `render-check.js` **0 problems**;
`gen-contexts.mjs --prove` **77/77** (x39, x40, x41 among them); `wasm-check.cjs` over the whole
corpus — *"the reader's Lean accepts all of it"*, which is the check that clears
`storeSet_same := update_same σ x v` under ERRATA §28; `verify.sh 21` (961 lines, 174 declarations);
banned-phrase grep **0 hits**.
