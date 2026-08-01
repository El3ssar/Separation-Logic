# ERRATA — read this before you write, along with the unit summaries

This file is not a unit summary. It is the running list of defects found in
`COURSE-PLAN.md` after it was written, and the decisions taken on them. Where it
contradicts the plan, **this file wins**. Append to it if you find another.

---

## 0. If you add Lean, run `verify.sh` WITH NO ARGUMENT

`site/tools/e2/verify.sh <NN>` builds fragments `00..NN` only. A new declaration
in an early unit that collides with a name in a *later* unit is therefore
**invisible** to it — your unit passes, and the corpus is broken for everyone
downstream.

This is not hypothetical. It has already happened once: `00-aliasing` added a
heap named `twoCells` for exercise `x01`, colliding with `def twoCells` in
`09-footprint`, which three exercises (`x16`–`x18`) are built on. `verify.sh 00`
passed. The whole corpus did not compile. The Unit 00 declaration was renamed to
`twoAllocated`, because §D names `twoCells` explicitly in Unit 07 while §F
specifies `x01` only by behaviour — **the later unit owned the name, so the
earlier one yielded.**

So, every time you touch `site/lean/e2/`:

```
site/tools/e2/verify.sh <NN>      # your unit compiles in its own context
site/tools/e2/verify.sh           # ...and the WHOLE corpus still compiles
```

Both, in that order. If the second one fails and the first passed, you have hit a
name collision with a unit after yours. Rename **yours**, unless the plan gives
you the name explicitly and gives them nothing — then say so in your summary and
tell the other unit's author through this file.

Pick names that are unlikely to collide in the first place: a bare `h`, `demo`,
`example₁`, `twoCells`, `test` are all names four other authors will also reach
for. There are 296 declarations in this corpus and every one shares a namespace.

**`verify.sh` proves DECLARATION order. It says nothing about TACTIC order.**
A fragment can compile perfectly and still teach a tactic three units before the
ledger introduces it — which is exactly what happened to `write_of_eq` in
`08-heap-laws`, written with `subst`, a tactic §E.1 books two units later. It
compiled, so nothing complained. **Do not read a green `verify.sh` as "my
ordering is clean".** It is not that check.

**So run the ledger too, in the same breath, not later:**

```
node site/tools/e2/ledger.mjs --sweep       # names the ledger cannot police
node site/tools/e2/ledger.mjs --fragments   # tactic order inside the Lean
```

`--sweep` lists every name in `site/lean/e2/` that has no row in `ledger.json`.
**A name you add that nobody rows is a name the ledger cannot police — including
yours.** `--fragments` runs the order check over the Lean itself rather than the
pages, which is the only check that will catch a tactic you used in a fragment
before any page quotes it. An unrowed name does not fail a check; it makes the check silently stop
covering that name, which is the failure the ledger exists to prevent, one level
up. The bare `ledger.mjs` run also prints the count on every invocation, pass or
fail, along with a `frags:` line for the fragment pass, so both are hard to
miss. They should say *every name in the verified Lean has a ledger row* and
*every tactic in site/lean/e2 is introduced before it is used*. If it does not, add the rows before you write the page — see §19
for why the timing decides whether the gap gets fixed or waived.

---

## 1. `site/tools/e2/ledger.mjs` now exists — run it

It was still being built when the first units were commissioned. It is finished
and it works. Run it on your unit before you report:

```
node site/tools/e2/ledger.mjs <your-file-id>
```

It checks four things: that nothing you used is introduced after your unit, that
every course lemma you cite actually exists in the verified fragments, coverage,
and (with `--audit`) the reverse direction. It reads
`site/tools/e2/ledger.json`, which is `COURSE-PLAN.md` §E as data — 510 rows.

`--audit` is the check that keeps the ledger honest, and it is worth running
after you add Lean: it compares every course-internal row against the
declarations in `site/lean/e2/`, in both directions. Every disagreement it
reports today is a known one, carrying a `status` and a reason (§5 below).
**Anything it reports without a status is new, and is yours.**

**Two escape hatches, both by name so a reviewer sees what was waived:**

- `ledgerForward: ['listRep', 'wp']` on a chapter — prose may name a thing the
  course has not reached yet. Use it *only* for a genuine forward reference, the
  "here is where we are going" kind, and never to excuse using something.
- `ledgerAllow: ['omega']` — a deliberate exhibit, e.g. quoting a tactic in
  order to show it failing, or a promissory-note block. Applies to every block
  in the chapter, and to shape rows as well as names.

Read **§10** before you reach for either: it draws the line between the forward
reference that is the course's chief device and the one that is a defect. A
waiver that suppresses nothing is now reported as a **stale waiver** warning, so
they cannot rot silently when a ledger row is renamed.

If the checker fires on something you believe is correct, do not silence it
without saying why in your summary. The checker found a lemma Edition 1 cites by
name that does not exist (`self_disjoint_empty`), and a second (`star_assoc`),
so its errors are worth reading carefully.

**Known false positives**, documented at the top of `ledger.mjs`: prose that
names a lemma in order to say it does *not* exist; error messages inside `state`
blocks, which are scanned as if they were Lean; `#check` output. Class (a)–(i).

---

## 2. `structure … where` is met at `07-heap`, not `12-pcm`

§E.2 books the keyword at unit 10 (`12-pcm`). But §D unit 05 (`07-heap`) displays
the `PHeap` dependent-pair exhibit, which *is* a `structure … where`.

**Decision: the ledger is corrected to `07-heap`.** The author of `07-heap` owes
the reader one sentence — a structure is a named record of fields — because the
exhibit is a rejected alternative the reader only has to *read*. `12-pcm` still
owns the concept and is where the reader *builds* one, and should not treat the
keyword as brand new.

---

## 3. Four constructs are needed by unit 00 but booked at unit 01

`fun x => e`, `→`, `∧` and the anonymous constructor `⟨…⟩` are booked at
`02-terms` by §E.2, but `00-aliasing`'s own Lean requires all four
(`def aliasedAfter := fun l => if …`, `Loc → Option Val`, `¬ (… ∧ …)`).

**Decision, already encoded in `ledger.json`:** all four are booked at
`00-aliasing`. The anonymous constructor is split — the bare two-slot bracket at
`00-aliasing`, its flattening across three or more slots at `02-terms`.

---

## 4. `⊢` is two different things

The goal turnstile in a Lean goal display (from `00-aliasing`, since every goal
state shows one) and the entailment notation `P ⊢ Q` (`14-assertions`). §E.5
books only the second. The checker matches the infix use only. Do not treat the
turnstile in a goal display as notation needing introduction.

---

## 5. Ledgered names that no Lean fragment declares — triaged

They have been checked one by one, against Edition-1 `content/*.js` and by
compiling each against its intended prelude. **Every one now carries a `status`
field in `ledger.json` saying which of four things it is**, and the checker
treats them differently, so read your row before you panic.

**`status: "todo"` — genuinely unwritten §D ⧗ Lean. If one is yours, YOU WRITE
IT**: draft it, compile it with `tools/e2/check.sh`, add it to your fragment,
re-run `tools/e2/verify.sh <NN>`. Do not ship it uncompiled and do not tag it
`verified` until it is in the fragment. Citing one is a *warning*, not an error,
because the ledger already knows it is missing.

| name | unit | exercise |
|---|---|---|
| `nested_pack`, `nested_unpack` | `02-terms` | x06 |
| `double` | `03-compute` | x07 |
| `defined` | `03-compute` | x09 |
| `funext_drill`, `if_drill`, `by_cases_drill` | `04-funext` | x10–x12 |
| `union_not_comm` | `13-splits` | x26 |
| `run_example` | `24-interpreter` | x47 |
| `writeTwice_spec` | `26-small-footprint` | x48 |

Not ledger rows, because they declare nothing, but in the same state: `x01`,
`x08`, `x29`, `x30`.

**`status: "migrate"` — real, `sorry`-free Lean that already existed in
`site/content/*.js` rather than in a fragment.** Not an authoring job; a move.
Most have already been moved; **`--audit` tells you which, if any, still have
not**. Citing one that has not landed is a warning, not an error.

`HeapLocalWeak` (`27-locality`, from `09-m8.js`) · `readAndFree_framed`
(`32-symbolic`, from `10-m9.js`) · `spin`, `spin_diverges`, `run_spin_none`
(`24-interpreter`, from `06-m5.js`) · `aForall`, `star_forall_left`,
`star_forall_right_fails`, `Pcx` (`17-star-algebra`, from `05-m4.js`).

`runIf` was on this list and has been removed: it is not a migration and never
was. See §12.

**`status: "illustration"` — real Lean that compiles against its own unit's
prelude, deliberately kept out of the fragments because it is a teaching exhibit
rather than course corpus.** Cite it freely; it is order-checked like anything
else, and the existence check stays quiet. `lookup_of_unallocated`
(`00-aliasing`, the `anat` block whose `(hx : x ≠ 4)` binder `02-terms` exists to
explain) is the first. Any `illustration`-tagged block that *declares* a name
wants a row of this kind — otherwise every unit citing it gets a coverage
warning.

**`status: "display"` — can never compile, and is not supposed to. The failure
IS the exhibit.** These do not fire the existence check.

- `runBad` (`22-exec`) — fails with `fail to show termination`.
- `PHeap` (`07-heap`) — its second half is a `def`-instead-of-`abbrev` sketch
  whose point is the real `failed to synthesize instance … Decidable (x = l)`.
- `alloc`, `hoare_alloc` (`41-beyond`) — `sketch`. Adding an `alloc` constructor
  to `Cmd` would invalidate every `Exec` proof in the corpus.

**`status: "renamed"` — an Edition-1 name for something the fragments carry
under an Edition-2 name.** Cite the new one. The checker names it for you.

- `load_stuck` → **`exec_load_stuck`** (`22-exec`, exercise x43)
- `star_or_left_conv` → **`star_or_right`** (`17-star-algebra`, exercise x38)

### Two corrections to what this section used to say

- **`readAndFree_framed` is a MIGRATION, not an authoring gap.** This file
  previously said it "exists nowhere". It does exist: the complete, `sorry`-free
  version is in `content/10-m9.js` and compiles against `32-symbolic`. (There is
  also a copy in `09-m8.js` carrying a deliberate `sorry` in the `Preserves`
  slot — that is a *different* block, the "you cannot discharge this yet"
  exhibit, and it is display-only.) `32-symbolic` does not have to write it.
- **`HeapLocalWeak` is two things, not one.** The `def` is plain, `sorry`-free
  Lean in `09-m8.js` that compiles against `27-locality` — a migration. The
  stranded frame proof that *consumes* it is an anonymous `example` carrying a
  `sorry`, so it has no name, no ledger row, and can never live in a fragment,
  because `verify.sh` refuses a `sorry`. It still has to be real Lean that
  really fails to close, and it has to be checked out of band. Quote the actual
  stuck goal.

`x07` remains mismarked ✔ in §F. Worse: §D Unit 02 names it as
`` `double_unfold`-flavoured drills ``, and **`double_unfold` exists nowhere** —
"-flavoured" was carrying the whole claim. The row is now `double`, `status:
todo`, and `03-compute` writes `def double n := n + n`.

---

## 6. Two declarations moved, for dependency reasons

Found while building the verified corpus; the fragments already reflect this.

- **`star_not_weakening` moved `16-star` → `17-star-algebra`.** Its proof needs
  `star_emp_left_intro`, which is `17-star-algebra`'s own exercise. `16-star`
  keeps the concrete refutations `no_star_weakening` and `no_star_duplication`,
  which is what that unit's argument actually needs; the general form is a
  packaging step and belongs at the end of the laws lab.
- **`counterGuard` and `countdown` (definitions only) moved `40-variant` →
  `39-invariant`**, because `39-invariant`'s own exercise mentions both.
  `countdown_spec` stays in `40-variant`.

---

## 7. Token collisions the checker cannot separate

Do not be surprised by these, and do not "introduce" a thing twice:

- **`cases`** has three forms in three units (structural at `03-compute`,
  inversion on a derivation and `cases … with` at `22-exec`). One token, booked
  at the earliest. A bare inversion used early will **not** be caught — check it
  yourself.
- **`subst`** is a tactic at `10-disjoint` and an assertion-level move at
  `25-hoare`.
- **`rfl`** is a term at `02-terms` and a tactic at `03-compute`.
- **`decide`** is introduced at `21-language` and banned by §E.1 "on non-trivial
  propositions". Not mechanically separable — use judgement.
- **`simp only [f] at h ⊢`** is booked at `24-interpreter`, which §E.6 declares
  **optional**. It is left unfenced, so you may use it — but a reader who
  skipped the optional unit has not seen it. Prefer introducing it where you
  need it, in one sentence.
- **`set`** is a banned tactic (§E.1) but `Store.set` is a course definition at
  `21-language`. The checker only reads `set` as a tactic when it stands in
  tactic position, so `Store.set` and `σ.set` are safe and will not fire.
- **`left` / `right`** are tactics at `02-terms`, and also the tails of a great
  many lemma names (`star_emp_left`, `disjoint_union_right`). Word boundaries
  keep them apart; the tactic rows only fire in tactic position.

Genuinely fenced by §E.6 — no unit after `24-interpreter` may use these, because
that unit is optional: **`simpa`**, **`induction hle with | refl | step`**,
**`max`**, **`Nat.le_max_left`**, **`Nat.le_max_right`**. The checker enforces it.

### The `<code>` tag is a citation. Twenty-one course names are English words

The checker reads `<code>` spans in prose, because §E's rule is that a thing
below your row "must not be mentioned". So tagging an ordinary English word as
code turns it into a citation of whatever declaration shares its spelling. The
fix is never a waiver — it is to drop the `<code>` tags, because it was English
and not a citation.

`00-aliasing` hit this with **`swap`**: §D.0 uses a swap routine as the running
example of why the classical repair does not scale, and unit 30's LAB is *called*
`swap`, so `<code>swap</code>` in unit 00 reads as a citation twenty-nine units
early. Every one of these will do the same to somebody:

`comp` · `mp` · `defined` · `double` · `twice` · `update` · `fact` · `emp` ·
`star` · `pure` · `run` · `spin` · `subst` · `swap` · `wp` · `node` · `lseg` ·
`wand` · `countdown` · `drain` · `alloc` — plus the library row `max`.

`fact`, `defined`, `update`, `run`, `double`, `twice`, `node`, `star`, `pure` and
`swap` are the ones you will actually write by accident. Ask of every `<code>`
span: *am I naming a declaration the reader could go and look at?* If not, it is
prose.

**The ledger cannot help you with this, and goes quiet exactly when you stop
being careful.** A mis-tagged English word only fires as an error while its
declaration is still in the future. After the introducing unit the checker is
structurally silent — `<code>fact</code>` used as an English word in unit 30 is
indistinguishable, to the tool, from a citation of `fact`. So this rule is
enforced by reading, for every unit except the handful that happen to precede
each name. A grep is the cheap half:

```
grep -oE "<code>(comp|mp|defined|double|twice|update|fact|emp|star|pure|run|spin|subst|swap|wp|node|lseg|wand|countdown|drain|alloc|max)</code>" content/<your-file>.js
```

Every hit is either a real citation — fine — or English that must lose its tags.
`00-aliasing` returns zero.

**Two cases where the tags are right and the tool now knows it.** Not everything
that looks like a collision is one, and you should not be dropping tags off
correct code:

- **A bare `<code>left</code>` or `<code>right</code>`** is almost always naming
  an `And`/`Or` field, not citing the tactic — `00-aliasing` glosses the
  daggered `right✝` that way. Those two rows are marked `english: true` in
  `ledger.json`, and a prose span that is *just* the bare word is exempt. In
  Lean text the tactic-position test still catches the real thing.
- **A quoted Lean error message** — `<code>failed to synthesize instance of type
  class …</code>`, or a `state` block holding one — is Lean talking, not you
  citing. `06-errors` exists to print twelve of these and would otherwise be
  unwritable. Three details worth knowing:
  - It covers **`state` blocks as well as prose spans**, because a `state` block
    holds a quoted error as often as a goal.
  - It covers the **continuation lines** of a multi-part message. Lean splits
    one error across `error:` and a following `Note:` or `Hint:` line, and
    `02-terms` found that the second line was not being recognised. Both are
    now stems.
  - It **downgrades, it does not silence.** Grammar inside a diagnostic is not
    an order error, but a unit displaying a message *about* a construct the
    reader has not met is still showing them something unreadable, and that is
    an editorial question worth asking. You get a `diagnostic` **warning**
    naming the construct and the unit that introduces it. If you have looked and
    the exhibit is in the right place, `ledgerAllow` it — that is what the
    waiver means here, and it will not go stale.

  Only grammar is downgraded. A **lemma name** inside `simp?` output is still a
  citation, and so is `∗`.

---

## 8. `calc` is in the Lean but not in the ledger

`calc_demo` in `lean/edition2/new-overview.lean` uses `calc`, which has no row in
§E. It sits in fragment `02-terms`. Either `02-terms` introduces `calc` properly
— it is worth teaching and the fragment already has a demonstration compiled —
or the declaration is dropped from the fragment. `02-terms`' author decides and
records the decision in their summary.

`ledger.json` now carries a `calc` row at `02-terms` so that a later unit using
`calc` is not silently unchecked. If `02-terms` drops the declaration instead,
the row moves to wherever `calc` is first taught, or comes out.

---

## 9. `site/content/` still holds the seventeen Edition-1 files

`00-overview.js`, `01-m0.js` … `16-ref.js`. They are the old course, kept on this
branch until integration. Do not edit them, do not read them for guidance on how
to write — their prose is what the client rejected — and ignore them in tool
output. `render-check.js` renders them alongside yours; that is expected.

---

## 10. Forward references: the legitimate kind and the defect

This is the distinction the whole edition turns on, so it is written down once,
here, rather than rediscovered per unit.

**A forward reference the prose openly marks as not-yet-readable is legitimate.**
It is the course's chief structural device: §D's promissory note says, in as many
words, *you cannot read this yet, and Unit 28 proves it*. Waive it **by name**,
with `ledgerForward` (prose) or `ledgerAllow` (anywhere), so a reviewer sees
exactly what was waived and can check that the prose really does say so.

**A forward reference the prose pretends the reader can follow is a defect.**
Not a waiver case. Fix the page.

That is the difference between a course that leaves nothing hanging and one that
leaves things hanging. If you cannot point at the sentence that admits the
reader cannot follow the exhibit yet, you do not have the first kind.

Never silence the checker wholesale, and never waive a name you have not looked
at. A waiver listing something that would not have fired is now reported as a
**stale waiver** warning, so waivers cannot rot quietly.

### `00-aliasing` — what its author and reviewer must add

`node site/tools/e2/ledger.mjs 00-aliasing` reports five order errors. All five
are inside the promissory-note exhibit — the one block in the course that is
*supposed* to be unreadable on first contact — and the fix is a `ledgerAllow` on
the **chapter object**, not a change to the page:

```js
registerChapter({
  id: 'aliasing',
  ledgerAllow: ['∀', 'leading-dot name resolution (.ctor)', 'Hoare', 'ptsAtLeast', 'aAnd'],
  ...
});
```

Verified: with exactly that list the unit is green. Three notes for the reviewer.

- **Quote shape-row names verbatim.** `∀` and
  `leading-dot name resolution (.ctor)` are the ledger's own row names — the
  checker matches waivers against them literally. Get one wrong and you get a
  stale-waiver warning, not a silent pass. That is deliberate.
- **`ledgerAllow` is chapter-wide.** Waiving `∀` waives it for the whole of
  `00-aliasing`, not just for that block. Acceptable here, because the unit has
  one exhibit and it is `sketch`-tagged; it is the reviewer's job to confirm no
  *other* block leans on the waiver.
- **`classical_conjunction_rule_is_false` does not need waiving** and should come
  out of `ledgerForward` — the block *declares* it, and declaring is not citing.
  The checker is deliberately silent about a unit declaring a theorem the ledger
  books elsewhere; §D wants that statement on page one and §E's row is where it
  is *proved*.

The `✝` in the goal display is **no longer an error** and needs no waiver — see
§11.

---

## 11. `✝` appears at `00-aliasing` and is explained at `01-goalstate`

> **Superseded in part by §15.** This section originally put the explanation at
> `04-funext`. `01-goalstate` has since taken it, and the ledger's `concept` row
> moved with it. The half that still stands is the first: the glyph *appears* at
> `00-aliasing` and its row is booked there. Read §15 for the rest.


§E.2 books the inaccessible-name dagger at unit 03 (`04-funext`) as a "first
sighting". But §D.0 mandates that x02 is scaffolded with `intro ⟨h3, _⟩`, and the
goal Lean really prints after that carries a `right✝`. PEDAGOGY §10 forbids
inventing a goal state, so the dagger is unavoidable on page one.

**Decision: split it the way `⟨…⟩` is split.** The glyph *appears* at
`00-aliasing`, deliberately unexplained — that is the exhibit, not a violation —
and is *explained* at `04-funext`, then named properly at `22-exec`. The ledger
row moved to `00-aliasing`; a `concept` row at `04-funext` records the other
half. `00-aliasing` owes the reader one clause saying the name is not theirs to
type; it already has one.

---

## 12. `runIf` is not a migration. Nobody can reproduce its goal state

Previously listed as `migrate`. It is not: **no `def runIf` exists anywhere** —
not in `content/`, not in `lean/`, not in the fragments. Edition 1 quotes a goal
state from a declaration that is not in the repo, which makes that goal state
unverifiable, and "goal states are real" is not a rule that bends for a
comparison.

`24-interpreter`'s author picks one, and records which in their summary:

- **write it** — the variant interpreter, the `ite` case spelled with `if`
  instead of `match`, about fifteen lines — compile it, and **re-derive the
  goal**. If the re-derived goal differs from Edition 1's, the re-derived one
  wins.
- **drop the comparison** and say so. It is an optional lab unit; that is a
  legitimate call.

What is not available is quoting a goal state nobody can reproduce.

---

## 13. §E numbers units; §D numbers files. They are three apart, twice

§E's "introduced" column is a **unit** number, 00–38. Every file id in §D is a
**file** number, 00–43, because five support pages are interleaved
(`01-goalstate`, `06-errors`, `20-compare`, `42-tactics`, `43-ref`). Unit 00 is
file `00-aliasing`; unit 01 is file `02-terms`; unit 05 is `07-heap`; unit 12 is
`14-assertions`; unit 18 is `21-language`; unit 38 is `41-beyond`.

`ledger.json` stores file ids throughout, and its top-level `note` field states
the translation. The offset is the easiest thing in this project to get wrong by
one, so the two audiences get different vocabularies and neither gets both.

**Writing for the reader — use unit numbers.** On the page, in prose, in a
`note`, in a hook: "Unit 28 proves it". The reader has never seen a file id and
never will; what they see is the sidebar badge, which carries the unit number.
§D's own text does this and it is right.

**Writing for another author or for a tool — use file ids.** Summaries, commit
messages, ledger rows, anything you say to a reviewer, anything you type at
`ledger.mjs`: "introduced in `12-pcm`", never "introduced in unit 10".

So a single unit legitimately says "Unit 28" on its page and `31-aliasing-closed`
in its summary. That is not an inconsistency; they are different readerships.

**Consequence for `num`.** The chapter's `num` field is the **unit** number from
its §D heading, *not* the file prefix. `31-aliasing-closed.js` carries
`num: '28'`. Support pages carry `§`, per §C.

**The badge is content identity. It agrees with the filename for `00-aliasing`
and never again.** Do not derive it — **§14 has the whole 44-row table; copy your
row.** `lint.mjs` fails your file if `num` disagrees with it.

(Edition 1 set `num` to the module name, `'M0'` — the badge has always been
content identity rather than file position.)

---

## 14. The badge table — copy your row

`num` is the **unit** number from the unit's §D heading. It is not the file
prefix, and it is not something to work out. Find your file, copy the value.

| file | `num` | | file | `num` |
|---|---|---|---|---|
| `00-aliasing` | `'00'` | | `22-exec` | `'19'` |
| `01-goalstate` | **§** | | `23-induction` | `'20'` |
| `02-terms` | `'01'` | | `24-interpreter` | `'21'` |
| `03-compute` | `'02'` | | `25-hoare` | `'22'` |
| `04-funext` | `'03'` | | `26-small-footprint` | `'23'` |
| `05-update` | `'04'` | | `27-locality` | `'24'` |
| `06-errors` | **§** | | `28-local-heap` | `'25'` |
| `07-heap` | `'05'` | | `29-local-compose` | `'26'` |
| `08-heap-laws` | `'06'` | | `30-frame` | `'27'` |
| `09-footprint` | `'07'` | | `31-aliasing-closed` | `'28'` |
| `10-disjoint` | `'08'` | | `32-symbolic` | `'29'` |
| `11-union` | `'09'` | | `33-swap` | `'30'` |
| `12-pcm` | `'10'` | | `34-wp` | `'31'` |
| `13-splits` | `'11'` | | `35-listrep` | `'32'` |
| `14-assertions` | `'12'` | | `36-lseg` | `'33'` |
| `15-pointsto` | `'13'` | | `37-wand` | `'34'` |
| `16-star` | `'14'` | | `38-partial` | `'35'` |
| `17-star-algebra` | `'15'` | | `39-invariant` | `'36'` |
| `18-star-assoc` | `'16'` | | `40-variant` | `'37'` |
| `19-pure` | `'17'` | | `41-beyond` | `'38'` |
| `20-compare` | **§** | | `42-tactics` | **§** |
| `21-language` | `'18'` | | `43-ref` | **§** |

**Why they diverge.** The five support pages take a file slot but carry `§`
rather than a number, so every teaching unit after one of them sits at a file
prefix ahead of its unit number. `01-goalstate` is the first, which is why
`02-terms` is unit **01**. The gap widens to two after `06-errors`, to three
after `20-compare`, and stays there.

**`00-aliasing` is the only file whose prefix equals its badge.** That is the
trap: the rule looks true on the first page anyone writes, and is false on every
page after it. `05-update` is unit **04**; `21-language` is unit **18**;
`41-beyond` is unit **38**.

**It is checked, not merely documented.** `tools/e2/lint.mjs` derives this table
from `ledger.json`'s `order` plus the support-page set and fails your file if
`num` disagrees, so a wrong guess is reported the moment you run the linter
rather than at integration. The table above is generated from the same two
inputs, so the two cannot drift apart.

**Why it matters more than it looks.** A wrong `num` is the one error in this
project that is invisible to its author, ships to the reader, and appears on
every page of the unit — the sidebar would skip 01 and 06 and read as broken.
Nothing in `COURSE-PLAN.md` would catch it: the plan gives every unit a `file`
and a `phase` and never once mentions `num`.

**This table is the bridge between the two vocabularies of §13.** The reader sees
the left column's `num`; you and your reviewer speak in file ids. When your page
prose says "Unit 28 proves it" and your summary says `31-aliasing-closed`, this
is the table that says those are the same thing.


---

## 15. `✝` is explained on `01-goalstate`, not at `04-funext`

§11 above ruled that the dagger *appears* at `00-aliasing` and is *explained* at
`04-funext`. That ruling was taken with only those two units in view. §D's entry
for the support page `01-goalstate` mandates, in its own contents list, "`✝`
daggers and inaccessible names, and the fact that `✝` is not an input
character" — and `01-goalstate` now carries the full treatment: what the glyph
means, the `funext _` exhibit that produces one, the real compiler output you get
from pasting one back in, and a `detail` on the superscripts counting backwards.

**Decision: `01-goalstate` owns the explanation.** It is a permanent reference
page, linked from every `trace` block, and this is the kind of material a reader
returns to rather than reads once. §11's ledger row is unaffected — the glyph is
still booked at `00-aliasing`.

**Author of `04-funext`:** you inherit `✝` as *known*. `funext _` producing an
inaccessible name needs no paragraph from you; say what `funext` gives you when
you *do* name it and move on. If your unit is the first place a dagger costs the
reader something concrete, show that — but do not re-derive what the glyph means.
The tactic that renames one after the fact (`rename_i`, booked at `22-exec`) is
still yours to leave alone: `01-goalstate` deliberately does not name it, and
says only that the repair *there* is to go back and supply a name.

---

## 16. The Check panel silently swallowed every `trace_state`

`assets/editor.js` filtered information messages with `m.severity === 'info'`.
Lean's own word, confirmed against the WASM build's JSON output, is
**`information`**. The filter matched nothing, so `trace_state`, `#check` and
`#eval` output was parsed, counted, and then dropped before rendering — a reader
following `01-goalstate`'s advice to "drop a `trace_state` in anywhere" would
have seen a green box and no goal.

Fixed in `assets/editor.js` (`renderResult`): the filter now accepts
`'information'`. Errors and warnings were never affected.

Two related facts, for anyone writing about the panel: the info box is
`--card-2`, a plain neutral card, **not blue**; and `lean-runtime.js` reports
columns 1-based (`at.column + 1`) where the CLI and `check.sh` print them
0-based, so the same message is `snippet:2:8` on the command line and
`line 2, col 9` in the workbook.
---

## 17. Two ledger rows found wrong by `02-terms` — BOTH APPLIED

Both were found by writing the unit. Both have since been verified against the
fragments and **applied to `ledger.json`**; this entry is the record of why.
(Numbered 17 because two other sections claimed 15 and 16 in parallel.)

**(a) `;` (two tactics on one line) is needed at `02-terms`, not `04-funext`.**
§E.1 books it at unit 03. But `or_comm_tac`, verified corpus and the *only*
`∨`-elimination proof the reader gets, is written

```
  · right; exact hp
  · left;  exact hq
```

in `lean/e2/02-terms.lean:32`. The semicolon is therefore on the page two units
before its row, exactly as `fun`, `→`, `∧` and `⟨…⟩` were in §3. `02-terms`
introduces it in one clause where the corpus forces it. §E.1's "first use 04" is
unaffected.

**Applied: the row is at `02-terms`.** Independently confirmed before moving —
`02-terms.lean` is the *earliest* fragment in the whole corpus containing a
one-line semicolon, so no unit before it is affected.

**`02-terms`' author: delete `ledgerAllow: ['; (two tactics on one line)']` from
`content/02-terms.js`.** The checker already says so — with the row moved, the
waiver suppresses nothing and `ledger.mjs 02-terms` reports it as a **stale
waiver**. That is the mechanism working as designed; the unit is otherwise clean.

**`04-funext`'s author: treat the semicolon as already met.** Do not introduce
it.

**(b) The `calc` row at `02-terms` is stale.** ERRATA §8 gave `02-terms`' author
the choice of teaching `calc` or dropping `calc_demo` from the fragment. Neither
was needed in the end (**applied**): **`calc_demo` is no longer in
`lean/e2/02-terms.lean` at all** — it is at `lean/e2/03-compute.lean:6`, where it sits among the equality
material it belongs to. `02-terms` does not use `calc`, does not mention it, and
teaches `.trans` instead as the way to chain two equations. **The row belongs at
`03-compute`**, whose author owns the declaration and must introduce the syntax.

**(c) Not an error, but know about it.** `ledger.mjs 02-terms` reports one
warning: `lookup_of_unallocated` — not in the ledger and not declared in the
verified Lean. That is correct and expected. `00-aliasing` tagged it
`illustration` and deliberately kept it out of its fragment (see that unit's
summary), and `02-terms` opens by citing it, because its `(hx : x ≠ 4)` binder
is the thing this unit exists to explain. Any later unit citing it gets the same
warning.

---

## 18. The block budgets were set too low. They are shape, not a cap — and the summit is protected

Three units in, every one has landed at or near §C's 40-block ceiling: `00-aliasing`
40 against a budget of ~26, `01-goalstate` 37 against ~14, `02-terms` 40 against
~30. That is a trend, so it was checked rather than waved through, and the prose
was read looking for padding.

**There is no padding.** The extra blocks are things like what `✝` actually is —
output only, not an input character, so pasting it back does not even reach the
"unknown identifier" complaint — which is exactly what a reader learning Lean
needs and exactly what Edition 1 never says. The budgets in §D were written
before a single unit existed, for an audience the plan then changed. They were
wrong.

**Ruling: the per-unit block budgets are advisory, and describe SHAPE — how many
traces, how many asides, roughly how many screens — not a ceiling on explanation.**
Write what the material needs for a reader who has never seen Lean. If that is
40 blocks, write 40.

Two things this ruling does **not** license.

**It is not permission to pad.** The test is unchanged and is in PEDAGOGY §4: a
sentence that would not change what the reader does or believes comes out. Every
block must serve the unit's one job. "The budget is advisory" is not an answer to
"what is this paragraph for".

**It does not flatten the course.** §C's range is 16–40 and three consecutive
units have hit 40, which is what a *target* looks like rather than a range. The
plan's relative weighting is the part that still binds: the summit units —
`27-locality` through `31-aliasing-closed`, and `32-symbolic` through `34-wp` —
carry the hardest material in the course and were given the largest budgets on
purpose. **An introductory unit that spends a summit-sized budget is borrowing
from the end of the course, and the end of the course is where the reader is most
likely to be abandoned.** If you are an early unit at 40 blocks, you are at the
ceiling and the material had better be there. If you are a summit unit, 40 is
your *floor* and you should say so in your summary if you needed more.

At the current rate the finished course is roughly 1,700 non-`ex` blocks and
230,000 words — a full textbook, about seventy per cent larger than the plan
projected. That is accepted deliberately: the client asked for a course that
"explains anything not previously mentioned" and "leaves nothing hanging", and
that is what it costs. What is not accepted is the back half being thinner than
the front.

---

## 19. Nine rows added by sweeping the fragments — including `absurd`

`02-terms` noticed that `Or.elim` had no ledger row: corpus `or_comm'` is
`fun h => h.elim Or.inr Or.inl`, the reader's first and only `∨`-elimination,
and the unit teaches the dot-notation resolution rule on it. **An unrowed name
is invisible to the checker** — nothing fired, and nothing would ever have
fired. That is the one failure mode a ledger check cannot report on itself.

So the fragments were swept for every name the verified Lean uses that
`ledger.json` had no row for. Nine rows added:

| row | unit | why |
|---|---|---|
| `Or.elim` | `02-terms` | §E lists `Or.inl`/`Or.inr`/`Or.symm` and not the eliminator |
| **`absurd`** | `03-compute` | **§E.1 has this row. It was dropped in transcription.** |
| `False`, `True` | `00-aliasing` | §E.2 books `¬ P` as `P → False` at unit 00, so `False` is met there |
| `Option.some`, `Option.none` | `00-aliasing` | `some`/`none` were rowed, the qualified spellings were not |
| `trivial` | `10-disjoint` | closes a `True` goal in `singleton_disjoint`; not in §E at all |
| `Type` | `02-terms` | §E books `Prop` at 00 and `Sort u` at 12 (`14-assertions`) and never `Type` |
| `Repr` | `21-language` | §E.2 books `deriving Repr`; the bare name had no row |

**`absurd` is the one that matters, and it was a process failure, not a plan
gap.** Say this plainly, because the distinction decides what gets fixed:

> **`COURSE-PLAN.md` §E.1 has the row.** It reads
> `` | `absurd` | **02** | 08 | ``. The plan did not forget it. **It was
> dropped in transcription**, when §E.1 was converted into `ledger.json`, and
> the loss went unnoticed for the entire project up to this point — through the
> building of all thirty-nine Lean fragments and three finished units.

Nothing on any page was ever wrong: every use of `absurd` falls after
`03-compute`, so there was nothing to catch. The check was simply absent. But
`absurd` is one of the five constructs in the plan's *own* opening example of
what Edition 1 got wrong, so of all the rows to lose in transcription, it was
the worst one — and it was invisible precisely because the ledger's own coverage
was the thing that failed.

The fix for a plan gap is to amend the plan. The fix for this is `--sweep`, run
routinely, because hand transcription of a 500-row table will lose rows and no
amount of care changes that.

**`Type` is booked at `02-terms`, not where it first appears in Lean.** It shows
up in Lean at `12-pcm` (`structure PCM where Carrier : Type`) but on the page at
`02-terms`, in the propositions-as-types material. §E's rule is about
*mentioning*, so the mention wins. `14-assertions` still owns universe
polymorphism.

**A blind spot this sweep also exposed.** The checker only treats a token as a
possible citation if it contains `_` or `.`, or is CamelCase. A lowercase name
with no underscore — `absurd`, `trivial`, `ite` — is invisible unless it already
has a row. The sweep therefore cannot be replaced by the checker.

**It is now a mode of the tool, and it runs on every invocation.**
`node site/tools/e2/ledger.mjs --sweep` lists every unrowed name; the bare run
prints the count whether or not anything else fails. It is not left to anyone's
memory, because forty-one units are still to land and a check that runs only
when someone recalls it stops running.

**When to sweep: when *Lean* lands, not when a page is written.** Adding Lean is
what introduces names; writing a page only cites them. `02-terms`' author made
this point and it is the important half — a missing row found *mid-authoring*
reads as an authoring problem and gets waived, while the same row found by a
sweep reads as a ledger problem and gets fixed. Same defect, opposite outcome,
decided purely by when it surfaces. Four of the nine restored rows sit at
`00-aliasing`: that debt was there from the very first fragment and survived
three finished units.

**The sweep does not report shape rows, and that was checked rather than
assumed.** Core syntax is tracked by *shape*, not by name — `fun` and `by` have
no rows of their own; they are covered by `fun x => e` and `:= by` through the
`re` field. A sweep matching on names alone would have reported every such
construct as missing and tempted someone into adding duplicate rows that then
disagree with the shape rows. Eleven core keywords were probed against the real
fragments — `fun` (124 uses), `by` (236), `match`, `with`, `if`, `then`, `else`,
`at`, `where`, `deriving`, `generalizing` — and **every one is either covered by
a shape row's `re` or has its own row**. The sweep is `re`-aware. The decision
that core syntax stays shape-tracked is recorded on the `theorem` row in
`ledger.json`, so the next sweep does not re-litigate it.

**Result of the first full-corpus pass: clean.** All thirty-nine fragments,
every name rowed. Two rounds got there — nine rows from the first pass, then
seven more when `03-compute`'s fragment landed (`double_unfold`, `double_three`,
`double_zero_left`, `some_inj`, `some_ne_none`, `some_ne_none'`,
`defined_of_ne_none`), plus `double` and `defined` losing their `⧗`.

---

## 20. Prove your exercises against the reader's own context

There is now one more check, and it is the only one that tests what the reader
actually experiences: that someone who types the solution you show gets a green
tick.

```
node site/tools/e2/gen-contexts.mjs --prove
```

For every exercise it splices `lean/e2/*` — cut immediately before that
exercise's own `/- ex … -/` marker, exactly as the browser cuts it — in front of
the `sol` your page displays, and runs Lean over the result. About half a second
per exercise.

`verify.sh` does **not** cover this. It compiles the corpus with every solution
already in place, so it cannot see a cut in the wrong position. The two failure
directions this catches:

- **cut too late** — the exercise's own answer is inside its context, so Lean
  says `has already been declared` instead of checking the reader's proof. The
  reader cannot pass, and the message does not tell them why.
- **cut too early** — a lemma your page told them to use is not in scope, so
  their correct proof is rejected with an unknown identifier.

It also catches a solution that quietly stopped compiling because a unit before
yours changed something underneath it, which nothing else you run will notice.

**If your exercise's solution has no `/- ex <id> <name> -/` marker in the Lean,
the tool says so and refuses to write.** Add the marker on its own line
immediately above the declaration that answers the exercise, in your unit's
fragment. The marker is the cut point: it is what tells the browser how much of
the course to put in front of the reader.

Run it after you add or change any exercise. It is cheap, and it is the check
that stands between a reader and an hour lost to an error message about a
theorem they never wrote.

---

## 21. Where the `/- ex … -/` marker goes: before the ANSWER, not before the setup

The marker is the cut point. Everything above it is what the reader has;
everything below it is what they are being asked to produce. So it goes
immediately before **the first declaration that is part of their answer** — and
not before a definition the unit is handing them to work with.

Two exercises in `03-compute` had it wrong and `--prove` caught both:

```lean
/- ex x09 defined -/                 ← WRONG: cuts `defined` out of the context
def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v

theorem defined_of_ne_none … : defined h l := by …
```

The page hands the reader `defined` and asks them to prove
`defined_of_ne_none`. With the marker above the `def`, their context stops
before it, so the statement they are shown mentions a name that does not exist
yet, and Lean answers `Function expected at defined` — an error about the
exercise's own setup, which no reader will diagnose. The marker belongs between
the `def` and the `theorem`.

**The discriminator is whether the `def` is in your `sol`.** If the reader writes
it, it is part of the answer and the marker goes above it. If you hand it to
them, it is setup and the marker goes below it. `x01` is the opposite case and
is correct: writing the heap *is* the exercise, so the marker sits above its
`def`.

Five markers elsewhere in the corpus sit above a definition and have not been
checked, because their units are not written yet — `x23 heapPCM`, `x41
Atom.size`, `m7-4 clearCell_spec`, `m7-5 readAndFree_spec`. If one is yours,
decide it deliberately, and then let the tool confirm it:

```
node site/tools/e2/gen-contexts.mjs --prove
```

Nothing else finds this. `verify.sh` compiles the corpus with every solution
already in place, so a cut in the wrong position is invisible to it. Only
splicing the context the way the browser splices it, and running the reader's own
answer through Lean, tells you what the reader will actually see.

---

## 22. A design [G] exercise cannot hide its statement without a placeholder `goal`

Found writing `05-update`'s `x13`, the course's first **[G]** exercise, and it
will recur at every later one (`x29`, `x30`, and the rest of the `G` column
in §F).

PEDAGOGY §8 says a [G] exercise "ships with the statement the reader is expected
to arrive at (**revealed at rung 3**)". But the workbook mounts an editor **only**
on an `ex` carrying a `goal` (`app.js`: `filter(b => b.t === 'ex' && b.goal)`),
and it renders that `goal` as a code block *above* the box. So putting the real
statement in `goal` reveals it at rung 0, and omitting `goal` costs the reader
the editor and the green tick entirely.

`lint.mjs` closes the third door: an `ex` with a `sol` and no `goal` is an
**error** ("has a solution but no 'goal'"), and an `ex` with neither is treated
as a design exercise with no Lean at all — which is not what these are, since
their `sol` is verified corpus.

**What `05-update` did, for want of anything better.** `goal` is a two-line Lean
comment plus a placeholder the reader deletes:

```lean
-- Delete the line below and write your own `theorem update_idem …`.
-- Any correct statement of the fact will be accepted.
example : True := by
```

`starterFor` requires the text to end `:=` or `:= by` — otherwise it appends
` := by\n  sorry` and mangles it — so the placeholder has to be a real opening.
The cost is one `lint.mjs` **warning** (`'goal' does not occur verbatim in the
verified fragments`), which is expected and should not be "fixed" by pasting the
statement in.

**If you are the author of a later [G] exercise:** either follow this, or fix it
properly — the clean repair is a `goalHidden` (or `starter`) field that seeds the
editor without rendering above it, which is about four lines in `app.js` and
`editor.js` plus a `lint.mjs` clause. Whoever does it should update this section
and `05-update`.

**Also found, and it is a plan slip rather than a tooling one.** §D Unit 04
objective 1 says the reader should "say which **three** rewrites `simp` fired in
each" of `update_same` and `update_other`. It is three in `update_other`
(`update`, `hne`, `↓reduceIte`) and **two** in `update_same` (`update`,
`↓reduceIte`) — `simp` settles `x = x` on its own, unprompted, so there is no
third. Confirmed with `simp?` against the Unit 04 prelude. The page states the
real counts and makes the difference the lesson.

---

## 23. Unit 04's payoff lands in TWO units, not one — 05 for the lookups, 06 for the equations

Found reviewing `05-update`. §D Unit 04 says the lab exists "so that when
`Heap.write` arrives in Unit 05 the reader recognises every proof". That is half
true and it misled the unit's first draft, which told the reader four separate
times that Unit 05 proves these five theorems again.

What the fragments actually hold:

- `lean/e2/07-heap.lean` (Unit 05) — six **lookup** laws: `singleton_same`,
  `singleton_other`, `write_same`, `write_other`, `erase_same`, `erase_other`.
  Every one is a one-line `simp [def]` or `simp [def, hne]`, i.e. the
  `update_same` / `update_other` shapes. **`funext` does not occur in the file.**
- `lean/e2/08-heap-laws.lean` (Unit 06, the LAB) — the **equations between
  heaps**. `write_shadow` is `update_shadow` line for line with `Heap.write` for
  `update`; `write_comm` is `update_comm` line for line; `write_of_eq` is the
  hypothesis-carrying generalisation of `update_idem`. This is where `funext`,
  the three-region hand-driven analysis and the `have` land.

So the `funext` + `by_cases` + `<;> simp` shape that Unit 04 installs is spent in
Unit **06**, and only the two lookup shapes are spent in Unit 05. `05-update` now
names the destination theorem for each of its five exercises, which cost six
`ledgerForward` entries and is worth them: a promise to a named theorem is one a
reviewer can check, and `ledger.mjs` reports a stale waiver the moment the
sentence carrying it is deleted.

**Authors of `07-heap` and `08-heap-laws`:** `05-update` makes these promises by
name. If your fragment stops honouring one, that page changes, not the promise.

**One more thing `05-update` names that no other early unit does.** `Store` is
`Var → Val` is `Nat → Nat`, so `update` is already at the store's type — §D Unit
02 says the abbrevs are given meanings there precisely "so Unit 04's `update` is
visibly the store", and nothing had made it visible. It is now one clause in the
brief. `21-language`'s `storeSet_same` / `storeSet_other` are literally
`update_same` / `update_other` applied; that is fourteen units forward and is
left for `21-language`'s author to collect.

---

## 24. `verify.sh` proves declaration order, not tactic order — and five rows moved because of it

The finding, relayed from a session that has since ended: **`write_of_eq` in
fragment `08-heap-laws` (unit 06) was written with `subst`, which §E.1 books at
unit 08.** It compiled. `verify.sh` was green. Nothing caught it, and nothing
was ever going to, because:

> `verify.sh` only proves *declaration* ordering. It says nothing about *tactic*
> ordering. A fragment can compile perfectly and still teach a tactic three
> units before it exists.

That is the whole gap in one sentence, and it is worth reading twice, because
every author so far has read a green `verify.sh` as "my ordering is clean".

It also escaped `ledger.mjs`, which read `content/*.js` only: the fragment
existed for hours before `08-heap-laws.js` did, and **a tactic in a fragment
that no page has quoted yet is invisible to the content pass by construction.**

### The fix: `--fragments`, and it runs by default

`node site/tools/e2/ledger.mjs --fragments` runs the order check directly over
`site/lean/e2/*.lean`, mapping each fragment to its unit by filename. It is
merged into the default run and prints a `frags:` line every time, pass or fail,
for the same reason `--sweep` does — a check nobody remembers to run is a check
that does not run.

Because every fragment is already written, the first pass found the whole class
at once rather than one unit at a time. **Five violations, and all five were the
plan, not the authors.** Four rows moved:

| row | §E said | now | forced by |
|---|---|---|---|
| `match … with` | `11-union` | **`10-disjoint`** | `Heap.union`'s body is a `match`, and §D states `union` at `10-disjoint` so `splits` can mention it |
| `by …` in a term-mode slot | `17-star-algebra` | **`11-union`** | `union_eq_none` is `exact ⟨rfl, by rwa […] at h⟩`; `splits_comm` likewise. Six units early |
| `Bool` | `21-language` | **`17-star-algebra`** | §D retains `star_forall_right_fails`, whose family is `def Pcx : Bool → Assertion` |
| `cases … with \| ctor` | `22-exec` | **`03-compute`** | see §25 |

Each move follows the rule already set in §2, §3 and §17a: **the verified corpus
decides where a construct is first MET; §E's later row is where the LESSON
belongs.** That pattern has now recurred five times, and it is the single most
common defect in the plan. `21-language` still owns `Bool` versus `Prop`;
`11-union` still owns why `match` blocks reduction.

The `by …` case is worth singling out: the Edition-1 audit flagged exactly this
construct in `01-m0` and `03-m2`, so the shape predates the edition and survived
into the new corpus. It is now legal from `11-union`, where the proof needs it.

---

## 25. `cases` — the plan contradicts its own ledger

Two legal uses had no row: `cases x with | false | true` on a `Bool` *value*
(`17-star-algebra`), and `cases h` on `h : some v = none`, a *constructor
equality* (`03-compute`). §E.1 gives `cases` three rows — saved-equation at unit
02, inversion and `with | ctor` at unit 20 — and none of them covers either.

**Verified before encoding, because a row moved to fit the code would be worse
than no row:**

- **§D unit 02's exercise x08 prescribes it verbatim** — *"`some v ≠ none` two
  ways (`by simp`; `intro h; cases h`)"*. So this is the plan contradicting its
  own ledger, not an author freelancing.
- **No fragment before `03-compute` uses `cases` in any form.** `02-terms` uses
  `rcases`, which has its own row there.

**Decision: one new §E.1 row — *`cases` on a value of an inductive type, or on a
constructor-equality hypothesis* — booked at file `03-compute`.** Mind the
offset: §E unit 02 is file `03-compute`, not `02-terms` (§13). The row is
recorded in `ledger.json` with `check: false`, because the `cases` token row and
the `cases … with | ctor` shape row do the matching; it exists so the ledger
*states* the rule and §`tactics` can print it.

**The cost, stated plainly.** A regex cannot tell a value split from an
inversion on a derivation, so `cases … with | ctor` is now booked at the
earliest legal form. **Inversion on a derivation used before `22-exec` will not
be caught.** `22-exec`'s author must check that by eye. This is the third
`cases` blind spot and they all have the same cause: §E splits one token across
three units, and a tokeniser cannot follow.

**Consequence for `03-compute`:** its `ledgerAllow: ['cases … with | ctor']` is
now stale and the checker says so. Delete it.

---

## 26. Term-mode `by` in an ARGUMENT, not just a tuple slot — and a row I booked wrong

Two findings from `10-disjoint`'s author, both verified, both mine to own.

**(a) The regex could only see half the construct.** The row for §E.2's
"`by …` inside a term-mode tuple slot" was `,\s*by\b` — comma-anchored. So it
saw `⟨rfl, by simp⟩` and was blind to `absurd h (by simp)`, the same construct in
argument position. That is not a corner case: **PEDAGOGY §2 quotes
`exact absurd h (by simp)` as the canonical Edition-1 violation**, and
`10-disjoint.lean`'s `singleton_disjoint_iff` ended with exactly that line, one
unit earlier than the row I had just claimed was "the earliest in the corpus".
My verification was as narrow as my regex.

Fixed: the regex is now `[,(]\s*by\b` and the row is renamed **`by …` inside a
term (tuple slot or argument)**, because that is the construct — a tactic block
standing where a term is expected. Its author fixed the fragment at source
(rewritten to `cases h`, booked at `03-compute`, constructor no-confusion), so
the `11-union` booking is now correct as written.

Widening immediately paid for itself: **two more Edition-1 violations**, and one
in a live Edition-2 page — `03-compute.js` `blocks[38]` has
`absurd h (by simp)` in an `illustration`, seven units before the row.
`03-compute`'s author: your own fragment already proves the same fact the other
way, with `cases h` at `03-compute.lean:29`. Align the page with the fragment, or
make the case for moving the row — but the row does not move to fit a page.

**(b) `trivial` was booked at the wrong unit, and it was my typo.** The row said
`10-disjoint` and claimed the name was "first used in 10-disjoint's
`singleton_disjoint` tuple". There is no `trivial` in `10-disjoint.lean` and that
theorem has no tuple. Its only two uses in the entire corpus are
`17-star-algebra.lean:72` and `:75`. The sweep that found the name had correctly
reported `17-star-algebra`; I typed the wrong unit into the patch. Moved. The
clause is owed by `17-star-algebra`, not `10-disjoint`.

**The check that now catches this class.** No existing check could: the sweep
only asks *is this name rowed at all*, the fragment pass only catches rows that
are too LATE, and a row booked too EARLY is merely permissive, so nothing fails.
But it is still a lie in the ledger and it hands the teaching obligation to the
wrong author. `--audit` now re-derives, for any row marked
`derived: "first-use"`, the earliest fragment that actually uses it, and reports
a mismatch either way.

**The marker is deliberately narrow.** It means *this row's unit is a claim
about observed first use*. Rows booked on pedagogical grounds — where the reader
**meets** a thing rather than where the Lean first uses it — must not carry it.
I marked fifteen rows on the first attempt and the check drowned: `False` at
`00-aliasing` (because `¬ P` is `P → False`) and `Type` at `02-terms` (because
the page teaches propositions-as-types) are *correct* despite the Lean not
touching them until `14-assertions` and `12-pcm`. Fifteen markers removed, one
kept. A check that reports correct decisions as defects gets switched off.
