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
  class …</code>` — is Lean talking, not you citing. Lines that came out of a
  span matching a diagnostic stem are exempt from `keyword` and `command` rows.
  `06-errors` exists to print twelve of these and would otherwise be unwritable.
  Note the limit: only grammar is exempted. A **lemma name** inside `simp?`
  output is still a citation, and so is `∗`.

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

## 11. `✝` appears at `00-aliasing` and is explained at `04-funext`

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

