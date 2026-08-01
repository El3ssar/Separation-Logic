# Separation Logic in Lean 4 — Edition 2

## The course plan

This document is the whole specification. A chapter-writing author receives it, the summaries
of the units written before theirs, `AUTHORING.md`, `PEDAGOGY.md`, and `lean/corpus.lean`.
Nothing else. It must therefore be complete, and every claim in it about Lean must be true.

Every piece of new Lean this plan commits to has been written and compiled under Lean 4.32.2,
no imports, no Mathlib, no `sorry`. It lives in `site/lean/edition2/new-<prelude>.lean`, one
file per chapter prelude it was checked against:

| file | checked against | contents |
|---|---|---|
| `new-overview.lean` | `prelude/overview.lean` | the aliasing refutation; the 13 Module 0 bootstrap declarations |
| `new-m1.lean` | `prelude/m1.lean` | `heap_ext`, `erase_erase`, `write_erase_same`, `erase_write_comm`, `erase_comm`, `write_empty`, `write_of_eq`, `update_idem`, the footprint exhibits |
| `new-m2.lean` | `prelude/m2.lean` | `self_disjoint_iff_empty`, `union_self`, `union_cancel_left` |
| `new-m4.lean` | `prelude/m4.lean` | `PCM`, `heapPCM`, `pcmStar`, `pcmStar_comm`, `pcmStar_unit_left`, the `⊣⊢` toolkit, `star_congr`, `no_star_weakening`, `no_star_duplication`, `starNoDisj_dup`, `star_same_loc_absurd`, `star_intro`, `star_or_right`, `star_exists_right`, `or_left/right/elim` |
| `new-m5.lean` | `prelude/m5.lean` | `@Store.set = @update`, `Atom.size`, `exec_load_stuck`, `exec_assign_inv`, `exec_load_inv`, `exec_skip_seq_inv`, `allZeros_length`, `append_nil`, `exec_id` |
| `new-m8.lean` | `prelude/m8.lean` | `heapLocal_ite`, `heapLocal_loop`, `write_union_no_disjointness`, `not_heapOnly_pure`, `frame_needs_preserves`, `free_with_frame`, `ptsAtLeast`, `classical_conjunction_rule_is_false`, `separated_write_ok` |
| `new-m9.lean` | `prelude/m9.lean` | `hoare_load_and`, `and_fact_star`, `and_fact_star_intro` |
| `new-m10.lean` | `prelude/m10.lean` | `listRep_cons_ne_zero`, `lseg_nil_iff`, `listRep_null` |
| `new-m11.lean` | `prelude/m11.lean` | `wand_unit`, `wand_curry`, `wand_uncurry`, `hole_intro`, `hole_elim`, `emp_wand_elim`, `emp_wand_intro` |
| `new-m12.lean` | `prelude/m12.lean` | `wp_sound`, `wp_weakest`, `wp_frame`, `hoare_ite`, `wp_ite` |
| `new-m13.lean` | `prelude/m13.lean` **truncated to line 1277** | `swap`, `swap_heap`, `swap_spec`, `drainBody`, `drain`, `drainInv`, `drain_step`, `drain_stop`, `drain_spec`, `countdown_keeps_cell` |

**Two facts about the repository that authors will otherwise discover the hard way.**

1. `site/lean/prelude/m13.lean` **does not compile.** Its last block redeclares `Cmd` and ends
   with an unterminated `hoare_load'`. `lean prelude/m13.lean` reports `` `Cmd` has already been
   declared `` and `unexpected end of input`. Truncating the file at line 1277 makes it compile.
   Fixing the prelude is a prerequisite task for Units 35–38.
2. There is **no Mathlib**. `set`, `omega`, `linarith`, `ring`, `simp_arith`, `aesop`,
   `Function.funext_iff` and `decide` on non-trivial propositions do not exist. `exact?` and
   `simp?` do exist and are worth teaching, but `exact?` without a library is feeble — asked for
   `b = a` from `h : a = b` it answers
   `exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm h))) a)`. That is a
   teaching moment, and the `errors` page uses it.

---

# A. AUDIENCE AND PROMISE

## A.1 Who this is for

A reader with **ordinary undergraduate mathematical maturity** and **no Lean at all**. They are
learning both subjects at once, and that is the design constraint that decides everything below.

**Assumed, and used without ceremony:**

- functions, including higher-order functions, composition, injectivity, domain and codomain;
- sets, subsets, membership, the empty set, disjointness as a property of sets;
- binary relations, and reflexivity / symmetry / transitivity;
- proof by induction on the natural numbers, and proof by cases;
- predicate logic as notation — `∧ ∨ ¬ → ↔ ∀ ∃` — and what a counterexample is;
- the idea that a definition is a *choice*, and that a choice can be judged by which theorems
  survive it;
- the idea that a program has a state and that running it changes the state.

**Not assumed, therefore taught here, each in the unit whose story needs it:**

| thing | introduced in |
|---|---|
| anything at all about Lean, type theory, dependent types | Unit 00 |
| propositions-as-types, proofs-as-terms | Unit 01 |
| definitional versus propositional equality | Unit 02 |
| decidability, and why `if` needs it | Unit 02 |
| partial functions and their `Option` encoding | Unit 02 (named) / Unit 05 (properly) |
| function extensionality as a genuine principle | Unit 03 |
| footprint; exact versus inexact ownership | Unit 07 |
| monoid, commutative monoid, **partial commutative monoid** | Unit 10 |
| substructural logic: weakening, contraction | Unit 14 |
| inductively defined relations; derivations; "no derivation" | Unit 19 |
| structural induction, the induction hypothesis, generalising it | Unit 20 |
| big-step (natural) operational semantics | Unit 19 |
| Hoare logic in any form | Unit 22 |
| locality as a simulation property | Unit 24 |
| least fixed points (as a foldable aside) | Unit 32 |
| adjunctions, from currying, with no category theory | Unit 34 |
| predicate transformers, weakest preconditions | Unit 31 |
| loop invariants and variants | Units 36, 37 |

Nothing in the right-hand column is used before its row. Section E is the enforcement mechanism.

No prior exposure to separation logic, Coq, Iris, VST or Dafny is needed or assumed.

## A.2 The promise — what the reader can do on the last page

**Lean.**

1. Read any declaration in this course's fragment and say what it claims — implicit binders,
   dot notation, anonymous constructors, inductive families included.
2. Write a term proof of any propositional or first-order fact, and say when a term proof beats
   a tactic proof. (About a fifth of the corpus is term proofs; a tactics-only reader cannot
   read the course's own solutions.)
3. Drive a tactic proof: `intro exact apply refine constructor obtain rcases cases by_cases
   induction … generalizing funext rw simp simp only simpa unfold subst have show left right
   absurd ▸ rename_i rwa`, focus dots and `<;>`.
4. Read a goal state — context, `⊢`, `case` tags, inaccessible names with `✝` — and read an
   error message well enough to name the tactic that failed and why.
5. Debug: shrink a `<;>` chain to focus dots, insert `sorry`, insert `trace_state`, run `simp?`,
   `#check @f`, `#print axioms`, `set_option pp.explicit true`.
6. Define an inductive relation, prove by inversion on it, prove by induction over its
   derivations, and know when `generalizing` is required and why.
7. Write a fuel-indexed interpreter Lean accepts as terminating, and prove it agrees with a
   relation in both directions.

**Separation logic.**

8. Build a heap model from nothing and prove it is a partial commutative monoid — where "is a
   PCM" is a Lean term they constructed, not a slogan.
9. State and prove the laws of `∗`, `emp`, `↦` and `-∗`, say which are entailments and which
   equivalences, and **prove the two laws that fail** — no weakening, no contraction.
10. Give a small imperative language a big-step semantics and a Hoare logic.
11. **Prove the frame rule** — for every command in the language, control flow included — from
    an operational locality property they derived from a stuck proof.
12. Verify heap-manipulating programs compositionally, without ever unfolding `Exec`.
13. Define recursive predicates for linked structures and prove the list-segment append theorem
    using only the `∗`-algebra.
14. Derive weakest preconditions and see that `Hoare P c Q` was `P ⊢ wp c Q` all along.
15. Prove partial and total correctness of loops, by invariant and by variant, and verify a
    terminating loop that owns a heap cell.
16. Say precisely which parts of the development were about heaps and which were about any PCM
    — by proving the commutativity of a generic PCM-induced `∗`.

## A.3 Prerequisites, precisely

A browser and the workbook; the exercises run a real Lean 4 kernel in a worker on the reader's
own machine. Optionally Lean 4.32.2 via `elan` locally — no `lake` project, no `import` lines
anywhere in the course.

Comfort with symbolic manipulation, and with the idea that a proof is an object one can be wrong
about. **Willingness to type.** This course is unusable as reading matter; every unit ends with
the reader having proved something.

Explicitly not prerequisites: functional programming, compilers, any proof assistant, category
theory, domain theory, lattice theory.

## A.4 What is deliberately out of scope

Concurrency, Iris, fractional permissions, ghost state, step-indexing. Each gets one sentence in
the closing unit saying what it is and which idea in this course it generalises.

Also out of scope, and **said out loud in Unit 00 rather than confessed at the end**: the
language's `load`, `write` and `free` take a literal `Loc`, not an expression, so a pointer held
in a variable cannot be dereferenced. Unit 38 states the one-line syntax change that removes the
limitation and shows that every theorem downstream survives it unchanged.

---

# B. THE NARRATIVE SPINE

One story, fifteen sentences. Every unit is locatable in this paragraph; if it is not, it does
not belong.

1. Hoare logic looks settled until memory enters it: the innocent rule
   `{[x]=3} [y]:=5 {[x]=3 ∧ [y]=5}` is **false** the moment `x` and `y` can be the same pointer,
   and the reader proves a shard of that falsity on page one — while the statement they actually
   want to refute is written down as a **named theorem with no proof**, a debt the course carries
   for twenty-eight units.
2. The classical repair — carry pairwise-distinctness hypotheses — works and destroys
   modularity, because every specification then mentions memory the routine does not touch; so
   the question becomes whether non-aliasing can be made a *consequence* of how assertions
   combine rather than a hypothesis dragged along.
3. That means changing what an assertion *means*: not "this is true of memory" but "this is the
   memory I own" — and to say that at all we need memory as a mathematical object, so memory
   becomes a partial function `Loc ⇀ Val`, encoded as a total function into `Option`, which
   immediately costs us `rfl` and forces function extensionality.
4. Eleven lookup and update laws later memory is opaque — manipulated only through its interface
   — and exactly four of the eleven carry a disequality, marking precisely where aliasing could
   bite; but the question "how much do you own?" is still open, and the two candidate readings of
   "`l` holds `v`" turn out to disagree about whether deallocation can be specified at all.
5. Owning *part* of memory means memory must split, so we define disjointness and union — and
   discover that the honest partial union is unusable in a total type theory, forcing a total
   left-biased union that carries disjointness as a separate hypothesis at every use.
6. Those operations satisfy exactly the axioms of a **partial commutative monoid** — associativity
   unconditionally, commutativity only under disjointness — and we build the PCM in Lean as a
   `structure` and instantiate it, so that "heaps form a PCM" is an object one can `#check` rather
   than a slogan.
7. Assertions are then predicates on a store and a heap, entailment is inclusion, the classical
   connectives lift pointwise and nothing has happened yet — until `emp` and `↦` are defined as
   *equations* on the heap, which finally decides the ownership question and yields the first
   ownership theorem and the first ownership refutation.
8. Now the connective: `P ∗ Q` holds when the heap splits into disjoint halves satisfying `P` and
   `Q` — and the first things proved about it are two **failures**, `P ∗ Q ⊬ P` and `P ⊬ P ∗ P`,
   because a logic that can neither forget nor duplicate a resource is a different kind of logic
   and every structural rule from here exists to compensate.
9. What `∗` does satisfy is the commutative monoid structure the PCM induces — unit,
   commutativity, monotonicity, distribution over `∨` and `∃`, and associativity, whose heap-level
   content was already proved as `splits_assoc`, so the assertion-level proof is bookkeeping.
10. None of that is about programs, so we build the smallest language that can get memory wrong,
    find that Lean refuses its interpreter, take the refusal seriously, and give the language a
    **big-step relational semantics** in which the absence of a derivation models crashing and
    diverging at once — then earn induction over a derivation, `generalizing` and all, on
    determinism.
11. A **Hoare triple** then says: from every state satisfying `P` there *exists* a terminating,
    non-faulting run landing in `Q` — one existential doing three jobs — and the primitive rules
    for load, write and free mention **exactly one cell**, which is sound only because `↦` was
    made exact, and which is immediately useless because two small rules will not compose.
12. What makes them compose is the **frame rule**, and it cannot be assumed, because it is a claim
    about what commands *do*: we write the textbook locality condition, run the frame proof into a
    wall, read the missing conjunct off the goal that cannot be closed, find a second and
    non-spatial gap from a three-line counterexample about a program variable, prove locality for
    every command including control flow, and then prove `hoare_frame` in eight lines with no
    axiom.
13. At that point the debt from sentence 1 comes due and is paid on the page: the classical
    conjunction rule is **refuted inside the logic**, and the same specification with `∗` in place
    of `∧` is **proved in four lines** by framing — the whole argument for the subject, compressed
    into two machine-checked theorems standing next to each other.
14. With framing, verification becomes calculation — split, frame, apply, renormalise — and
    reading the same equivalence backwards gives **weakest preconditions**, which are the same
    statement as a triple (`Iff.rfl`) but the mechanical direction.
15. Finally the ideas that scale: **recursive predicates** that assert shape and ownership in one
    breath, the **magic wand** as the right adjoint of `∗` and hence the algebra of a structure
    with a hole, **invariants and variants** for loops, ending on a terminating loop that owns a
    heap cell — and then, generically, the proof that everything in the first half used only the
    four PCM laws, which is why the same logic serves permissions, tokens and ghost state.

**In one sentence:** *Ordinary Hoare logic breaks on aliasing; the repair is to make assertions
assert ownership; ownership makes memory an algebra; the algebra makes the frame rule provable;
and the frame rule makes verification compositional.*

---

# C. MODULE STRUCTURE

**39 teaching units and 5 support pages**, in 10 modules. A *unit* is one `content/NN-id.js`
file: one sitting, 2–7 exercises, 16–40 non-`ex` blocks. A **LAB** introduces no new mathematics
and little new syntax; its job is guided practice, and it has a fixed four-part format (§C.1).
A **support page** carries the badge `§`, is off the narrative path, and says so.

Module boundaries are placed where the reader's *capability* changes, not where the subject
matter changes. No boundary falls in the middle of a proof technique.

| # | Module | Units | Files |
|---|---|---|---|
| 0 | Getting a proof past Lean | 00–04 | `00`–`06` (incl. 2 support pages) |
| 1 | Memory | 05–07 | `07`–`09` |
| 2 | The resource algebra | 08–11 | `10`–`13` |
| 3 | The logic of ownership | 12–17 | `14`–`20` (incl. 1 support page) |
| 4 | Programs | 18–21 | `21`–`24` |
| 5 | The program logic | 22–23 | `25`–`26` |
| 6 | Locality and the frame rule | 24–28 | `27`–`31` |
| 7 | Verification as calculation | 29–31 | `32`–`34` |
| 8 | Unbounded structures and the wand | 32–34 | `35`–`37` |
| 9 | Control and termination | 35–37 | `38`–`40` |
| 10 | Beyond | 38 | `41` (+ 2 support pages, `42`–`43`) |

## C.1 The lab format

A lab page is not a lecture with the prose deleted. Its structure is fixed and mandatory:

1. a one-paragraph **brief** saying what the reader is about to build and where it is spent;
2. a **worked example done in full** — the largest block on the page — with every goal state
   printed by `goalstate.sh`, the tactic named, one sentence on what changed, and one sentence on
   what a reader would plausibly have tried instead and why it fails;
3. the **exercises**, in a strict difficulty ramp, with at most one sentence of prose between
   them saying what is new;
4. a **retrospective**: three questions the reader should now be able to answer, with the answers
   in `detail` blocks.

A lab whose worked example is shorter than its brief has failed and must be rejected in review.

---

### Module 0 · Getting a proof past Lean — units 00–04

**Purpose.** The reader has never written a line of Lean. Before any heap exists they must read a
declaration, write a term proof, know why `rfl` sometimes fails, drive a tactic block, and prove a
function equality by `funext` plus a case split without being told to. Every example in this
module is a shard of the model or of the problem: 00 refutes the aliasing postcondition and issues
the course's promissory note, 01 proves the logical skeleton every `∗` proof will reuse, 02 builds
`Option` and meets the `if` that blocks every later proof, 03 installs the three-move heap
pattern, 04 proves the four `update` laws — which are the heap laws with `Option` removed.

**Why the boundary is here.** It closes when the reader can prove
`update (update f x a) y b = update (update f y b) x a` given `x ≠ y` — *independent updates
commute*, the baby frame rule, and the last thing that can be said about memory without splitting
it. Nothing in Module 1 can start before `funext` plus a case split is automatic.

**Why this replaces Edition 1's M0.** Edition 1 opens M0 with `Decidable` instances, stuck
`Nat.beq` matches and the difference between a simproc and a lemma — material that presupposes
typeclasses, instance resolution and reduction, none of which the reader has met — and then gives
four exercises before dropping them into heap lemmas. That is the single worst pacing failure in
the current course.

Units: 00 `aliasing`, §`goalstate`, 01 `terms`, 02 `compute`, 03 `funext`, 04 `update` (LAB),
§`errors`.

---

### Module 1 · Memory — units 05–07

**Purpose.** Turn "memory" into a Lean object with a closed interface, and then pose — not answer
— the question the whole course turns on. Six lookup equations characterise the four operations;
five equations between heaps close the interface; after Unit 06 no proof in the course unfolds a
heap operation. Unit 07 asks: given a location and a value, *which heaps* satisfy "`l` holds `v`"
— every heap mapping `l` to `v`, or the single one-cell heap? — and shows the two answers disagree
about whether `free` can be specified at all.

**Why the boundary is here.** Everything in this module is about **one** heap. The moment you ask
how much of a heap you hold you need two heaps and a way to combine them, and that is algebra
rather than analysis of a data structure.

Units: 05 `heap`, 06 `heap-laws` (LAB), 07 `footprint`.

---

### Module 2 · The resource algebra — units 08–11

**Purpose.** The mathematical heart of the first half, and the part that transfers verbatim to any
other resource model. Disjointness; the discovery that the honest partial union cannot be written
in a total type theory; the left-biased total union and the discipline it imposes; the nine laws;
the naming of the structure — a partial commutative monoid — and its **construction in Lean** as a
`structure` with `heapPCM` as an instance, so that every field is a theorem the reader has just
proved. The module ends at `splits_assoc`, the associativity of a partial operation, which is the
first proof whose difficulty is real rather than notational.

**Why the boundary is here.** No assertions, no logic, no programs — pure algebra of resources.
Keeping it sealed is what makes Unit 38's generalisation a theorem rather than a hand-wave.

Units: 08 `disjoint`, 09 `union`, 10 `pcm`, 11 `splits` (LAB).

---

### Module 3 · The logic of ownership — units 12–17

**Purpose.** Lift the algebra to a logic. Assertions and entailment (Unit 12) achieve nothing on
purpose, so the reader notices when something finally does: `emp` and `↦` as equations (Unit 13)
decide Unit 07's question. Then `∗` (Unit 14) with its definition, its two mechanical moves, and —
before any law — its **two failures**, because what makes this a different logic is what it cannot
do. Units 15–16 are the laws and associativity. Unit 17 introduces `pure` as the answer to a
question that can only now be asked, proves the non-aliasing theorem, and assembles the
normalisation library that Modules 7–8 consume.

**Why the boundary is here.** This is the last module with no programs in it. It ends when
assertions under `∗` and `emp` are a commutative monoid and the reader can prove an entailment
*without mentioning a heap*. That equational style is the working language of Modules 7–8; a
reader who has not crossed that line will grind semantics for the rest of the course.

Units: 12 `assertions`, 13 `pointsto`, 14 `star`, 15 `star-algebra` (LAB), 16 `star-assoc`,
17 `pure`, §`compare`.

---

### Module 4 · Programs — units 18–21

**Purpose.** Something to reason *about*, and the largest single new Lean skill in the course.
Syntax as an inductive type (18); execution as an inductive relation, with inversion (19);
structural induction built up from `Nat` to `List` to a derivation to `generalizing` (20); and an
executable interpreter proved to agree, so the semantics can be tested rather than trusted (21).

**Why the boundary is here.** This module mentions `∗` exactly zero times, deliberately, and says
so to the reader: two independent developments are being built and they meet in Module 5. Unit 20
exists as its own unit because induction on a derivation with a generalised hypothesis is the
hardest Lean technique in the course and recurs three more times (26, 36, and implicitly 37).

Units: 18 `language`, 19 `exec`, 20 `induction`, 21 `interpreter` (LAB, **optional**).

---

### Module 5 · The program logic — units 22–23

**Purpose.** Join the two threads, prove the structural rules, and state the primitive memory
rules on exactly the cells they touch. Then **fail**, deliberately and at length.

**Why the boundary is here.** The module is short and ends on a defeat: `readAndFree` cannot be
built by composing the load rule and the free rule, because the load's postcondition is not the
free's precondition, and the reader must drop back to `Exec.seq` and feel it. That felt need is
the entire motivation for Module 6, and manufacturing it is worth a page.

Units: 22 `hoare`, 23 `small-footprint`.

---

### Module 6 · Locality and the frame rule — units 24–28

**Purpose.** The summit. Unit 24 *discovers* the definition of `HeapLocal` by writing the textbook
version, starting the frame proof, and reading the missing conjunct off the goal that cannot be
closed — then finds the second, non-spatial gap from a counterexample about a program variable.
Units 25–26 prove locality command by command, control flow included. Unit 27 proves
`hoare_frame`. Unit 28 discharges the promissory note issued in Unit 00.

**Why the boundary is here.** Unit 28 is its own unit and not a closing section because it is the
*narrative* summit rather than the technical one, and a promise made on page one and kept
twenty-eight units later deserves a place the reader cannot miss. Units 25 and 26 are separate
because `heapLocal_write` and `heapLocal_free` are the two hardest pointwise heap arguments in the
corpus and must not share a page with the theorem they serve.

Units: 24 `locality`, 25 `local-heap`, 26 `local-compose`, 27 `frame`, 28 `aliasing-closed`.

---

### Module 7 · Verification as calculation — units 29–31

**Purpose.** Use the logic. A fixed four-move recipe — `hoare_seq`, `hoare_frame`, a small rule,
`hoare_consequence` — applied twice (29), then a four-command capstone the reader drives (30),
then the change of direction that turns verification from a search into a calculation (31).

**Why the boundary is here.** This is the first module in which no new semantic object is defined:
everything is composition of things already proved, and that change of character is worth telling
the reader about. `wp` sits at the end because it answers the question Unit 30 generates — "these
four intermediate assertions were all forced by what the next command needed; can they be
computed?" — and a predicate transformer put in front of a reader who has not yet chosen an
intermediate assertion by hand and found it painful is a definition with no question attached.

Units: 29 `symbolic`, 30 `swap` (LAB/capstone), 31 `wp`.

---

### Module 8 · Unbounded structures and the wand — units 32–34

**Purpose.** Assertions describing unboundedly many cells, and the connective describing a
structure with a hole. Unit 32 makes the double reading explicit — a recursive separation-logic
predicate is simultaneously a shape invariant and an ownership claim. Unit 33 proves the append
theorem by an induction carried out **entirely in the assertion algebra**, and uses the theorem
one cannot prove to diagnose a wrong definition. Unit 34 defines `-∗`, proves the adjunction, and
cashes it out as the hole pattern.

**Why the boundary is here.** Units 32–33 are the first place the `∗`-algebra of Module 3 is used
in anger rather than for bookkeeping: the cons case of `lseg_append` is five lines, no heaps, all
Module 3 lemmas. That dividend is the point of the module, and the wand is placed after it because
`lseg` is what makes anyone want a wand.

Units: 32 `listrep`, 33 `lseg` (LAB), 34 `wand`.

---

### Module 9 · Control and termination — units 35–37

**Purpose.** Close the language. `ite` and `loop` have sat in `Cmd` since Unit 18 unused; now the
partial/total distinction becomes real (35), the invariant rule is proved by induction over a
derivation whose index must be kept general (36), and a variant buys termination back (37) —
ending on a loop that reads a bound, rewrites a heap cell every iteration, and terminates.

**Why the boundary is here.** It is the only module where the existential in `Hoare` cannot be
discharged by construction, which is strictly harder than everything before it.

Units: 35 `partial`, 36 `invariant`, 37 `variant` (LAB/capstone).

---

### Module 10 · Beyond — unit 38

**Purpose.** Not a survey. Three concrete things: exhibit the allocator that **breaks** locality
and the two honest repairs; **prove** the generalisation to arbitrary PCMs rather than assert it;
and state the address-expression limitation with the exact change that removes it.

Unit: 38 `beyond`, then §`tactics` and §`ref`.

---

### The support pages

| id | file | placed | job |
|---|---|---|---|
| `goalstate` | `01-goalstate.js` | after Unit 00 | How to read a Lean goal display. Permanent reference, linked from every `trace` block. |
| `errors` | `06-errors.js` | after Unit 04 | **When Lean says no.** Twelve real error messages, indexed by their first three words. |
| `compare` | `20-compare.js` | after Unit 17 | **The same proof, several ways.** Four worked comparisons with an explicit verdict. |
| `tactics` | `42-tactics.js` | end | Tactic index: every tactic, one line, the unit that introduced it. Generated from §E. |
| `ref` | `43-ref.js` | end | Notation table, proof discipline, the ideas worth keeping, what comes next. |

Their specifications are in §D.10.

---

# D. PER-UNIT SPECIFICATION

Reading key for every entry:

- **file** — the exact path the unit must be written to, and the `id` used for the `#hash` deep
  link. Both are load-bearing and must not be changed.
- **inherits** — the exact unfinished business handed over by the previous unit. The unit's first
  paragraph answers it. If this field were empty the unit would be in the wrong place.
- **corpus** — theorems already in `lean/corpus.lean` that live here, by name. Quoted verbatim,
  tagged `verified`.
- **new Lean needed** — Lean that is not in the corpus. Everything marked ✔ is already written and
  compiled; the file it lives in is named. Anything marked ⧗ must be written and compiled *before*
  the unit is authored.
- **hook** — the one question the unit deliberately leaves open. It is contractual: the next
  unit's opening paragraph answers it, and the author of unit *n* must end on it.
- **size** — screens of prose (≈600 words each) and total block count excluding `ex` blocks, as a
  budget.

Difficulty is graded 1–5 by **Lean** difficulty, not separation-logic difficulty. 4 and 5 carry
the `hard: true` badge. Exercise kinds: **D** drill (mechanical, builds fluency) · **C**
construction (the reader chooses the shape) · **G** design (the reader writes the statement).

---

## D.0 Module 0 · Getting a proof past Lean

---

### Unit 00 · `aliasing` · The rule that is false
**file** `site/content/00-aliasing.js` · **phase** `Phase 0 · Getting started`

**One job.** Exhibit a Hoare rule that is false, show the classical repair does not scale, name
the move that does — and, in doing so, get the reader's first proof past Lean.

**Inherits.** Nothing. This is the front door. It inherits the reader's belief, from any prior
exposure, that Hoare logic is settled.

**Objectives.** You will be able to:
1. read a `theorem` header and name its four parts (keyword, name, binders, statement);
2. say what `⊢` means and read a context of hypotheses above it;
3. state the aliasing problem precisely, as a claim about a function that cannot take two values
   at one point;
4. say why adding disequality hypotheses repairs the rule and why the repair destroys modularity
   — specifically, that a routine's specification then mentions memory it does not use;
5. type `∀ ∃ → ≠ ↦ ∗` using Lean's abbreviations and the symbol palette, press *Check*, and
   interpret both a success and a failure.

**New Lean.** `theorem`, `def`, `example`, `abbrev`; explicit binders `(x : T)`; `:=` versus
`:= by`; `Prop`; `Nat`; `Option`, `some`, `none`; `if _ then _ else _`; `¬ P` as notation for
`P → False`; `≠`; the goal display `⊢` and the hypothesis context; `intro`, including the pattern
form `intro ⟨h, _⟩`; `simp [f]`; `simp [f] at h`; the fact that a hypothesis reduced to `False`
closes any goal; `#check`; `#eval`; `trace_state`; `sorry` — named once as the placeholder and
banned thereafter; Lean's Unicode abbreviations (`\to \star \mapsto \vdash \wand \forall \1`).

Deliberately **not** here: implicit binders, `funext`, `congrFun`, tactic mode beyond `intro` and
`simp`.

**New mathematics / SL.** Aliasing. Memory as a function from addresses to values. Partial
function and the `Option` encoding — *named*, defined properly in Unit 05. Footprint — named,
defined in Unit 07. Ownership versus truth as two readings of an assertion — named, decided in
Unit 13. The distinction between *unproved* and *false*.

**Corpus.** `Loc`, `Val`, `Heap`, `Var`, `Store` (the five `abbrev`s). No theorems.

**New Lean needed** — ✔ `new-overview.lean`:
```
def aliasedAfter : Heap := fun x => if x = 4 then some 5 else none
example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5)
```

**The promissory note — the most important structural device in the course.** The refutation just
proved is a fact about `Option`, not about Hoare logic, because there is no Hoare logic here yet
to be false. The statement the reader actually wants to refute is a statement about a *triple*,
and it cannot be written until there is a language, a semantics and a definition of a triple. The
unit therefore writes it on the page as a named theorem with no proof, tagged `sketch`, in a
`note kind:key`:

```
theorem classical_conjunction_rule_is_false :
    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),
        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))
              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b)))
```

and says plainly: *you cannot read this yet. Unit 28 proves it, and proves its repair in four
lines beside it. Everything between here and there exists to make those two theorems sayable.*

**Exercises (2).**

| id | what | kind | diff | what it buys |
|---|---|---|---|---|
| `x01` | write a heap in which cells 4 and 9 are allocated and nothing else is; prove `h 7 = none` | D | 1 | a heap is a function you can write down; first `if`/`Option` |
| `x02` | `aliasedAfter`: prove the aliased postcondition unsatisfiable | D | 1 | the counterexample is theirs, not the author's; *unproved* versus *false* |

`x02` is scaffolded: the reader is given `intro ⟨h3, _⟩` and must supply the `simp`. A reader who
has never seen Lean should finish their first exercise; the *reading* is the lesson.

**Hook.** "That refutation is a fact about `Option`, not about Hoare logic — there is no Hoare
logic here yet. Before we can even write the statement we want to refute, we need to be able to
write mathematics down at all, and Lean's answer to what a proof is turns out to be unusually
simple."

**Size.** ~4 screens, ~26 blocks: 1 `anat` on the five-line model, 1 `anat` on the `theorem`
header, 1 `svg` (memory as a partial function, from Edition 1's overview), 1 `cmp`
(classical repair versus separation repair), 1 `note kind:key` (the promissory note), 1 `dod`.

---

### §`goalstate` · Reading what Lean tells you
**file** `site/content/01-goalstate.js` · **badge** `§` · **support page**

**Job.** One page the reader returns to forty times. Not a lecture; a reference, and it says so in
its first sentence.

Contents: an annotated goal display (hypothesis block, turnstile, goal); where `case pos` and
`case neg` labels come from; `✝` daggers and inaccessible names, and the fact that `✝` is not an
input character; what `?m.1` is; why `Heap.write h l v` sometimes prints as `h.write l v`; why
`{store := σ, heap := h}.store` is not simplified in the display but *is* accepted by `exact`;
how to make Lean print any goal (`trace_state`); how the workbook's *Check* button reports
failure. Every example produced by `site/tools/goalstate.sh`, never invented.

**Size.** ~14 blocks, mostly `state` and `dl`. No exercises.

---

### Unit 01 · `terms` · Propositions are types, proofs are terms
**file** `site/content/02-terms.js`

**One job.** Establish that in Lean a proof *is* a term, implication *is* a function type and
modus ponens *is* application — and give the reader the four connectives in both directions,
because every separation-logic goal for the next thirty units is a nest of exactly these.

**Inherits.** Unit 00 wrote a proof but did not say what a proof *is*, and issued a promissory
note that cannot be written until we can state things about relations and existentials.

**Objectives.**
1. Write `fun h => …` proofs of implications and compositions, and read `P → Q → R` correctly.
2. Prove a `∀` by producing a function and use one by applying it; prove an `∃` with
   `⟨witness, proof⟩` and use one with `obtain`.
3. Use `⟨…⟩` and explain its **flattening** — that `∃ a b, P ∧ Q ∧ R` is built and destructured
   with five components. *This is the single most important piece of syntax in the course.*
4. Split an `∧` goal with `constructor`, an `∨` goal with `left`/`right`, and an `∨` hypothesis
   with `rcases h with h | h`.
5. Distinguish `(x : T)` from `{x : T}` and predict which arguments you must supply; use `@f`.
6. Resolve dot notation: `(hd l).symm` finds `Or.symm` because the head of the *type* is `Or`.

**New Lean.** `fun x => e`; `→` right-associativity; application as modus ponens; `∀` as a
dependent function type; `∃`; `∧`; `∨`; `↔`; `⟨…⟩` anonymous constructor and its flattening;
`.1`, `.2`; `Or.inl`, `Or.inr`; `exact`; `obtain ⟨…⟩ :=`; `rcases … with … | …`; `constructor`;
`left`; `right`; `·` focus dot; implicit binders `{x : T}` and `@f`; `Iff`, `.mp`, `.mpr`; `rfl`
as a term; `Eq.symm`, `Eq.trans`, dot notation `h.symm`; `#check @funext`.

**New mathematics / SL.** Propositions-as-types; the constructive reading of the connectives.
Nothing separation-logic-specific — and the unit says so, which is why it is short. It does say
one thing forward: `Entails P Q` will turn out to be `∀ σ h, P σ h → Q σ h`, so **every entailment
proof in this course is a lambda**, and about a fifth of the corpus's 127 theorems have no `by` in
them at all.

**Corpus.** `implication_example`, `exists_example`.

**New Lean needed** — ✔ `new-overview.lean`: `mp`, `comp`, `and_comm'`, `or_comm'`,
`exists_three`, `exists_mono`, `two_add_two`. Plus ⧗ two one-liners over `Prop`:
`nested_pack : ∃ x y, x = a ∧ y = b ∧ P x ∧ Q y` and
`nested_unpack : (∃ x y, P x ∧ Q y ∧ x = y) → ∃ z, P z ∧ Q z`.

**Exercises (4).**

| id | what | kind | diff | what it buys |
|---|---|---|---|---|
| `x03` | `comp : (P → Q) → (Q → R) → P → R`, term mode | D | 1 | composition is `fun` and application |
| `x04` | `and_comm'` with `⟨h.2, h.1⟩`, then `or_comm'` via `rcases` | D | 2 | first `⟨…⟩`, first projection; `∨` is eliminated, not projected |
| `x05` | `exists_mono : (∀ n, P n → Q n) → (∃ n, P n) → ∃ n, Q n` | C | 2 | witness in, witness out — the pattern every `star_mono` proof repeats |
| `x06` | `nested_pack` / `nested_unpack` | C | 3 | **the six-slot shape of `star`**, met on a statement with no heaps in it, thirteen units before it matters |

Each carries a `cmp` block showing the same statement's tactic proof greyed out, captioned "you
will write this in Unit 02; you cannot yet, and that is deliberate".

**Pitfall to record.** Naming `x04`'s helper `not_not_intro` fails with
`` `not_not_intro` has already been declared `` — a real collision with Lean's core, and a good
first lesson in reading an error.

**Hook.** "Nothing you have written can compute. `2 + 2 = 4` closed by `rfl` — but why did that
work, and when will it stop working? Memory is going to be a function, and the first thing we ask
of two heaps is whether they are equal."

**Size.** ~4 screens, ~30 blocks: 2 `anat` (a lambda proof; an `⟨…⟩` tower), 1 `cmp` per exercise,
1 `dl` of term-level vocabulary, 1 `trace` on a nested `obtain`.

---

### Unit 02 · `compute` · Equality, computation, and the limits of `rfl`
**file** `site/content/03-compute.js`

**One job.** Separate definitional from propositional equality, because "why does `rfl` work here
and not there?" is the single most common complaint about Edition 1 and it is this distinction,
never stated — and introduce `Option` and `if` as the two pieces of data the whole model is made
of.

**Inherits.** Unit 01 closed `2 + 2 = 4` with `rfl` and asked why.

**Objectives.**
1. Read an `inductive` declaration and name its constructors; write a `def` by pattern matching.
2. State the rule: `rfl` succeeds when both sides reduce to the same normal form, and a *variable*
   blocks reduction. Predict which of a given list of goals `rfl` closes.
3. Explain why `if c then a else b` needs a `Decidable c` instance, and why `Loc := Nat` is
   therefore not an arbitrary choice.
4. Use the two facts about `Option`: constructors are distinct, `some` is injective.
5. Rewrite with `rw [h]`, `rw [← h]`, `rw … at h`, and know that `rw` tries `rfl` afterwards;
   restate a goal with `show`; introduce a fact with `have`.
6. Split on a *value* with `cases hl : e with | none => … | some v => …`, and say what the saved
   equation `hl` buys.

**New Lean.** `inductive` (met as `Option`, `Bool`, `Nat`); constructors; leading-dot name
resolution; pattern-matching `def`; definitional versus propositional equality; `rfl` as a tactic
and its limits; `Decidable` and a typeclass instance, introduced concretely as "a value Lean finds
for you"; `Nat.decEq`, `Nat.beq`; `Option.some.inj`; `absurd`; `False`; `rw [h]`, `rw [← h]`,
`rw … at h`; `unfold`; `simp`, `simp [f]`, `simp only [f]`; `show`; `have h : T := e`; anonymous
`have` and `this`; `congrArg`; `cases h : e with | c => …`; `#print`.

**New mathematics / SL.** Partial functions, and the decision to encode them as total functions
into `Option` — with the rejected alternative named and costed: a dependent pair of a domain
predicate and a function on it makes every later rewrite carry a transport. `Heap`, `Loc`, `Val`,
`Var`, `Store` are given their meanings here so Unit 04's `update` is visibly the store.

**Corpus.** The `abbrev` block (already shown in Unit 00; here it is *used*).

**New Lean needed** — ✔ `new-overview.lean` (`double_unfold`-flavoured drills) plus ⧗
`def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v` with its
`cases hl : h l` proof. (Edition 1 has this at the end of M0 as an `illustration`; it is real, and
it moves here where `Option` is being built.)

**Exercises (3).**

| id | what | kind | diff | what it buys |
|---|---|---|---|---|
| `x07` | `def double n := n + n`; close `double n = n + n` and `double 3 = 6` by `rfl`; then meet a sibling `rfl` cannot close and close it with `simp [double]` | D | 1 | when `rfl` works and when it does not — stated as a rule, then tested |
| `x08` | `some v = some w → v = w` by `Option.some.inj`, and `some v ≠ none` two ways (`by simp`; `intro h; cases h`) | D | 2 | injectivity as a lemma, not a reflex; constructors are distinct |
| `x09` | `defined h l` from `h l ≠ none`, using `cases hl : h l with` | C | 3 | **the `hl :` that records the equation** — the single most-forgotten piece of syntax in the course |

**Pitfall planted here, cashed in Unit 09 and Unit 21.** `cases h l` *without* the `hl :` gives
you a value out of nowhere, unconnected to `h`. A `cmp` block shows both contexts side by side.

**Hook.** "`Heap` is a type now, and it has no operations. The smallest useful one changes what is
stored at one address — and writing it will show you that `rfl` was never going to be enough,
because two heaps are two *functions*."

**Size.** ~4 screens, ~28 blocks: 1 `anat` on `Option`, 1 `cmp` (with/without `hl :`), 2 `state`
blocks of real `#print` output, 1 `detail` on what `Decidable` costs and what `open Classical`
would buy, 1 `detail` on the dependent-pair alternative to `Option`.

---

### Unit 03 · `funext` · Functions as values
**file** `site/content/04-funext.js`

**One job.** Install the three-move pattern — `funext`, split on the point, close both branches —
that opens every heap proof for the next twenty units, and present function extensionality as what
it is: an extra principle, not a triviality.

**Inherits.** Unit 02 ended on the observation that heaps are functions and `rfl` cannot prove two
functions equal.

**Objectives.**
1. Reduce a function equality to a pointwise one with `funext`, and go the other way with
   `congrFun`; say why each is the exact converse of the other.
2. Split on a decidable proposition with `by_cases h : p` and read `case pos` / `case neg`.
3. Collapse an `if` with `if_pos` / `if_neg` by hand, and know when `simp [h]` does it for you.
4. Run one tactic on all remaining goals with `<;>`, focus one with `·`, and say which of the two
   is a tactic and which is not.
5. Read `¬ p` as `p → False` and `a ≠ b` as `¬ (a = b)`, and know that `x ≠ l` and `l ≠ x` are
   *different terms* — `Ne.symm` is the fix.
6. Run `#print axioms` on a `funext` proof and see `Quot.sound` and `propext` appear.

**New Lean.** `funext` (tactic and term); `congrFun`; `by_cases h : p`; `case pos` / `case neg`;
`if_pos`, `if_neg`; `<;>`; `;` on one line; `·` in a nested split; `Ne`, `Ne.symm`; inaccessible
names and the `✝` marker (first sighting; named properly in Unit 19); `#print axioms`.

**New mathematics / SL.** Function extensionality. Characterising an operation by its behaviour at
every point rather than by its definition.

**Corpus.** `function_extensionality`.

**New Lean needed** — ⧗ three one-line drills over `Nat → Nat`: `funext_drill`
(`(fun n => n + 0) = (fun n => n)`, whose point is that this is *not* `rfl`), `if_drill`
(collapse an `if` in both directions with explicit `if_pos`/`if_neg`), `by_cases_drill`
(`∀ f x y, (if y = x then f x else f y) = f y`, whose surprise is that the `pos` branch needs the
hypothesis to rewrite the *goal*).

**Exercises (3).** `x10` `funext_drill` [D,2] · `x11` `if_drill` [D,2] · `x12` `by_cases_drill`
[C,2].

**Hook.** "You now have every tactic the next page needs. The theorems there are about updating a
function at one point — which is, with one type changed, exactly what writing to memory will be."

**Size.** ~4 screens, ~24 blocks: 2 `anat`, 2 `trace`, 1 `cmp` (`by_cases` + `simp` versus
explicit `if_pos`/`if_neg`), 1 `note` on `<;>` and when its branches diverge, 1 `state` of a real
`rfl` failure on a function equality.

---

### Unit 04 · `update` · LAB — the update family
**file** `site/content/05-update.js` · **LAB**

**One job.** Guided doing. Five exercises with no new exposition, on `update`, which is the heap
with `Option` removed — so that when `Heap.write` arrives in Unit 05 the reader recognises every
proof.

**Inherits.** All of Units 00–03. This lab introduces nothing.

**Worked example (part 2 of the lab format).** `update_same`, with every goal state printed, the
tactic named, and the alternative spellings compared: `simp [update]`, `unfold update; rw [if_pos
rfl]`, and `rfl` (which fails, and the failure is shown).

**Objectives.**
1. Prove `update_same` and `update_other` and say which three rewrites `simp` fired in each.
2. Recognise the residue `⊢ y = x → value = f y` as "you owe me a disequality", and know that the
   hypothesis must be passed to `simp` explicitly.
3. Prove a function equality by `funext` + `by_cases` + `<;> simp` without being told to.
4. Drive a three-region case analysis by hand with `if_pos`/`if_neg`, and point at the single line
   where the disequality is consumed.
5. Say which of `simp` and hand-driven `rw` to use, by the stated rule: `simp` when both branches
   want the same text and you do not care which conditional collapsed; `rw` when the location of
   the hypothesis's use is the content.

**New Lean.** None. The lab says so: a page whose job is fluency introduces no new syntax, so the
reader can measure their own speed.

**New mathematics / SL.** Shadowing (unconditional) versus commuting (conditional), and the
observation that the asymmetry is the whole subject in miniature: separation buys its frame rule
from *disjointness*, not from agreement. Locality of an update: changing one key disturbs no
other.

**Corpus.** `update` (def); `update_same` (`m0-1`), `update_other` (`m0-2`), `update_shadow`
(`m0-3`), `update_comm` (`m0-4`).

**New Lean needed** — ✔ `new-m1.lean`: `update_idem`.

**Exercises (5).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m0-1` | `update_same` | D | 1 | first `simp [def]`; also the worked example, so it is read before it is done |
| `m0-2` | `update_other` | D | 1 | first hypothesis in the simp set; the orientation of `y ≠ x` against `if y = x` |
| `m0-3` | `update_shadow` | C | 2 | the permanent three-step shape; first `<;>` |
| `m0-4` | `update_comm` | C | 3 | three regions, not two; explicit `if_pos`/`if_neg`; **the first proof where non-aliasing is used, exactly once** |
| `x13` | `update_idem` | **G** | 2 | *design*: "state and prove that updating a point with the value already there does nothing." The reader writes the statement. |

**Retrospective.** (i) Which of the four laws needs a hypothesis, and why only that one? (ii) In
`update_comm`, which line consumes `hne`? (iii) What did `<;> simp` hide in `m0-3` that
`if_pos`/`if_neg` shows in `m0-4`?

**Hook.** "`update_comm` used `hne` exactly once, to derive `z ≠ y` from `z = x`. Remember that
line: in twenty-three units it is the reason the frame rule is true. But nobody hands you `hne` in
a real program, and `update` cannot give a cell up — 'not mine' is what `emp` will be made of."

**Size.** ~2 screens of prose, ~16 blocks (the worked example is most of it), plus 5 `ex`.

---

### §`errors` · When Lean says no
**file** `site/content/06-errors.js` · **badge** `§` · **support page**

**Job.** The 2am page. Twelve real error messages, each with what Lean printed, what it means, the
commonest cause, and the fix. Every message is produced by deliberately breaking a real proof from
this course and copying what Lean said. Linked from every exercise's hint panel.

The twelve, in the order a reader meets them:

1. `unknown identifier` — not defined yet, or wrong namespace.
2. `Type mismatch … has type X but is expected to have type Y` where X and Y look identical — read
   the whole term; the difference is usually argument order.
3. The same, where they genuinely differ by a reduction — `exact` would have worked, you used `rw`.
4. `Invalid field 'symm'` — you projected before applying: `(hd l).symm`, not `hd.symm l`.
5. `unsolved goals` after `by_cases` — one branch left; focus dots and `<;>`.
6. `motive is not type correct` — you tried `rw` where you needed `subst` or `cases`.
7. `` `simp` made no progress `` — the definition is not in the simp set, or the goal is stuck on a
   `match`.
8. `The rewrite tactic failed: did not find an instance of the pattern` — orientation: `x ≠ l`
   versus `l ≠ x`.
9. `function expected` — a missing pair of parentheses before a dot.
10. `failed to infer … metavariable` — an implicit argument nothing determines; supply it with
    `(l := 0)`.
11. `application type mismatch` on an induction hypothesis — you needed `generalizing`.
12. `declaration has already been declared` — you pasted the solution above your own attempt.

**Also on this page, and load-bearing:** the standing rule that a tactic not in the `tactics` index
does not exist here, demonstrated with `set x := …` failing as `unknown tactic` because `set` is
Mathlib's; and the honest limits of search — `exact?` on `(h : a = b) ⊢ b = a` answers
`exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm h))) a)`, a correct and
absurd term.

**New Lean introduced here (diagnostic only, never in a solution).** `simp?`, `exact?`,
`#print axioms`, `set_option pp.explicit true`, `set_option pp.numericTypes true`, reading
`Try this:` output.

**Format.** Each entry: a `state` block with the verbatim error, a `p` with the diagnosis, a `cmp`
with broken and fixed code. A `dl` at the top indexes the twelve **by the first three words of the
message**, so a reader can find their error by matching text. Also on the page: *what a stuck
reader does, in order* (see §H.3).

**Size.** ~40 blocks. The largest support page, and worth it. No exercises.

---

## D.1 Module 1 · Memory

---

### Unit 05 · `heap` · Memory as a partial function
**file** `site/content/07-heap.js` · **phase** `Phase 1 · The resource algebra`

**One job.** Define memory and its four operations, and replace the definitions immediately by six
lookup equations that are the only interface from here on.

**Inherits.** Unit 04 proved four laws about `update : (Nat → Nat) → Nat → Nat → (Nat → Nat)`, a
*total* update. Memory is not total: a location can be unallocated, and the difference is exactly
what ownership is about.

**Objectives.**
1. Read `Heap := Loc → Option Val` and say what `h l = none` means — two things, *unallocated* and
   *not mine*, and the ambiguity is deliberate.
2. Read the 2×2 table (then-branch × else-branch) that generates the four operations, and predict
   from it which lemmas come in pairs.
3. Work inside a `namespace`, name things `Heap.write` in a `simp` set, and read `h.write l v` in
   a goal as `Heap.write h l v`.
4. Prove all six lookup laws, each in one `simp`, and distinguish the two residues `simp` leaves —
   `⊢ x = l → some v = h x` versus `⊢ ¬x = l` — saying why the second gets one step further.
5. State what each operation does to the *domain*, and note that no operation requires ownership:
   `Heap.write` allocates when the location was absent. The intended meaning is restored later by
   a precondition, not by the definition. **This is the first appearance of "ownership is imposed
   by preconditions".**
6. State the interface discipline: after this unit, `Heap.write` never appears in a `simp` bracket
   again except while the *algebra of the operation itself* is being established (Unit 06), and
   never after that.

**New Lean.** `namespace … end`; dot-notation display and the rule that governs it. Nothing else —
this unit deliberately introduces no new tactic, which is the point of putting it directly after
the `funext` lab.

**New mathematics / SL.** Partial function, properly. Domain of definition. Deallocation. The
*interface* idea: once an operation is characterised by equations, its definition is not unfolded
again. Immutability of values versus mutation of state — "the heap after the write" denotes a new
function.

**Corpus.** `Heap.empty`, `Heap.singleton`, `Heap.write`, `Heap.erase`; `singleton_same` (`m1-1`),
`singleton_other` (`m1-2`), `write_same`/`write_other` (`m1-3`), `erase_same`/`erase_other`
(`m1-4`).

**New Lean needed.** None. Edition 1's `PHeap` dependent-pair `illustration` and its
`def`-instead-of-`abbrev` `sketch` (with the real
`failed to synthesize instance … Decidable (x = l)` error) move here from `00-overview.js`, where
they belong.

**Exercises (4, all corpus).** `m1-1` [D,1] · `m1-2` [D,1] · `m1-3` [D,1] · `m1-4` [D,1].

All four are single `simp` calls. **This is deliberate and is stated to the reader**: the purpose
of the unit is the interface, not the difficulty, and four one-line proofs in a row is what
building an interface looks like.

**Hook.** "Six equations, and none of them mentions more than one lookup. What happens when you
write twice to the same cell, or to two different cells? Those two facts are what the assignment
rule and the frame rule are made of."

**Size.** ~4 screens, ~28 blocks: 1 `tbl` (the 2×2 that generates the four operations), 1 `svg`,
1 `defn` card per operation, 1 `dl` of domains, 2 `detail` (why not one `upd` with an `Option`
argument; why heaps are not finite).

---

### Unit 06 · `heap-laws` · LAB — equations between heaps
**file** `site/content/08-heap-laws.js` · **LAB**

**One job.** Close the heap interface — the equations between whole heaps — and leave the reader
never needing to unfold a heap operation again.

**Inherits.** Unit 05's six lookup equations, with the promise that the definitions need never be
unfolded again. This lab tests that promise, and is honest about the one wrinkle: the corpus proof
of `write_shadow` *does* use `simp [Heap.write, hx]`. The lab addresses that head-on in a
`detail`: unfolding is permitted while the algebra of the operation is being established, and
forbidden from Unit 07 on. Saying this is better than letting the reader notice the inconsistency.

**Worked example.** `write_singleton` three ways — pointwise with `simp`, pointwise with explicit
`rw [if_pos]`/`rw [if_neg]`, and via `write_of_eq`. The verdict is that the third *reuses a lemma*,
and reuse is the habit. (This worked example is repeated in the `compare` page.)

**Objectives.**
1. Instantiate one schema — *an operation at `l` does not care what an earlier write to `l` put
   there* — at four positions and get four theorems.
2. Prove `write_comm` by hand and name the single line where non-aliasing enters.
3. Produce the counterexample showing `write_comm` fails without its hypothesis, and note that it
   needs *different values*, not merely one location.
4. Prove `write_singleton` and `erase_singleton`, and say which program rule each one is the whole
   content of. **The unit says explicitly: prove these now, in the heap layer, so that Unit 23 is
   three lines and does no pointwise reasoning inside a Hoare proof.** That layering discipline is
   stated here and enforced for the rest of the course.
5. Extend the interface yourself, choosing between `simp` and hand-driven `rw` by the Unit 04
   rule — and meet the case where `unfold` is wrong: `unfold Heap.write Heap.erase` leaves a
   beta-redex that blocks `rw [if_pos]`, and the working incantation is
   `simp only [Heap.write, Heap.erase]`.

**New Lean.** No new tactic. The unit flags this: the tactic vocabulary is now sufficient for real
work. (`simp only` was introduced in Unit 02; this is its first load-bearing use.)

**New mathematics / SL.** Disjoint operations commute — the germ of the frame rule, and the lab
names the later theorem it becomes (`heapLocal_write`, Unit 25).

**Corpus.** `write_shadow` (`m1-5`), `erase_write_same` (`m1-6`), `write_comm` (`m1-7`),
`write_singleton`/`erase_singleton` (`m1-8`).

**New Lean needed** — ✔ `new-m1.lean`: `heap_ext`, `erase_erase`, `write_erase_same`,
`erase_write_comm`, `erase_comm`, `write_empty`, `write_of_eq`.

`erase_write_comm` matters. Edition 1 *asserts* it in the `variants` field of `m1-6` — "the true
statement there is a commutation law … which is proved the same way" — and never proves it. It is
now an exercise, and "the same way" turns out to need the `simp only` fix above. That failure is
real and the reader must be shown it rather than protected from it.

**Exercises (6).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m1-5` | `write_shadow` | C | 2 | the schema, first instance; last write wins — the assignment axiom's content |
| `m1-6` | `erase_write_same` | C | 2 | why `write; free` = `free`; why `Heap.write` must be in the brackets even though its value is discarded |
| `m1-7` | `write_comm` | C | 3 | the hand-driven three-region proof; **the germ of the frame rule**; the counterexample |
| `m1-8` | `write_singleton` / `erase_singleton` | C | 2 | the write rule and the free rule of Unit 23, computed in advance |
| `x14` | `erase_erase`, `write_of_eq` | C | 3 | idempotence (a free win after `write_comm`), then a proof where a *hypothesis about the heap* drives the `pos` branch — the shape of every locality proof in Unit 25 |
| `x15` | `erase_write_comm`, and then: state and refute the claim that erase and write always commute | **G** | 3 | the mixed law; `unfold` versus `simp only` met head-on; and the reader finds the failing case `l = l'` themselves and refutes it by `congrFun` at a point |

**Retrospective.** (i) Why is `Heap` a function into `Option` and not a partial-map primitive?
(ii) Which of the eleven lemmas needs a disequality, and why only those? (iii) What does "the
interface is closed" forbid you from doing?

**Hook.** "Every law so far is about one heap, and `write_comm` had its disequality handed to it.
In a real program nobody hands it to you. To *derive* such a fact rather than assume it, memory has
to be splittable — and before we can split a heap we had better decide what it means to hold one."

**Size.** ~2 screens of prose, ~22 blocks: the worked example, 1 `txt` schema diagram, 1 `tbl` of
the eleven-lemma interface, 1 `cmp` (`simp` route versus `rw [if_pos]` route), 1 `detail` (the
unfolding-discipline wrinkle), plus 6 `ex`.

---

### Unit 07 · `footprint` · How much do you own?
**file** `site/content/09-footprint.js`

**One job.** Pose, sharply and with a counterexample, the question the whole course turns on —
which heaps satisfy "`l` holds `v`"? — and show the two answers disagree about whether
deallocation can be specified at all.

**Inherits.** Unit 06's `erase_singleton : Heap.erase (Heap.singleton l v) l = Heap.empty`, which
is true of the *one-cell* heap and says nothing about erasing a cell from a bigger one.

**Objectives.**
1. State the two candidate readings of "`l` holds `v`" as two Lean definitions — a predicate
   satisfied by many heaps versus one satisfied by exactly one.
2. Exhibit a heap satisfying one and not the other, and prove both facts.
3. Explain, with a concrete heap, why `{l ↦ v} free l {emp}` is **false** under the loose reading,
   and why the failure is not vacuous.
4. Say what a *footprint* is, and why a specification that does not pin one down cannot promise
   anything about what survives.
5. Use the refutation idiom as a **named pattern**: pick the location where the two functions must
   disagree, apply both sides to it with `congrFun`, land on an equation between distinct
   constructors. Every refutation about heaps in this course is that shape.

**New Lean.** No new tactic. The refutation idiom is *named*: `intro h; have := congrFun h n;
rw [...] at this; exact absurd this (by simp)`.

**New mathematics / SL.** **Footprint.** Exact versus inexact ownership — *posed*, not decided;
Unit 13 decides it and Unit 23 justifies it. The first explicit use of the principle that a
definition is a choice and the choice is judged by which theorems survive it.

**Corpus.** None. This unit proves no corpus theorem, and that is correct: it is the unit that
makes Unit 13's definitions inevitable. (Edition 1 has this argument, well made, in
`00-overview.js` — before the reader has `Heap.erase`, before `Assertion` means anything, and
before there is any free rule to be false. It moves here, where it is a question rather than an
announcement.)

**Note for the author.** `Assertion` is *not* defined at this point in Edition 2's ordering. Write
the two readings with the bare type `Store → Heap → Prop` spelled out; Unit 12 gives it its name.
That inversion is deliberate: the reader meets the thing before the abbreviation.

**New Lean needed** — ✔ `new-m1.lean`:
```
def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v
def ptsExactly (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h = Heap.singleton l v
def twoCells : Heap := Heap.write (Heap.singleton 4 3) 9 7
example : ptsAtLeast 4 3 (fun _ => 0) twoCells
example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells
example : Heap.erase twoCells 4 ≠ Heap.empty
```

**Exercises (3, all new).**

| id | what | kind | diff | what it buys |
|---|---|---|---|---|
| `x16` | exhibit a two-cell heap and prove it satisfies the loose reading at one of its cells | D | 1 | concreteness |
| `x17` | prove the same heap does *not* satisfy the exact reading | C | 3 | the `congrFun`-at-a-witness pattern, used again in Units 13, 14 and 31 |
| `x18` | prove the heap left after erasing cell 4 is not the empty heap | C | 3 | **the free rule is false under the loose reading, and the reader proved it.** Every later appeal to exactness points back to this exercise by name |

**Hook.** "The exact reading survives the test and the loose one does not, so `l ↦ v` is going to
mean *the heap is this one cell*. But then an assertion talks about all of the memory it holds, so
combining two of them means cutting memory in two — and nothing you have can cut a heap."

**Size.** ~4 screens, ~24 blocks: 1 `cmp` (at-least versus exactly), 2 `code`, 1 `state` with the
real intermediate goal, 1 `note kind:key`, 1 `dod`.

---

## D.2 Module 2 · The resource algebra

---

### Unit 08 · `disjoint` · Disjointness
**file** `site/content/10-disjoint.js`

**One job.** Define what it means for two heaps not to overlap, and prove the first theorem in the
course in which a disequality is *derived* rather than assumed.

**Inherits.** Unit 07 settled on exact ownership, which forces us to be able to divide a heap; and
Units 04 and 06 both needed a disequality hypothesis that nobody supplies in practice.

**Objectives.**
1. Read `Heap.disjoint h₁ h₂ := ∀ l, h₁ l = none ∨ h₂ l = none` and say why it is stated with
   `none` rather than with domains as sets.
2. Prove a `∀`-goal by `intro` where the `def : Prop` unfolds without being asked, and an
   `∨`-goal by `left` / `right`; destructure an `∨` hypothesis with `rcases … with h | h`.
3. Give a term proof where one is shorter than a tactic proof —
   `disjoint_empty_left := fun _ => Or.inl rfl` — and say why `rfl` suffices there.
4. Instantiate a disjointness hypothesis at a location: `hd l` is already a proof.
5. Prove the **converse**: separation implies non-aliasing. Owning two cells separately *proves*
   they are different.
6. Prove that the only self-disjoint heap is the empty one.

**New Lean.** `intro` on a `∀`-goal into a folded `def : Prop`; `rcases h l with h | h`;
`subst`; `<;> ·` (a bullet block under a combinator, as it appears in `singleton_disjoint_iff`).
`left`/`right`, `constructor` on `↔`, `absurd` and `.mp`/`.mpr` were introduced in Units 01–02 and
are first *used* here.

**New mathematics / SL.** Disjointness of resources. **Separation implies non-aliasing** — the
small lemma with the large moral, met here and cashed at Unit 17 and again at Unit 28. The reading
of `∀ l, h₁ l = none ∨ h₂ l = none` as "every cell belongs to at most one side". A foldable aside
worth keeping: the *weakest* hypothesis making union commutative is compatibility (agreement on
the overlap), not disjointness — the over-strengthening is the whole subject, because ownership is
what we want, not well-definedness.

**Corpus.** `Heap.disjoint` (def); `Heap.union` and `Heap.splits` are *stated* here because
`splits` mentions `union` — the author states them and moves on; they are proved about in Units 09
and 11. `disjoint_symm` (`m2-1`), `disjoint_empty_left`/`right` (`m2-2`), `singleton_disjoint` and
`singleton_disjoint_iff` (`m2-3`).

**New Lean needed** — ✔ `new-m2.lean`: `self_disjoint_iff_empty`.

**This closes a real defect.** Edition 1 states `self_disjoint_empty` inside the `variants` prose
of `m2-2` as untagged, unverified code, and then `05-m4.js` cites it *by name* in body prose
("M2's `self_disjoint_empty` says…") as though it were available. Grepping `corpus.lean` returns
zero matches. Edition 2 promotes it to a verified exercise, strengthened to an `↔`, because Unit
14's no-contraction proof needs it.

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m2-1` | `disjoint_symm` | D | 1 | a `def : Prop` unfolds under `intro`; two lines, one of them `.symm` |
| `m2-2` | `disjoint_empty_left` / `_right` | D | 1 | a proof with no tactics at all; `Heap.empty l` *is* `none` definitionally. **Pitfall:** picking the wrong injection — the error lands on `rfl`, not on `Or.inl` |
| `m2-3` | `singleton_disjoint` and `singleton_disjoint_iff` | C | 3 | **separation proves non-aliasing.** The `mp` direction turns disjointness into `l₁ ≠ l₂`; every disequality in every later program proof comes from here |
| `x19` | `self_disjoint_iff_empty` | C | 2 | the sharpest one-line statement of what disjointness means; the engine of Unit 14's no-contraction proof |

**Hook.** "We can say two heaps do not overlap. We still cannot *combine* them, and 'the heap
splits into these two pieces' needs both halves of that sentence."

**Size.** ~3 screens, ~26 blocks: 1 `svg` of a split, 1 `trace` on `singleton_disjoint_iff`,
1 `detail` (compatibility versus disjointness), 1 `detail` (what putting the disjointness proof in
the *type* would cost).

---

### Unit 09 · `union` · Union, and why it must be total
**file** `site/content/11-union.js`

**One job.** Define combination of heaps, confront honestly that the mathematically correct
partial operation is unusable in a total type theory, and equip the reader with the three lookup
lemmas without which every later proof drowns in unreduced `match` expressions.

**Inherits.** Unit 08 gave us "these two heaps do not overlap" and nothing that combines them.

**Objectives.**
1. Define `Heap.union` by matching on the left argument, and say precisely what left-biasedness
   means at a location where both heaps are defined.
2. Explain why a genuinely partial union — one whose *type* demands a disjointness proof — makes
   every subsequent rewrite carry that proof, and why the course pays a hypothesis at each use
   site instead.
3. Say why `simp only [Heap.union]` parks the goal, and what unsticks it: a `match` computes only
   when its scrutinee is a constructor application.
4. Split on a *value* with `cases hl : h l with | none => … | some v => …` — this is Unit 02's
   `hl :`, now doing real work — and distinguish it from `by_cases` on a decidable proposition.
5. Prove `union_of_none`, `union_of_some`, `union_eq_none`, and thereafter never write
   `Heap.union` in a `simp` bracket again.
6. Explain the asymmetry between `union_empty_left` (pointwise `rfl`) and `union_empty_right`
   (needs a case split) in terms of which argument the `match` scrutinises.

**New Lean.** `match … with` inside a `def` and why it blocks reduction; `rwa`; pattern `intro
⟨ha, hb⟩`; implicit `{}` versus explicit `()` binders and how to decide — which is what explains
the argument order of `union_of_none h₂ hl`.

**New mathematics / SL.** Combination of resources; `Heap.empty` as unit. Left-biasing as a
convenience with a discipline attached. **The register-shift paragraph, promoted to first-class
exposition**: on paper you write "the two heaps are disjoint, so define their union"; Lean will not
let you, so union is total, left-biased, and disjointness travels separately as a hypothesis — which
is why every lemma below takes an explicit `hd` that on paper would be invisible.

**Corpus.** `Heap.union` (def); `union_of_none`, `union_of_some`, `union_eq_none` — **promoted
from `code` blocks to exercises**; `union_empty_left`/`union_empty_right` (`m2-4`).

**New Lean needed** — ✔ `new-m2.lean`: `union_self`. (Currently an `illustration` inside
`05-m4.js`; promoted here because Unit 14 needs it to build the duplicating pseudo-star, and
because it is the cleanest demonstration of what left-biasing does.)

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x20` | `union_of_none` / `union_of_some` | D | 2 | the pattern: rewrite the scrutinee to a constructor, let the `match` compute. The entire rewriting vocabulary of Units 10–11 and 25–27 |
| `x21` | `union_eq_none` | C | 3 | the only one of the three with content; first `rwa`; the only way to reason about a union being undefined at a point, needed immediately by `union_assoc` |
| `m2-4` | `union_empty_left` / `union_empty_right` | C | 2 | **one is `rfl` pointwise, its mirror image is not.** The sharpest demonstration in the course of what a `match` will and will not do |
| `x22` | `union_self` | D | 1 | idempotence; left-biasing, sharply; Unit 14's counterexample |

Promoting the three lookup lemmas from `code` to `ex` is deliberate: Edition 1 hands them over
after saying "three tiny lookup lemmas … add them", and they are the exact skill (`cases hl :` plus
`rw` with a lookup lemma) that the next three units are built on.

**Hook.** "We have an operation and a unit. Whether they form anything worth a name depends on
associativity and commutativity — and those two behave *completely differently*, one needing no
hypothesis and the other false outright without one. That asymmetry has a name."

**Size.** ~4 screens, ~26 blocks: 1 `state` (the parked `match` goal, printed by Lean), 1 `anat`
on `union`, 1 `cmp` (partial versus total union), 1 `cmp` (`by_cases` versus `cases … :`),
1 `note` carrying the register-shift paragraph, 1 `detail` on why the right unit law is not `rfl`.

---

### Unit 10 · `pcm` · The partial commutative monoid
**file** `site/content/12-pcm.js`

**One job.** Prove the remaining laws, observe that associativity needs no hypothesis while
commutativity does, name the structure — and **build it in Lean**, so that the name denotes an
object the reader can inspect rather than a slogan.

**Inherits.** Unit 09 delivered `union`, `empty` and the unit laws, and left open whether the
operation is associative and commutative.

**Objectives.**
1. Prove `union_assoc` with **no disjointness hypothesis**, and explain why "the first defined
   value wins" is associative on the nose.
2. Prove `union_comm` from disjointness, and exhibit the two-heap counterexample showing it is
   *false* without — with `h₁ = singleton 0 4`, `h₂ = singleton 0 7` the two unions disagree at 0,
   and left-biasing becomes visible exactly where disjointness fails.
3. Prove `disjoint_union_left` and **derive** `disjoint_union_right` from it by conjugating with
   `disjoint_symm` rather than reproving it — and say why: a development that reproves its mirror
   images triples in size.
4. Discharge several obligations at once with `refine ⟨fun l => ?_, fun l => ?_⟩` and read
   `case refine_1`.
5. State what a monoid is, what a commutative monoid is, and what a **partial** commutative monoid
   is; check `(Heap, union, empty, disjoint)` against the definition field by field.
6. Write a Lean `structure` bundling an operation with its laws, and instantiate it — turning
   "heaps form a PCM" into a term you can `#check`.

**New Lean.** `refine … ?_` and metavariable goals; `fun l => ?_` inside a `refine`;
`structure … where` with `Prop`-valued fields; the `where` instance syntax; field projection
`K.op`, `K.op_comm`; `obtain` applied to the result of `.mp` on an `↔`.

**New mathematics / SL.** **Monoid**, **commutative monoid**, **partial commutative monoid** —
defined here, properly, for a reader who has never seen one, motivated by the fact that we have
just finished proving exactly those axioms, with `(Nat, +, 0)` and `(List, ++, [])` as the two
examples the reader already knows. The distinction between a law that holds unconditionally and a
law that holds where the operation is defined — that is the mathematical content of the word
*partial*. Bundling laws with data as the way a structure is written in type theory.
**Cancellativity** — the one property heaps have that a general PCM need not — named here so that
Unit 38 can be honest about what does *not* generalise.

**Corpus.** `union_assoc` (`m2-5`), `union_comm` (`m2-6`), `disjoint_union_left`/`right` (`m2-7`).

**New Lean needed** — ✔ `new-m4.lean` (it type-checks against `prelude/m2.lean` too; the file is
filed under m4 because `pcmStar` needs `Assertion`): `PCM`, `heapPCM`, `union_cancel_left`.

`heapPCM` is the load-bearing addition of this module. Every field is a theorem the reader has just
proved, so instantiating it is a five-minute exercise that retroactively explains why each law
needed the hypotheses it needed — and it is the object Unit 38 generalises over.

**Exercises (5).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m2-5` | `union_assoc` | C | 3 | three leaves and **no hypothesis**; the middle one needs `union_eq_none.mpr`. This is why `star_assoc` will be pure bookkeeping |
| `m2-6` | `union_comm` | C | 3 | the one law that *needs* the hypothesis; a nested `cases hl :` inside an `rcases` branch |
| `m2-7` | `disjoint_union_left` / `_right` | C | 4 | **the workhorses.** Every re-bracketing of a `∗` for the rest of the course is one of these; `_right` is derived, not reproved |
| `x23` | `heapPCM` | D | 1 | fill five fields with five theorems you have proved. **"Heaps form a PCM" becomes a term.** Difficulty deliberately low; the value is conceptual |
| `x24` | `union_cancel_left` | C | 4 | a heap determines its complement; the honest boundary of the generalisation; a genuine test of the lookup lemmas |

**Author's note on over-promising.** State the plan explicitly: *we build this now because you have
just proved all six fields; we then put it away and work concretely with heaps until Unit 38, where
we take it out and prove that the concrete work was generic all along.* A reader who has just met
the word "monoid" must not conclude the course is about abstract algebra.

**Hook.** "You have an algebra of resources. What you do not have is a way to say *this heap splits
into these two* — and its associativity is none of the four laws above. It is the first statement
whose proof has to manufacture hypotheses nobody handed you."

**Size.** ~5 screens, ~30 blocks: 1 `defn` card for PCM, 1 `tbl` mapping PCM data to heap data
with a "needs `disjoint`?" column, 2 `trace`, 1 `detail` on why `structure` and not `class`,
1 `note kind:key` (`∗` is not a connective about heaps; it is the connective induced by any PCM —
stated here as a claim, *proved* in Unit 38).

---

### Unit 11 · `splits` · LAB — splitting a heap
**file** `site/content/13-splits.js` · **LAB**

**One job.** Package disjointness and union into the single relation the logic actually uses, and
prove its associativity — the first proof in the course whose difficulty is real rather than
notational, and which is `star_assoc` with every trace of assertions removed.

**Inherits.** Unit 10's four laws and the two `disjoint_union_*` bridges, plus the observation that
"`h` splits into `h₁` and `h₂`" is a relation nobody has written down.

**Worked example.** `splits_empty_left` as a pure term proof, followed by its tactic transcript —
the two spellings of one object, side by side, one last time before terms become the norm in
Module 3.

**Objectives.**
1. Read `Heap.splits whole left right` as a conjunction, build one with `⟨_, _⟩`, and say why the
   *relation* rather than the operation is what the logic quantifies over.
2. Prove `splits_comm` and `splits_empty_left` as one-line term proofs.
3. Prove `splits_assoc`, whose statement is an existential: choose the witness before discharging
   the obligations, with `refine ⟨w, ⟨_, ?_⟩, ⟨_, rfl⟩⟩`, and `subst` the heap equations *before*
   building the goal.
4. Name the two `disjoint_union_*` uses as the real content: the equation is free (`union_assoc`
   needs nothing), and all the work is reconstructing hypotheses across the bracket.
5. Say in one sentence why this is harder than `union_assoc`. **The associativity of a partial
   operation is not the associativity of its underlying total operation.**

**New Lean.** None new. Consolidates `refine`/`?_`, `obtain` on a conjunction, `subst`, and the
anonymous constructor for an `∃`-of-`∧`.

**Corpus.** `Heap.splits` (def); `splits_empty_left`/`splits_comm` (`m2-8`), `splits_assoc`
(`m2-9`).

**New Lean needed** — ✔ `new-m4.lean`: `splits_empty_right`. Plus ⧗ `union_not_comm`, the Unit 10
counterexample restated by the reader as a theorem (one line; the same shape as the two-singleton
argument already displayed in Unit 10).

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x25` | `splits_empty_right` | D | 1 | symmetry restored; a warm-up before `m2-9`. Its absence in Edition 1 is an asymmetry the reader would notice |
| `m2-8` | `splits_empty_left` / `splits_comm` | D | 2 | term proofs over a conjunction; `Eq.symm` to turn a unit law round |
| `m2-9` | `splits_assoc` | C | 4 | **the module checkpoint.** Everything hard about associativity of `∗`, stripped of all assertion machinery. Three lines: `disjoint_union_left.mp` to take a disjointness apart, `disjoint_union_right.mpr` to build a new one, `union_assoc` for the equation |
| `x26` | `union_not_comm` | **G** | 2 | *design*: "state and prove that union is not commutative in general." The reader converts a demonstration into a theorem, and writes a negated statement from scratch for the first time |

**Retrospective.** (i) Which single law needs disjointness? (ii) Why is associativity free?
(iii) If you replaced heaps with something else, what exactly would you have to reprove?

**Hook.** "`(Heap, union, empty, disjoint)` is a partial commutative monoid, and you can split and
re-bracket. Not one line of this module has mentioned truth, or a proposition about memory, or a
program. The logic starts now."

**Size.** ~2 screens of prose, ~18 blocks: the worked example, 1 `txt` diagram of the
re-bracketing, 1 `trace` on `splits_assoc` with the two `disjoint_union_*` uses called out, plus
4 `ex`.

---

## D.3 Module 3 · The logic of ownership

---

### Unit 12 · `assertions` · Assertions and entailment
**file** `site/content/14-assertions.js` · **phase** `Phase 2 · The logic of ownership`

**One job.** Lift the algebra to a logic, and make clear that lifting the *classical* connectives
achieves nothing — so the reader is primed to notice when something finally does.

**Inherits.** Module 2 proved `(Heap, union, empty, disjoint)` is a PCM and said the logic starts
now. Nothing in it mentioned a proposition about memory.

**Objectives.**
1. Read `Assertion := Store → Heap → Prop` and justify **both** arguments — the heap divides, the
   store does not — by pointing at where the definition of `∗` would fail with only one.
2. Prove an entailment by `intro σ h hp` on a goal that displays as `P ⊢ Q` with no visible
   binders, and explain why that works: `⊢` is a folded `def`.
3. Give term proofs of `entails_refl` and `entails_trans` and recognise them as the identity
   function and composition. **The reader will write `entails_trans` dozens of times and should
   know it is literally function composition.**
4. Lift `True`, `False`, `∧`, `∨`, `∃` pointwise, and prove the three `aAnd` rules as projections
   and pairing.
5. Lift an ordinary proposition about the store into an assertion with `fact`, and say what it
   does *not* claim.
6. Declare an infix notation with a precedence and predict how a mixed expression parses.

**New Lean.** `infix:40 " ⊢ " => Entails` — the first custom notation — and precedence numbers;
`Sort u` and universe polymorphism (declared with `aExists`; first exercised in Unit 15); applying
a proved entailment to a store, a heap and a premise (`h₁ σ h hp`); term proofs at three binders
(`fun _ _ hp => hp`).

**New mathematics / SL.** Assertion as a predicate on states. Entailment as inclusion of
predicates; preorder (defined, not assumed). The pointwise lifting of a logic along a parameter.
`fact` — the *trivial* embedding of a proposition, which says nothing about the heap.

**Corpus.** `Assertion`; `Entails`, `⊢`; `AssertionEquiv`, `⊣⊢`; `aTrue`, `aFalse`, `aAnd`, `aOr`,
`aExists`, `fact`; `entails_refl`/`entails_trans` (`m3-2`), `and_left`/`and_right`/`and_intro`
(`m3-3`).

**New Lean needed** — ✔ `new-m4.lean`: `or_left`, `or_right`, `or_elim`, `equiv_refl`,
`equiv_symm`, `equiv_trans`. Plus ⧗ two one-liners: `aAnd P Q ⊣⊢ aAnd Q P` and
`aAnd P (aAnd Q R) ⊣⊢ aAnd (aAnd P Q) R`.

Edition 1 defines `⊣⊢` in M3 and never proves it is reflexive, symmetric or transitive, which
leaves every later `⊣⊢` chain unjustified. `equiv_*` closes that gap and costs three lines.

**Exercises (5).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m3-2` | `entails_refl` / `entails_trans` | D | 1 | identity and composition; the glue for every chain from Unit 15 on |
| `m3-3` | `and_left` / `and_right` / `and_intro` | D | 1 | projections and pairing. **The unit says so explicitly: remember that `∧` has projections. In two units you meet a conjunction that does not** |
| `x27` | `or_left` / `or_right` / `or_elim` | D | 2 | completes the classical picture, so there is something to contrast `∗` against |
| `x28` | `equiv_refl` / `equiv_symm` / `equiv_trans` | D | 1 | makes every later `⊣⊢` chain legitimate |
| `x29` | `aAnd` commutativity and associativity, as `⊣⊢` | D | 2 | a baseline. `∧` is commutative, associative, idempotent and projective; the next module's connective keeps the first two and loses the last two, and a reader who has proved all four here will feel exactly which ones go |

**Hook.** "Every definition so far has been a lifting, and every proof the corresponding proof one
level down. Nothing about *memory* has entered the logic. It enters with one definition, and there
are two candidates for it — the question Unit 07 posed and did not answer."

**Size.** ~3 screens, ~20 blocks: 1 `dl` on the two arguments of `Assertion`, 1 `defn` per
connective, 1 `anat` on `Entails` showing why `intro σ h hp` works.

---

### Unit 13 · `pointsto` · `emp`, `↦`, and exact ownership
**file** `site/content/15-pointsto.js`

**One job.** Answer Unit 07's question with a definition, and prove the first two theorems that are
about ownership rather than about truth.

**Inherits.** Unit 07 showed the loose reading destroys the free rule and left the exact reading
unformalised; Unit 12 built the type in which to formalise it.

**Objectives.**
1. Define `emp` and `pointsTo` as *equations* on the heap, and say why the heap argument appears in
   an equation rather than a membership test.
2. Read `l ↦ v` aloud in the first person — "I own exactly the cell `l`, and it contains `v`" —
   and use that reading to predict which entailments can hold.
3. Prove that owning `l` with `v₁` *and* owning `l` with `v₂` forces `v₁ = v₂`, and say why the
   conclusion must be `fact` and not something stronger.
4. Prove `¬ ((l ↦ v) ⊢ emp)` and explain why a machine-checked *non*-entailment is worth as much as
   an entailment.
5. Use `subst` on a hypothesis whose type is only *definitionally* an equation between heaps.

**New Lean.** `infix:60 " ↦ " => pointsTo` and its interaction with the `∗` precedence declared
next unit; `subst` seeing through a `def` — `hp : (l ↦ v) σ h₁` is definitionally
`h₁ = Heap.singleton l v`. (`Option.some.inj` was introduced in Unit 02 and is first *needed* here.)

**New mathematics / SL.** **Exact ownership — the decision, finally made.** The first-person
reading of an assertion. The difference between "the heap contains this" and "this is what I have".
Why a value is determined by the resource.

**Corpus.** `emp`, `pointsTo`, `↦`; `pointsTo_value_unique` and `pointsTo_not_emp` (`m3-1`).

**New Lean needed** — ⧗ one one-liner: `emp ⊣⊢ fun _ h => ∀ l, h l = none`. (`funext` in assertion
clothing; it reassures the reader the equational style is not a trick.)

**Author's note.** `pure` is **not** introduced here. Edition 1 introduces `fact` and `pure`
together in M3 and justifies the distinction with a forward reference to `∗`, defined in the next
chapter — the reader is asked to accept a distinction whose criterion does not exist yet. In
Edition 2 `pure` arrives in Unit 17, after `∗`, as the answer to a question the reader can then
ask. Do not mention it here.

**Exercises (2).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m3-1` | `pointsTo_value_unique` and `pointsTo_not_emp` | C | 3 | transport two heap equations to one equation between singletons, evaluate at `l`, strip the `some`; then the refutation that shows ownership cannot be discarded — the seed of Unit 14 |
| `x30` | `emp ⊣⊢ fun _ h => ∀ l, h l = none` | D | 2 | "the heap *is* empty" and "the heap has nothing anywhere" agree |

**Hook.** "`l₁ ↦ v₁` and `l₂ ↦ v₂` each claim to own *all* of the heap they are evaluated at, so
`aAnd (l₁ ↦ v₁) (l₂ ↦ v₂)` is nearly always false and is never what you mean. Saying 'I own this
cell *and separately* that one' needs a conjunction that divides the heap between its conjuncts.
There is exactly one way to write it, and Module 2 has already proved everything it needs."

**Size.** ~3 screens, ~22 blocks: 1 `quote` (the first-person reading), 1 `cmp` recalling Unit 07's
two readings now as two `Assertion`s, 1 `note kind:key`, 1 `trace` on `pointsTo_not_emp`.

---

### Unit 14 · `star` · Separating conjunction, and what it cannot do
**file** `site/content/16-star.js`

**One job.** Define `∗`, install the two mechanical moves — supply a cut, or receive one — and
then, **before any law**, prove the two failures, because what makes this a different logic is what
it cannot do, and every structural rule in the remaining twenty units exists to compensate.

**Inherits.** Unit 13 ended needing a conjunction that divides the heap. It also left `and_left :
aAnd P Q ⊢ P`, proved in one line, which is about to have no analogue.

**Objectives.**
1. Write the definition of `∗` from memory and name its four components in order; say what each of
   `disjoint h₁ h₂` and `h = union h₁ h₂` is holding up, by exhibiting what goes wrong when each is
   deleted.
2. Explain that the cut is **existentially quantified**, and derive from that single fact the
   asymmetry between proving a star (you must choose the cut — the only creative act) and using one
   (you are given a cut you know nothing about).
3. Destructure a star hypothesis in one `intro` pattern with six names, and build one with a flat
   `⟨…⟩`, explaining why the anonymous constructor flattens.
4. Prove `(l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse` in three lines using only Unit 08.
5. State and prove `¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4))` — **no weakening** — and read the witness.
6. State and prove `¬ (∀ P, P ⊢ P ∗ P)` — **no contraction** — and identify the exact clause of the
   definition that forbids it, by showing that deleting the disjointness conjunct yields a
   connective that *is* duplicable.
7. Say what a substructural logic is, which structural rule of ordinary logic corresponds to each
   failure, and predict the consequence: since you cannot drop an unused conjunct from a
   precondition, there must be a rule that carries it through. **Name that rule before meeting it.**

**New Lean.** `infixr:55 " ∗ " => star`; deeply-destructuring `intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩`;
`show` used to unfold a goal into its six slots for readability. Nothing else — and the unit says
so, because it is the honest report: **the two most important theorems in the module need no syntax
you do not already have.**

**New mathematics / SL.** The separating conjunction, and the reading "the heap splits". Why `⊎` on
paper is three Lean conjuncts (it asserts disjointness, forms the union, and names the
decomposition — one operator doing three jobs). The contrast with `∧` as a picture: `∧` gives both
conjuncts the same heap, `∗` gives them complementary ones. **Weakening** and **contraction** as
structural rules, defined for a reader who has not met the terms. **Substructural logic**; linearity
in resources. The slogan *forgetting a conjunct would mean leaking the memory it owns*, made into a
theorem.

**Corpus.** `star`, `∗` (definition). No corpus theorems — and that is the point of the unit.

**New Lean needed** — ✔ `new-m4.lean`: `star_intro`, `star_same_loc_absurd`, `no_star_weakening`,
`starNoDisj`, `starNoDisj_dup`, `no_star_duplication`, `star_not_weakening` (the general form).

**The foldable aside that must not be buried.** Under the *loose* `↦` of Unit 07, weakening **is**
provable (`ptsAtLeast l v ∗ Q ⊢ ptsAtLeast l v`). So exactness is not what gives you non-aliasing —
disjointness gives you that. Exactness is what gives you the **absence of weakening**. That is the
precise statement of what Unit 07's decision bought, and Edition 1 hides it three clicks deep
inside `m4-7`'s `deep` array. Here it is the concluding argument of the unit.

**Exercises (5).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x31` | `star_intro`: given `hp`, `hq`, `hd` and `h = h₁ ⊎ h₂`, produce `(P ∗ Q) σ h` | D | 1 | the construction move in isolation, with no lemma lookup |
| `x32` | `star_same_loc_absurd` | C | 2 | the consumption move; the first cash-in of `singleton_disjoint_iff` |
| `x33` | `no_star_weakening` | C | 4 | **no weakening** — the frame rule's reason to exist. A two-cell heap cannot *be* a one-cell heap. Referred back to by name in Units 23, 27 and 34 |
| `x34` | `no_star_duplication` | C | 4 | **no contraction** — absent from Edition 1 entirely. Four lines, the last of which is `((singleton_disjoint_iff 7 7).mp hd) rfl`; uses `x19` |
| `x35` | `starNoDisj_dup` | C | 3 | delete disjointness and duplication returns. The reader localises contraction to a single conjunct — genuinely surprising and memorable |

Refutations are harder than proofs because you must produce a witness, and the unit says so before
the first one.

**Hook.** "A connective with no projection and no duplication. Whether it has anything at all is
the next question: does it even have a unit? Is it commutative?"

**Size.** ~5 screens, ~30 blocks: 1 `anat` on the definition with six callouts — **the only `anat`
on `star` in the whole course**; 1 `svg` (`P ∧ Q` versus `P ∗ Q`); 1 `trace` of a six-name
`obtain`; 1 `dl` (weakening / contraction); 1 `note kind:warn` on the consequence for
preconditions; 1 `detail` (exactness versus disjointness).

---

### Unit 15 · `star-algebra` · LAB — the laws of `∗`
**file** `site/content/17-star-algebra.js` · **LAB**

**One job.** Prove everything routine about `∗` in one sitting, so that Unit 16 can give
associativity the room it needs.

**Inherits.** Unit 14 established two failures and left open whether anything succeeds.

**Worked example.** `star_emp_left` in full — six-way destructuring, then the
`rw [hu, he, union_empty_left]` rhythm — with every goal state printed, followed by
`star_emp_left_intro` to show that the *converse* is where you must choose `Heap.empty` as one
half.

**Objectives.**
1. Prove both unit laws and both converses, and hence `emp ∗ P ⊣⊢ P`; observe why they are two
   theorems, not one.
2. Prove commutativity and point at the single `rw` where the PCM's commutativity is spent; know
   the counterexample that shows it is false without `hd`.
3. Prove monotonicity and **derive** the two one-sided specialisations from it as term proofs.
4. Prove that `∗` distributes over `∨` and commutes with `∃`, and say why the `∃` case is the one
   that matters for Unit 33.
5. Recognise, in a failed proof, whether an equation slot wants its lemma reversed — the `.symm`
   discipline.
6. Package a pair of entailments as a `⊣⊢` using Unit 12's `equiv_*`, and rewrite *inside* a star
   with `star_congr`.

**New Lean.** `entails_trans` chaining in term mode with no `intro`; `by …` used inside a term-mode
tuple slot (as in `star_comm`'s equation slot). `Sort u`, declared in Unit 12, is first exercised
here by `star_exists_left`.

**New mathematics / SL.** Monotonicity of a connective, and the observation that monotonicity plus
`⊣⊢` gives congruence. The `∀`/`∃` asymmetry: `∗` commutes with `∃` in both directions but with `∀`
in only one, and the reason is quantifier order over the cut.

**Corpus.** `star_emp_left`/`star_emp_right` (`m4-1`), `star_emp_left_intro`/`star_emp_right_intro`
(`m4-2`), `star_comm` (`m4-3`), `star_mono` + `star_mono_left`/`star_mono_right` (`m4-5`),
`star_or_left`/`star_exists_left` (`m4-6`).

**New Lean needed** — ✔ `new-m4.lean`: `star_emp_left_iff`, `star_emp_right_iff`, `star_comm_iff`,
`star_congr`. Edition 1's `illustration`s `star_or_left_conv`, `aForall`, `star_forall_left` and
`star_forall_right_fails` (the `Bool`-indexed counterexample) are retained.

**Exercises (6).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m4-1` | `star_emp_left` / `star_emp_right` | C | 2 | consume a star; first six-way destructuring |
| `m4-2` | `star_emp_left_intro` / `star_emp_right_intro` | C | 2 | **construct** a star; the cut is forced, which is why this is the right place to learn to choose one; the `.symm` discipline on the equation slot |
| `m4-3` | `star_comm` | C | 2 | one line of content — `union_comm hd`. **Variants:** without `hd` it is false, and the witness is two singletons at one location where left-biasing becomes visible |
| `m4-5` | `star_mono` and its two specialisations | D | 2 | the only law in the module whose proof mentions no heap lemma at all; improve one side without touching the other |
| `m4-6` | `star_or_left` / `star_exists_left` | C | 2 | destructure and rebuild with the same cut. **`star_exists_left` is the first line of the inductive step of both list theorems in Unit 33**, and the lab says so |
| `x36` | `star_emp_left_iff`, `star_comm_iff`, `star_congr` | D | 1 | package the directions; the reader can now rewrite *inside* a star, which is what makes Unit 17's toolkit feel like algebra instead of plumbing |

**Retrospective.** (i) Which of the laws is an equivalence and which only an entailment, and why?
(ii) Where exactly did `union_comm`'s disjointness hypothesis end up in `star_comm`? (iii) Why is
there no `star_and_left`?

**Hook.** "Unit, commutative, monotone, distributive. One law is missing, and it is the one that
lets you stop thinking about a *tree* of stars and start thinking about a *list* of owned
resources. It is also the only one whose proof has to manufacture hypotheses — but Unit 11 already
did that work."

**Size.** ~3 screens of prose, ~24 blocks plus 6 `ex`: the worked example, 3 `trace`, 1 `detail`
on the `∀`/`∃` asymmetry.

---

### Unit 16 · `star-assoc` · Associativity
**file** `site/content/18-star-assoc.js`

**One job.** One theorem, both directions, done properly — because it is the theorem that closes
the commutative monoid, and it is the hardest pure-`∗` proof in the course.

**Inherits.** Unit 15 left exactly one law unproved, and Unit 11 proved its heap-level content as
`splits_assoc`. The unit opens by putting the two statements side by side.

**Objectives.**
1. Draw the re-bracketing picture before writing Lean, and say which heaps move (none — only the
   brackets do).
2. Destructure a star whose conjunct is itself a star, in a single nested `intro` pattern.
3. Eliminate an intermediate heap with `subst hu₂` *before* building the goal, and say why that
   leaves the goal untouched.
4. Extract two pairwise disjointness facts with `disjoint_union_left.mp` and assemble a third with
   `disjoint_union_right.mpr` — and say why the names refer to which side of `Heap.disjoint` the
   union sits on, not to which side of the goal you are working on.
5. State that the heap equation is `union_assoc` and generates nothing to discharge, so that
   **all** the work is disjointness bookkeeping.
6. Read the mirror-image proof and predict which two lemmas swap.

**New Lean.** Deeply nested `intro` patterns (a six-slot tuple with a six-slot tuple inside slot 5,
or slot 6). Nothing else — and the unit says so, because that is the honest report: the difficulty
here is mathematical, not syntactic.

**New mathematics / SL.** The commutative monoid of assertions, complete. The *induced* structure:
`∗` is not a connective about heaps, it is the connective any PCM induces — stated here as a claim
whose **proof** is Unit 38. (That is a forward reference to a proof, not to a definition: `PCM` is
already in hand from Unit 10. That is the difference between a promise and a hole.)

**Corpus.** `star_assoc_left`/`star_assoc_right` (`m4-4`).

**New Lean needed** — ✔ `new-m4.lean`: `star_assoc_iff`.

**Exercises (2).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m4-4` | `star_assoc_left` / `star_assoc_right` | C | 4 | the hardest pure-`∗` proof; both directions. **Variants worth keeping from Edition 1:** delete disjointness from `∗` altogether and associativity *survives* (because `union_assoc` needs no hypothesis) while commutativity dies — the two laws fail for genuinely different reasons |
| `x37` | `star_assoc_iff` | D | 1 | package it |

One `hard` exercise on a whole page is deliberate. It gets a full `trace` of the forward direction,
a `steps` block mapping each `refine` obligation to its picture, a `cmp` of the two directions with
the swapped lemmas highlighted, a four-rung hint ladder, and a `variants` field asking what happens
if you try to get it from `star_comm` and one direction only (you cannot — associativity is not a
consequence of commutativity).

**Hook.** "The algebra is nearly complete and you can move resources around freely. Two things are
missing before it can be used. First: how do you attach an ordinary proposition — '`tmp` holds 7' —
to a separating conjunction, when a proposition owns no memory?"

**Size.** ~4 screens, ~22 blocks: 1 `txt` box diagram of the re-bracketing, 2 `trace`, 1 `detail`
on `subst` and when it refuses.

---

### Unit 17 · `pure` · Propositions inside a `∗`, and the toolkit
**file** `site/content/19-pure.js`

**One job.** Answer Unit 16's question, introduce `pure` as the `∗`-compatible embedding of a
proposition, prove the non-aliasing theorem at the assertion level, and assemble the normalisation
library that Modules 7 and 8 consume.

**Inherits.** Unit 16's open question, and Unit 12's `fact`, whose partner for `∗` has not been
named.

**Objectives.**
1. State the two embeddings of a store proposition — `fact φ` (says nothing about the heap) and
   `pure φ` (`φ`, *and I own nothing*) — and say which connective each pairs with **and why**: an
   embedding must match the resource discipline of the connective it will sit under.
2. Prove `pure φ ∗ P ⊣⊢ aAnd (fact φ) P`, the formal content of that slogan.
3. Prove `two_cells_distinct` and explain why its conclusion is `fact` and not `pure`.
4. Build `star_swap_middle` from associativity and commutativity — a three-lemma composition with
   no `intro`, no heap and no tuple in it. **The unit states the rule: if you find yourself typing
   `intro σ h ⟨…⟩` here, stop.**
5. Push `∗` past `∨` and `∃` in both directions, and pick the right lemma from the toolkit given a
   target shape.

**New Lean.** No new tactic. New **skill**: proof by composition. The centrepiece is
`star_swap_middle`, which in the corpus is a single term:
`entails_trans (star_assoc_right P Q R) (entails_trans (star_mono_left R (star_comm P Q))
(star_assoc_left Q P R))`. The reader is walked through building it from the outside in, and this
is the technique that makes `lseg_append` a five-line proof in Unit 33.

**New mathematics / SL.** The two embeddings and the general principle behind them. **Ownership
implies non-aliasing**, at the assertion level. Normalisation as an activity: putting a
precondition into the shape the next rule wants.

**Corpus.** `pure`; `two_cells_distinct` (`m4-7`); `star_swap_middle`, `star_rotate_left`,
`star_rotate_right`, `star_pure_left`, `star_pure_right` (`m4-8`).

**New Lean needed** — ✔ `new-m4.lean`: `star_or_right`, `star_exists_right`.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m4-7` | `two_cells_distinct` | C | 2 | **the punchline of Phase 1.** The precondition of a two-cell program already contains its non-aliasing information. Unit 32's `node_cells_distinct` is one application with no proof, and Unit 27's `write_with_frame` never needs `l ≠ other` as a hypothesis |
| `m4-8` | `star_pure_left`/`right`, `star_swap_middle`, `star_rotate_left`/`right` | C | 3 | **proof by composition**; the toolkit, complete. **Variants:** replace `pure` by `fact` in `star_pure_left` and it becomes false, for exactly `no_star_weakening`'s reason; in the other direction it stays true but useless, because `fact φ ∗ P` does not pin the cut |
| `x38` | `star_or_right` / `star_exists_right` | C | 2 | the converses; the reader discovers both hold, and that this is *not* automatic |

**Hook.** "The algebra is complete and every law it has is proved. It cannot state the frame rule,
because the frame rule says a *command* leaves the frame alone, and there are no commands. The next
module builds them, and mentions `∗` exactly zero times."

**Size.** ~3 screens, ~26 blocks: 1 `txt` for the `fact`/`pure` pairing table, 1 `tbl` of the whole
module's laws with the shape each turns into what — which the reader will consult constantly from
Unit 29 onwards — 1 `dod`.

---

### §`compare` · The same proof, several ways
**file** `site/content/20-compare.js` · **badge** `§` · **support page**

**Job.** Four worked comparisons, each showing one theorem proved several ways, with an explicit
verdict on which to prefer and why. Placed here because the fourth comparison only makes sense once
the `∗`-algebra exists.

1. **`update_shadow`** — `funext` + `by_cases` + `<;> simp`; explicit `if_pos`/`if_neg`; one
   `simp [update]`. *Verdict:* the middle one once, the first one thereafter.
2. **`disjoint_empty_left`** — term proof `fun _ => Or.inl rfl`; tactic proof `intro; left; rfl`;
   `simp [Heap.disjoint, Heap.empty]`. *Verdict:* the term, because it is shorter than the goal
   state a tactic proof would print.
3. **`write_singleton`** — pointwise with `simp`; pointwise with `rw`; via `write_of_eq`.
   *Verdict:* the third *reuses* a lemma, and reuse is the habit.
4. **`star_swap_middle`** — semantically, by destructuring; algebraically, three `entails_trans`.
   *Verdict:* the algebraic one, and the paragraph explaining why is the thesis of Module 3.

A fifth comparison lives in Unit 30 (compositional versus direct `swap_spec`), because it only
makes sense after Module 7.

**Size.** ~24 blocks, mostly `cmp` and `code`. No exercises.

---

## D.4 Module 4 · Programs

---

### Unit 18 · `language` · A language that can get memory wrong
**file** `site/content/21-language.js` · **phase** `Phase 3 · Programs and their semantics`

**One job.** Define the smallest syntax that can commit a memory error, and introduce inductive
datatypes, structures and the equation compiler along the way.

**Inherits.** Unit 17 ended by naming exactly what is missing: a command.

**Objectives.**
1. Declare an inductive datatype with recursive constructors and read its values as the grammar of
   a language; define a function on it by pattern matching, and say why Lean accepts it without a
   termination proof.
2. Read `.const 3` and say what the leading dot resolves to and how; predict how Lean will *print*
   a term you wrote with dot notation, and not be surprised.
3. Read a `structure` as a one-constructor inductive, build one with `⟨σ, h⟩`, project with
   `.store`/`.heap`, and use structure eta.
4. Prove `@Store.set = @update` by `rfl` and re-derive the store's lookup laws from Unit 04 in one
   line each. **The store is `update`.**
5. Say why `BExpr.eval` returns `Bool` while assertions live in `Prop`, and predict the shape of a
   guard hypothesis (`hb : b.eval σ = true`).
6. Say why the store is *not* a resource — it cannot be divided — which is exactly why Unit 24 will
   need a second, non-spatial side condition.

**New Lean.** `inductive … where` with recursive constructors; `deriving Repr`; pattern-matching
`def` (the equation compiler); structural recursion; `.ctor` leading-dot notation; `structure …
where`, field projections, structure eta; `infixr:60 " ;; " => Cmd.seq`; `Bool` versus `Prop` in
earnest; `==`, `!`, `decide`; truncated `Nat` subtraction; `#eval` on a type with `Repr` and its
failure without.

(`structure` was introduced in Unit 10 for `PCM`; here it is reused for `State`.)

**New mathematics / SL.** Abstract syntax as an inductive type. The store/heap split at the level
of states. Expressions that cannot fail versus commands that can. Why `ite` and `loop` are declared
now and unused until Unit 35 — extending an inductive type later means redoing every proof about
it, which is engineering judgement that matters more in a proof assistant than in a compiler, and
is stated as such. **The design decision that `load`/`write`/`free` take a literal `Loc` and not an
expression is stated here with its full price** — Unit 32's list predicates describe structures no
program in this course can walk — so that Unit 32 does not have to apologise and Unit 38 can
discharge it.

**Corpus.** `Atom`, `Atom.eval`, `Store.set`, `State`, `BExpr`, `BExpr.eval`, `Cmd`, `;;`.

**New Lean needed** — ✔ `new-m5.lean`: `@Store.set = @update` by `rfl`, `storeSet_same`,
`storeSet_other`, the truncated-subtraction example, `Atom.size`.

Exercise `x39` repairs Edition 1's biggest structural weakness: there, M0's four `update` laws are
a warm-up thrown away when M1 starts, and M5 silently reintroduces the same function as
`Store.set`. The reader's first four theorems now stay useful for the whole course.

**Exercises (3, all new).**

| id | what | kind | diff | what it buys |
|---|---|---|---|---|
| `x39` | `@Store.set = @update` by `rfl`; then re-derive the two store lookup laws in one line each | D | 1 | **the store is `update`** — the payoff for Unit 04 being about `update` and not about heaps |
| `x40` | evaluate a compound `Atom` under a given store by `rfl`; then `(Atom.minus (.const 3) (.const 5)).eval σ = 0` | D | 1 | concreteness; truncated subtraction met before it can cause a mystery in Unit 37 |
| `x41` | define `Atom.size : Atom → Nat` by structural recursion and prove one equation | C | 2 | structural recursion, before Unit 21 shows a case where it is unavailable |

**Hook.** "We have syntax and no meaning. 'The command writes to memory' has to become
mathematics, and the choice of *how* — a function, or a relation — decides what 'the program
crashed' will mean."

**Size.** ~4 screens, ~26 blocks: 2 `anat` (the `Atom`/`State` group; the `Cmd` group), 1 `txt`
mapping constructors to concrete syntax, 1 `cmp` (`Bool` versus `Prop` guards), 2 `note` on naming
traps (`while` is a reserved token; `⦃ ⦄` is taken).

---

### Unit 19 · `exec` · Running a command is a relation
**file** `site/content/22-exec.js`

**One job.** Meet Lean's refusal of the interpreter, take it seriously, define `Exec` as an
inductive relation, and do the first inversions.

**Inherits.** Unit 18's syntax with no semantics.

**Objectives.**
1. Read Lean's `fail to show termination` message on the naive interpreter and say which two
   parameters it tried.
2. State the second, deeper objection — an `Option`-valued interpreter conflates faulting with
   diverging — and see that taking it seriously dissolves the first.
3. Read `inductive Exec : Cmd → State → State → Prop` as a set of inference rules; read a proof of
   `Exec c s s'` as a finite derivation tree; state the closure property that makes it the *least*
   relation closed under the rules.
4. Distinguish **indices** from **parameters** and say why that distinction is what makes inversion
   possible.
5. Invert a derivation with `cases h`, read the `case` labels and inaccessible names, and name an
   inaccessible hypothesis with `rename_i` — and say why you cannot simply type `s'✝`.
6. Prove that a stuck program has *no* final state, and explain why a memory fault therefore needs
   no error value in the semantics.

**New Lean.** `inductive … : … → Prop`; indices versus parameters; implicit constructor arguments
`{s}`; premises as explicit constructor arguments; `cases h` as **inversion**;
`cases h with | ctor a b => …`; the `case skip` tag; inaccessible names `x✝` and the fact that `✝`
is not an input character; `rename_i`; the "too many variable names provided" error and what it
tells you about which fields are explicit; `fail to show termination` and `termination_by` (named,
not used).

**New mathematics / SL.** **Inductively defined relations** — the least relation closed under the
rules, explained properly for a reader who has not met the phrase, with two derivation trees drawn.
**Big-step (natural) semantics.** *Stuck* versus *diverging*, and the fact that this semantics
conflates them — with a forward pointer to Unit 35, where the distinction finally matters.
**Inversion** as a proof principle. Determinism as something to be proved rather than assumed.

**Corpus.** `Exec` (all ten constructors); `exec_skip_inv` (`m5-1`).

**New Lean needed** — ✔ `new-m5.lean`: `exec_load_stuck`, `exec_assign_inv`, `exec_load_inv`,
`exec_skip_seq_inv`. Edition 1's `runBad` (with its exact error) and `load_stuck` illustrations are
real and are retained.

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m5-1` | `exec_skip_inv` | D | 1 | the first inversion, on the one constructor where there is nothing to get wrong; the constructor's own equation eliminates a variable |
| `x42` | `exec_assign_inv`, `exec_load_inv` | C | 2 | inversion that *produces* the final state, then inversion that recovers a *premise* (`hl : s.heap l = some v`). **This is the shape of every proof in Module 6** |
| `x43` | `exec_load_stuck` | C | 2 | **a fault is the absence of a derivation, and the reader proved it.** Edition 1 asserts this in prose and never proves it |
| `x44` | `exec_skip_seq_inv` | C | 3 | nested inversion, and a first sight of the middle state being inaccessible — which motivates `rename_i` before Unit 26 needs it under pressure |

**Hook.** "You can look at the last step of a derivation. The theorem we actually want — that a
command has at most one final state — needs us to reason about *every* derivation at once, and on a
derivation that is not the induction you know."

**Size.** ~4 screens, ~26 blocks: 1 `code` of `Exec` with an `anat` on three representative
constructors, 1 `txt` of the rules drawn as inference rules, 1 `svg` (a derivation tree for a
two-command program), 1 `ul` (stuck versus diverging), 1 `note kind:key` (`Exec` *is* the
definition of safety).

---

### Unit 20 · `induction` · Structural induction, up to derivations
**file** `site/content/23-induction.js`

**One job.** Teach induction properly, from `Nat` upward, ending at induction on a derivation with
a generalised hypothesis — because that is the technique the course cannot do without, and Edition
1 introduces it cold, inside its hardest proof.

**Inherits.** Unit 19 could invert one derivation and could not reason about all of them.

**Objectives.**
1. Prove a statement about all `Nat` by `induction n with | zero | succ n ih`, and about all
   `List α` by `induction xs with | nil | cons x xs ih`.
2. Prove a statement about all derivations by `induction h with | rule args ih => …`, and say why
   there is one case per constructor and what each induction hypothesis says.
3. Recognise when the induction hypothesis is too weak and repair it with `generalizing` — writing
   the proof without it, seeing the `seq` case fail, and reading the failure. **Say precisely what
   `generalizing s₂` does: it reverts `s₂` and everything mentioning it into the goal before the
   induction, and reintroduces them in each case, so the hypothesis speaks about every `s₂` and not
   only the one you started with.**
4. Classify the ten cases of `exec_deterministic` into three shapes —
   deterministic-by-construction, value-carrying, compositional — and handle each.
5. Kill an impossible case by contradicting the guard:
   `rw [hb] at hb'; exact absurd hb' (by simp)`.
6. Transport an equality inside a hypothesis with `▸`, and write the same step by hand with `have`
   plus `subst` when `▸` refuses.
7. Read a goal full of inaccessible names (`s✝`, `v✝¹`) without panic.

**New Lean.** `induction n with | zero | succ n ih`; `List`, `[]`, `::`;
`induction xs with | nil | cons x xs ih`; `induction h with | ctor … ih` on a derivation;
`induction h generalizing y`; `▸`; `cases hl'` as no-confusion on constructor equality
(`some v = some v'`); `exact absurd hb' (by simp)` as the standard refutation of `true = false`;
nested `cases … with` inside an induction branch, and the error you get for confusing their name
lists.

**New mathematics / SL.** **Structural induction**, in three escalating forms. The *induction
hypothesis* as a mathematical object you can state. **Generalisation of the induction hypothesis.**
Determinism of the language, and its use: Unit 35 needs it to derive partial correctness from total
correctness.

**Corpus.** `exec_deterministic` (`m5-2`).

**New Lean needed** — ✔ `new-m5.lean`: `allZeros`, `allZeros_length`, `append_nil`, `exec_id`.

These three warm-ups exist solely so that `induction` is met three times, on objects of escalating
difficulty, before it is met on a derivation *with a generalised hypothesis*. They cost half a
screen and remove the course's steepest cliff. **They were chosen so that no goal is an arithmetic
identity** — `omega` and the `Nat.add_succ` family stay out of the course, because the corpus never
needs them and a tactic introduced for a warm-up is a ledger entry forever.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x45` | `allZeros_length` and `append_nil` | D | 2 | induction on `Nat` and on `List`, on statements the reader already believes, with nothing else in the room |
| `x46` | `exec_id` | C | 3 | prove `Exec c s s' → Exec c s s'` by `induction` rather than `exact h`, purely to see all ten cases and read all ten induction hypotheses. Presented with an explicit *this is deliberately pointless; look at the goals, not at the proof*, and paired with a `trace` showing three of the ten hypotheses side by side |
| `m5-2` | `exec_deterministic` | C | 4 | the real thing. **Pitfall to record verbatim:** omitting `generalizing s₂` fails in the `seq` case, and the error is a type mismatch on `ih₂`, not a message about induction — so the reader must be told to suspect the induction hypothesis |

**Hook.** "The relation proves things and computes nothing. You cannot ask it what a program does —
only offer an answer and ask whether it agrees. Whether that matters is the subject of the next
unit, and the fact that the next unit is *optional* is itself informative about what a relational
semantics is for."

**Size.** ~5 screens, ~26 blocks: 3 `trace` (the `load` case; the `seq` case; a guard clash),
1 `cmp` showing `ih₁` with and without `generalizing` — Edition 1's version of this is the single
best teaching artefact in the current course and is retained verbatim — 1 `steps` classifying the
ten cases into three shapes.

---

### Unit 21 · `interpreter` · LAB — an interpreter, proved to agree
**file** `site/content/24-interpreter.js` · **LAB** · **OPTIONAL**

**One job.** Build a fuelled interpreter, prove it equivalent to the relation so the semantics can
be *tested*, and drill induction on a second, independent example.

**Inherits.** Unit 20's relation, which is good for proofs and useless for testing.

**Status — stated in the unit's first sentence and in the sidebar.** **Optional and off the
critical path.** Nothing later in the course uses `run`, `run_sound`, `run_mono`, `run_le` or
`run_complete` — verified by inspection of `corpus.lean`: no occurrence of any of them after line
735. A reader in a hurry may skip to Unit 22 with no debt, losing only the ability to test the
semantics and the sight of induction on `≤`. **A reader who grinds through `run_complete` believing
the frame rule depends on it is being lied to**, and Edition 1 gives this material a full third of
a milestone with no such signal.

**Objectives.**
1. Say why an interpreter for a language with loops cannot be structurally recursive on the
   command, and how a **fuel** parameter restores termination.
2. Say what `run n c s = none` does and does not tell you, and why soundness is therefore stated
   with `some s'` as its hypothesis.
3. Induct on the **fuel** rather than the command, and explain what `intro n` alone (rather than
   `intro n c s s' h`) buys.
4. Read a hypothesis that *displays* as an unreduced `match` and recognise it as definitionally the
   thing you want — then hand it to `exact` without simplifying.
5. Choose between `simp [run]` and `simp only [run]` by a stated rule.
6. Prove monotonicity in the fuel, then `run_le` by induction on a proof of `≤`, then completeness
   by induction on the derivation, taking `max` in the two-premise cases — and explain why `max`
   and not `+`.
7. State what completeness does **not** give you: no bound on the fuel in terms of the program.

**New Lean.** Fuel-indexed recursion; equation lemmas and `simp only [f]` firing them; definitional
(iota) reduction of a `match` on a literal constructor; `simp only [f] at h ⊢` and the meaning of
`⊢` in a location list; `simpa … using`; `induction hle with | refl | step`; `Nat.le_max_left`,
`Nat.le_max_right`; `max`; `#eval` on a program.

**Ledger fence.** `simpa … using`, `induction hle with`, `Nat.le_max_*` and `max` are introduced
here and used **nowhere else**. No unit after 21 may use them. If a later author reaches for one,
that is a signal that this unit should be made compulsory — and the fence is what makes the signal
audible.

**Corpus.** `run`; `run_sound` (`m5-3`); `run_mono`, `run_le`, `run_complete` (`m5-4`).

**New Lean needed** — ⧗ `run_example`: `example : run 6 prog s₀ = some s₁ := by rfl` on a concrete
two-command program. One `#eval` picks the fuel. Edition 1's `runIf` comparison, the
`spin`/`spin_diverges` illustration and the three `#eval` outputs are real and retained.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x47` | `run_example` | D | 1 | the payoff first: run a program, get an answer, `rfl` closes it. Placed **before** the two hard proofs so the unit opens on a win |
| `m5-3` | `run_sound` | C | 4 | the interpreter never lies. The lesson is definitional reduction: after `rw [hl] at h` the hypothesis *is* what you need, with no simplification |
| `m5-4` | `run_mono`, `run_le`, `run_complete` | C | 5 | `simp only [run] at h ⊢`; induction on a proof of `≤` (three lines, and a genuinely new idea); `max` and `run_le` to reconcile two fuel bounds |

**Retrospective.** (i) What does `run n c s = none` *not* tell you? (ii) Why `max` and not `+`?
(iii) What would break if `Exec` were nondeterministic?

**Hook.** "Two descriptions of the same partial function, and neither says anything about what
*should be true* before or after a run. Nothing in this course so far mentions both a command and
an assertion."

**Size.** ~3 screens of prose, ~22 blocks: the worked example (`run_sound`'s `load` case), 1 `anat`
on `run`'s fuel pattern, 1 `cmp` (relation versus interpreter: what each is good for), 1 `detail`
on `simp` versus `simp only`, 1 `detail` on why `match … with | true | false` beats `if` here.

---

## D.5 Module 5 · The program logic

---

### Unit 22 · `hoare` · Hoare triples
**file** `site/content/25-hoare.js` · **phase** `Phase 4 · The program logic`

**One job.** Join the two threads in one definition, and prove the structural rules that let the
reader stop unfolding `Exec`.

**Inherits.** Module 3 ended with an algebra that could not talk about commands; Module 4 ended
with a semantics that could not talk about what should be true. This unit is the join, and says so.

**Objectives.**
1. Read `Hoare P c Q := ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap` and identify
   the three separate claims the single `∃ s'` is making: no memory fault, termination, and the
   postcondition.
2. Define `PartialHoare` and state precisely how the two differ and when — noting that for the
   loop-free fragment they coincide, which is why the difference is deferred to Unit 35.
3. Prove `hoare_consequence` and read off its variance — contravariant in the precondition,
   covariant in the postcondition, for the same reason a function type is. **Every entailment
   proved about `∗` becomes usable here**, and the unit says so in those words.
4. Prove `hoare_skip` as a term and `hoare_seq` by running the first triple and feeding its final
   state to the second; supply the intermediate assertion with `hoare_seq (Q := …)` and recognise
   that *choosing that assertion is the act of verifying a program*.
5. Define substitution **semantically** and explain why a shallow embedding makes the assignment
   axiom nearly a tautology — no substitution function on syntax, no capture, no substitution
   lemma.
6. Use `show` to force a folded assertion open at exactly the point `simp` needs to see it.

**New Lean.** Named arguments `(Q := …)`; `obtain` on a triple's output; building `⟨s', hex, hq⟩`
witnesses by hand. `show` (Unit 02) becomes load-bearing here and stays that way.

Note the ordering constraint: named arguments are needed by `assign_twice` in *this* unit, so they
are introduced here in one sentence at the point of first use. Unit 29 then discusses *why you must
supply `Q`* — that Lean cannot guess it because it is genuinely a creative choice — which is a
different point and belongs there.

**New mathematics / SL.** The **Hoare triple**. **Total versus partial correctness**, defined and
contrasted. **Safety as an existential.** Shallow versus deep embedding, and semantic substitution.
Variance.

**Corpus.** `Hoare`, `PartialHoare`, `subst` (the assertion transformer); `hoare_consequence`
(`m6-1`), `hoare_skip`/`hoare_seq` (`m6-2`), `hoare_assign` (`m6-3`), `assign_constant` (`m6-4`),
`assign_twice` (`m6-5`).

**New Lean needed.** None.

**Exercises (5, all corpus).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m6-1` | `hoare_consequence` | D | 2 | pre- and post-composition; variance; the rule that connects Module 3 to Module 5 |
| `m6-2` | `hoare_skip` / `hoare_seq` | C | 2 | one term proof and one three-line tactic proof, and the contrast is the lesson |
| `m6-3` | `hoare_assign` | D | 2 | three lines, two of them boilerplate; the payoff of the semantic `subst`; the backwards reading |
| `m6-4` | `assign_constant` | C | 2 | **first `show` in anger**, on a goal that displays as an opaque assertion application |
| `m6-5` | `assign_twice` | C | 3 | first self-chosen intermediate assertion. **And what you do *not* need:** there is no `x ≠ y` hypothesis and Lean will tell you it is unused; the degenerate case `x = y` works because `y := x` copies. A formalisation catching a side condition the reader assumed was necessary is worth a page and gets one |

**Hook.** "Three rules, and none of them touches the heap. The moment a rule does, the question
Unit 07 answered becomes operational: *how much* memory does the rule mention?"

**Size.** ~4 screens, ~30 blocks: 1 `anat` on `Hoare` with the existential's three jobs called out,
1 `cmp` (total versus partial), 1 `anat` on `subst`, 1 `note kind:key`, 1 `note kind:warn` (the
bracket notation `⦃ ⦄` you cannot have).

---

### Unit 23 · `small-footprint` · Rules that mention only what they touch
**file** `site/content/26-small-footprint.js`

**One job.** State the primitive memory rules on exactly the cells they touch, cash in Unit 07's
exactness decision — and then *fail* to compose them, deliberately and at length.

**Inherits.** Unit 22's structural rules, none of which mentions the heap.

**Objectives.**
1. State the design principle: a primitive specification mentions only the cells the command
   touches; larger heaps are the frame rule's problem.
2. Explain why `{l ↦ v} free l {emp}` is a theorem here and would be **false** under Unit 07's
   loose reading — pointing at exercise `x18` by name.
3. Prove `hoare_load` and see that the postcondition's `pure` conjunct *forces* the cut to be
   `Heap.empty ∗ Heap.singleton l v`; explain why it must be `pure` and not `fact`.
4. Prove `hoare_write` and `hoare_free`, each of which is **one application of a Unit 06 lemma**
   (`write_singleton`, `erase_singleton`). The unit makes the layering point explicitly: if you had
   not proved those in Unit 06 you would now be doing `funext` inside a Hoare proof, which is the
   violation the whole discipline exists to prevent.
5. Say why reading is not destructive and the cell reappears in the postcondition.
6. Prove a two-command specification with **no frame rule available**, by building the `Exec`
   derivation by hand, and articulate exactly which step was intolerable.

**New Lean.** `subst hp` on a hypothesis `h = Heap.singleton l v`, replacing the heap variable
throughout; `refine` with several holes inside one tuple in a Hoare-triple goal. No new tactics —
deliberately, because the difficulty here is entirely in choosing what to build.

**New mathematics / SL.** **Small-footprint specification.** The trade separation logic makes: tiny
exact specifications plus one structural rule, instead of big specifications with side conditions.
Exact ownership doing real work: the free rule *is* `erase_singleton` with a wrapper.

**Corpus.** `hoare_load` (`m7-1`), `hoare_write` (`m7-2`), `hoare_free` (`m7-3`),
`clearCell`/`clearCell_spec` (`m7-4`), `readAndFree`/`readAndFree_spec` (`m7-5`).

**New Lean needed** — ⧗ `writeTwice_spec`:
`Hoare (l ↦ old) (.write l (.const 1) ;; .write l (.const 2)) (l ↦ 2)`, by `hoare_seq` and two
applications of `hoare_write`. (Low risk; the shape is `assign_twice`'s.)

**Exercises (6).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m7-1` | `hoare_load` | C | 3 | the deepest witness construction so far; the whole proof is choosing the cut, and the cut is forced because `pure` must own the empty heap |
| `m7-2` | `hoare_write` | C | 2 | one application of `write_singleton` |
| `m7-3` | `hoare_free` | C | 2 | one application of `erase_singleton`; the rule that would be unsound with an inexact `↦`, here trivial |
| `m7-4` | `clearCell_spec` | D | 1 | literally `hoare_write` specialised; `(Atom.const 0).eval σ` reduces definitionally, so no consequence rule is needed. Opens the unit on a win |
| `x48` | `writeTwice_spec` | C | 2 | composition that *does* work, because both commands have the same footprint. The baseline against which the next exercise fails |
| `m7-5` | `readAndFree_spec` | C | 3 | **the deliberate defeat.** The load's postcondition `pure … ∗ l ↦ v` is not the free's precondition `l ↦ v`, so the reader must abandon the rules and rebuild the derivation from `Exec.seq`. The `why` field says so in advance, and the `solNote` says: *you will redo this in four structural rules in Unit 29* |

**Author's note.** The unit's `dod` records the failure explicitly. The reader is asked, while
proving `m7-5`, to note which step forced them back to `Exec`; the closing section collects those
notes into three questions whose answers are the statement of `HeapLocal`: (i) what did the load's
postcondition have that the free's precondition did not want? (ii) if a command runs correctly on a
small heap, what would you have to know to conclude it runs correctly on a bigger one? (iii) name a
command for which that would be *false*.

**Hook.** "Question (iii) has an answer, and it is the reason the next module takes five units
instead of one. Three correct rules that will not compose, and one program proved from the
semantics: the missing tool is a rule saying *a command that works on its own memory still works
inside a bigger heap*. That rule cannot be assumed — it is a claim about what commands *do* — so
the next unit has to find out what it would take for it to be true."

**Size.** ~4 screens, ~30 blocks: 1 `txt` of the three rules in textbook notation, 1 `note
kind:key` on exactness paying for itself, 1 `cmp` (the exact rule versus the inexact one that would
be unsound), 1 `dod` that records the failure.

---

## D.6 Module 6 · Locality and the frame rule

---

### Unit 24 · `locality` · What "local" has to mean
**file** `site/content/27-locality.js` · **phase** `Phase 5 · Locality and the frame rule`

**One job.** *Discover* the definition of `HeapLocal` rather than be handed it — by writing the
textbook version, starting the frame proof, running it into a wall, and reading the missing
conjunct off the goal that cannot be closed. Then find the second, non-spatial gap from a
three-line counterexample about a program variable.

**Inherits.** Unit 23's three questions.

**Objectives.**
1. State the frame rule informally and say why it is a *theorem about the semantics*, not an axiom
   of the proof system.
2. Write the textbook locality statement as a Lean `def` and read it as a **commuting square**:
   extend by the frame then run, or run then extend by the frame.
3. Say why the conclusion is existential rather than an equation — `Exec` is a relation, so there
   is no final state to compute and one must be exhibited.
4. **Derive** the missing conjunct `Heap.disjoint s'.heap hFrame` by identifying the single goal in
   the frame proof that no hypothesis can reach, and argue that a fact about the command belongs in
   the definition of *local*.
5. Exhibit the store counterexample — `{x = 0} x := 1 {x = 1}` framed with `x = 0` — and prove
   both halves in Lean.
6. State `Preserves` semantically and say why the textbook syntactic condition
   `modifies(c) ∩ freeVars(R) = ∅` is not merely inconvenient here but **unstatable**: an
   `Assertion` is an arbitrary function with no syntax to take the free variables of.
7. Discharge `Preserves` for any assertion built from `↦`, `emp` and `∗`, and identify the exact
   assertion at which that route stops.

**New Lean.** None. Stated deliberately: **the hardest conceptual unit in the course introduces no
syntax.** Everything is definition-design and one stuck goal. (`sorry` appears here for the first
and only time in a *displayed* proof — the stranded frame proof — never in a solution.)

**New mathematics / SL.** **Locality** as a simulation property of an operational semantics — and
the observation that whether it holds depends entirely on which commands the language has, not at
all on the assertion language. The **commuting square** reading. **Non-interference** on the store,
as a second and independent obligation, following from Unit 18's observation that the store is not
a resource. Semantic versus syntactic side conditions.

**Corpus.** `HeapLocal`, `Preserves`, `HeapOnly`; `preserves_of_heapOnly`, `heapOnly_pointsTo`,
`heapOnly_emp`, `heapOnly_star`; `heapLocal_skip`/`heapLocal_assign`/`heapLocal_load` (`m8-1`).

**New Lean needed** — ✔ `new-m8.lean`: `not_heapOnly_pure`, `frame_needs_preserves` (both halves —
the triple holds, the framed triple does not). Plus, retained from Edition 1's `09-m8.js` and real:
`HeapLocalWeak` (the version one conjunct short) and its **stranded frame proof**, which compiles
with one `sorry` and is the unit's central exhibit — it must be *shown*, not described.

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m8-1` | `heapLocal_skip` / `_assign` / `_load` | C | 2 | the shape, three times; `union_of_some` is the whole content of the `load` case — *the frame cannot change what a load reads* |
| `x49` | `heapOnly_emp`, `heapOnly_pointsTo`, `heapOnly_star` | D | 2 | promoted from `code` to `ex`. The first two are `fun _ _ _ hr => hr` — the dividend of having written `pointsTo` as an equation with the store ignored. `heapOnly_star` is a six-way destructuring the reader can now do in their sleep, and it **covers any frame at any size**, which is what makes Unit 27's four-line proof independent of the size of the frame |
| `x50` | `not_heapOnly_pure` | C | 4 | where the free route stops. The reader knows in advance which framing obligations will be free and which need work, and Unit 29's `StoreStable` is motivated before it appears |
| `x51` | the store counterexample, as a refutation | **G** | 4 | *design*: "state, as a Lean proposition, the claim that framing an assignment with a store fact is sound — and refute it." **`Preserves` is earned, not asserted** |

**Hook.** "Two definitions, both justified, and neither yet proved of a single command. Locality is
a claim about `Exec`, and `Exec` has ten constructors. Three of them do not touch the heap and are
done. The two that do are where the argument has content, and each is a `funext` over a union."

**Size.** ~5 screens, ~30 blocks: 1 `svg` of the commuting square, 1 `code` of `HeapLocalWeak` and
1 of `HeapLocal` with the difference called out, 1 `state` of the goal that cannot be closed,
1 `cmp` (syntactic versus semantic side condition), 1 `note kind:warn` on the missing conjunct in
the original syllabus, 2 `detail`.

---

### Unit 25 · `local-heap` · Locality of `write` and `free`
**file** `site/content/28-local-heap.js`

**One job.** The two hardest pointwise heap arguments in the corpus, done slowly — and the last
time in the course that the reader does pointwise heap reasoning at all.

**Inherits.** Unit 24's promise.

**Objectives.**
1. Decompose each proof into its two named obligations before writing any Lean: the **disjointness
   half** and the **heap-equation half**.
2. Prove that writing preserves disjointness, using `h l = some old` to force `hFrame l = none`.
3. Prove `write (h ∪ hFrame) l v = (write h l v) ∪ hFrame` by `funext` plus a split on `x = l`, and
   observe that **the heap equation needs no hypothesis at all** — `write_union_no_disjointness`
   proves it with none.
4. Do the same for `free`, and identify the single goal — `none = hFrame x` — that *is* the
   theorem, where disjointness is genuinely load-bearing rather than bookkeeping.
5. Use `have hl' : h l = _ := hl` and say why it is needed: `hl` is stated about `⟨σ, h⟩.heap` and
   `rw` will not see through the projection. Use `show` on a heap equation to name the obligation
   before proving it, and `hwx.trans hx` to compose two equations as a term inside a `rw`.
6. Say what would go wrong if the frame were allowed to own the freed location.

**New Lean.** `have h' : T := e` as a **definitional restatement** — asserting the type you want
and proving it with a term whose type is definitionally equal; `.trans` / `Eq.trans` in dot
notation; `show` on a heap equation.

**New mathematics / SL.** The distinction, made sharply and returned to, between a hypothesis that
keeps *bookkeeping* honest and a hypothesis the *equation* depends on. For `write`, disjointness is
needed only for the domain conjunct; for `free`, it is needed for the equation. That asymmetry is
the mathematical content of the unit and is stated as a `steps` block stripped of all Lean before
any Lean appears.

**Corpus.** `heapLocal_write` (`m8-2`), `heapLocal_free` (`m8-3`).

**New Lean needed** — ✔ `new-m8.lean`: `write_union_no_disjointness`.

**Exercises (2, both corpus).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m8-2` | `heapLocal_write` | C | 4 | the first case with content; disjointness as *bookkeeping*. **Variants:** delete `hd` and exactly one thing breaks — the domain conjunct; the equation survives, as `write_union_no_disjointness` proves with no hypothesis at all |
| `m8-3` | `heapLocal_free` | C | 4 | **the case where the two heaps genuinely meet.** The reader reaches `none = hFrame x` and recognises it as the whole theorem. **Variants:** let the frame own `l` too and locality is *false* — with `h = singleton 0 7`, `hFrame = singleton 0 99`, the small run leaves the frame's 99 visible at 0 and the big run leaves `none` |

Each exercise offers the reader the option of proving the two obligations as separate `have`s
before assembling. That decomposition is the unit's main teaching device.

**The eight-line rule applies hardest here.** Edition 1's `trace` blocks in this chapter run to
twelve lines of
`{ store := { store := σ, heap := h }.store, heap := … }.heap` projection noise. See §H.2: any goal
state longer than eight lines goes in a foldable `detail`, and the main-line `trace` shows a real
state obtained after a `show` that appears in the displayed tactic sequence.

**Hook.** "Five commands are local. A program is not five commands — it is commands glued together
with `;;`, and two of the ten constructors are control flow that Edition 1 never proved local at
all."

**Size.** ~3 screens of prose, ~24 blocks plus 2 `ex`: 1 `steps` of the mathematics stripped of
Lean, 4 `trace` (two per obligation), 2 `detail` holding the long raw states.

---

### Unit 26 · `local-compose` · Locality composes
**file** `site/content/29-local-compose.js`

**One job.** Prove locality is closed under sequencing, conditionals and loops, so that the frame
rule applies to whole programs rather than single commands.

**Inherits.** Unit 25's closing observation.

**Objectives.**
1. Prove `heapLocal_seq` and see exactly where Unit 24's extra disjointness conjunct is spent — it
   comes out of the first application and goes into the second.
2. Use `rename_i` to name a variable Lean introduced inaccessibly, under real pressure.
3. Close the gap between `Exec c₂ ⟨sMid.store, sMid.heap ∪ hFrame⟩ r₂` and `Exec c₂ r₁ r₂` with a
   structure-eta `have`.
4. Prove `heapLocal_ite` by inversion and two applications of the hypothesis, noting that the guard
   transfers unchanged because `b.eval` reads only the store.
5. Prove `heapLocal_loop` by induction on the derivation, using the **constant-command idiom**:
   generalise the command, carry the hypothesis `cmd = .loop b c`, induct, and kill the eight
   impossible cases with `intro heq; cases heq`.
6. State the conclusion: **every command in this language is local**, so adding a command tomorrow
   extends the frame rule with no further thought.

**New Lean.** `rename_i` in earnest (introduced Unit 19); the **constant-command / index-equation
induction idiom** (`∀ {cmd}, Exec cmd s s' → cmd = … → …`) and `cases heq` closing a branch by
constructor no-confusion. The idiom is introduced here and is compulsory again in Unit 36 —
Unit 36's author must be able to say "this is the manoeuvre from Unit 26".

Also here: the failure that motivates the idiom — `induction hex` directly on
`Exec (.loop b c) s s'` fails with *Invalid target: Index in target's type is not a variable*.
Show the error.

**New mathematics / SL.** Compositional locality.

**Corpus.** `heapLocal_seq` (`m8-4`).

**New Lean needed** — ✔ `new-m8.lean`: `heapLocal_ite`, `heapLocal_loop_aux`, `heapLocal_loop`.

**This is where Edition 2 goes beyond Edition 1.** Edition 1 proves locality for `skip`, `assign`,
`load`, `write`, `free` and `seq` and stops, so its frame rule cannot be applied to any program
containing a conditional or a loop — that is, to any interesting program. The gap is invisible only
because M9's examples are loop-free and M13's loop example touches no heap. Edition 2 closes it,
and the closing is what makes Unit 37's `drain_spec` possible.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m8-4` | `heapLocal_seq` | C | 3 | composition; `rename_i`; the structure-eta gap. **Pitfall:** `obtain ⟨sMid, hex₁, hex₂⟩ := hex` *silently* drops all three names — they collide with `Exec.seq`'s own field names — and the error arrives at the next line as `Unknown identifier` |
| `x52` | `heapLocal_ite` | D | 2 | inversion into two branches, each a direct application. Deliberately easy, to make the loop case look approachable, and it lets the reader complete the loop-free language themselves |
| `x53` | `heapLocal_loop` | C | 4 | **the constant-command induction idiom**; the course's second induction over a derivation, and a preview of Unit 36 where the same manoeuvre is compulsory |

**Hook.** "Every command is local. That is a fact about the language. Turning it into a fact about
triples is one theorem, eight lines, and every one of them is a step of the informal argument."

**Size.** ~4 screens, ~26 blocks: 1 `state` of the `Invalid target` error, 1 `steps` of the
constant-command idiom in words, 2 `trace`.

---

### Unit 27 · `frame` · The frame rule
**file** `site/content/30-frame.js`

**One job.** Prove `hoare_frame`, and demonstrate that the length of a verification does not grow
with the size of the frame.

**Inherits.** Unit 26 proved locality of every command; Unit 24 defined `Preserves`; Unit 23 left a
two-command program proved the hard way.

**Objectives.**
1. Prove `hoare_frame` in five moves — split the initial heap, run `c` small, lift with locality,
   reassemble `Q ∗ R`, re-establish `R` with `Preserves` — and map each of its eight lines onto one
   of them.
2. Identify the only decision in the proof — the cut in the *postcondition* — and observe that
   `HeapLocal`'s conclusion was stated so that both heap obligations arrive in exactly the form `∗`
   demands.
3. Say what the proof does **not** contain: no induction on `c`, no case analysis on `Exec`, no
   lemma about `∗`, no determinism, no finiteness. `hoare_frame` is a fact about *any* relation
   satisfying the two conditions. It never uses the initial disjointness directly — it only passes
   it to `hlocal`, and that is precisely the modularity being bought.
4. Apply the frame rule to obtain a two-cell specification in five lines, none of which mentions a
   heap — then replace the frame by a ten-thousand-node linked list and observe that **not one
   character changes**.
5. Explain where `l ≠ other` comes from in that specification: it is never a hypothesis, because
   `two_cells_distinct` extracts it from the precondition.
6. Say precisely which language features would make the rule false.

**New Lean.** None. The lesson is that the proof is *entirely* composition of things already
proved, and the unit makes the reader check that: every line of `hoare_frame` is an application of
a lemma from Unit 10, Unit 24, Unit 25 or Unit 26.

**Corpus.** `hoare_frame` (`m8-5`), `write_with_frame` (`m8-6`).

**New Lean needed** — ✔ `new-m8.lean`: `free_with_frame`.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m8-5` | `hoare_frame` | C | 4 | **the theorem the course exists to prove.** **Pitfall:** forgetting `subst hu` — the goal keeps saying `heap := h` while `hrex` says `heap := hP.union hR`, and Lean reports it from inside `And.intro`. **Variants:** drop `hpres` and the second hole is refuted by Unit 24's counterexample; drop `hlocal` and you cannot start; weaken to `HeapLocalWeak` and the fifth component has nothing to fill it |
| `m8-6` | `write_with_frame` | D | 2 | five lines, none mentioning a heap; the contrast with the proof above is the lesson. **Pitfall:** the missing leading `_` in `preserves_of_heapOnly _ (…)`, whose error reads as though something were wrong with `heapOnly_pointsTo` |
| `x54` | `free_with_frame` | C | 3 | the same lift with a different rule, and the postcondition needs tidying with `star_emp_left` — **the first time Unit 15's unit law earns its keep in a program proof** |

**Retrospective.** (i) Which of the two side conditions failed in the store counterexample and
which in the heap counterexample? (ii) Why does `HeapLocal` carry a disjointness conjunct?
(iii) Give a command for which `HeapLocal` is false.

**Hook.** "The rule is proved. There is one debt outstanding, issued on the first page: the
statement we could not write down then, and can now."

**Size.** ~4 screens, ~26 blocks: 1 `steps` (the five moves), 2 `trace`, 1 `cmp` (with and without
the frame rule), 1 `note kind:key` on what the proof does not contain, 1 `note kind:warn` pointing
at Unit 38 for allocation.

---

### Unit 28 · `aliasing-closed` · The opening question, closed
**file** `site/content/31-aliasing-closed.js`

**One job.** Discharge the promissory note issued in Unit 00, with two machine-checked theorems,
and state in one page what the course has established.

**Inherits.** Unit 00's named-but-unproved theorem, carried unpaid for twenty-eight units, and Unit
27's frame rule, which is what makes the second half of the pair short.

**Objectives.**
1. Write the classical conjunction rule for pointer writes as a Lean statement about `Hoare`, using
   the loose points-to from Unit 07.
2. **Refute it**, by instantiating both locations at 0 and reading the contradiction off the final
   heap.
3. State the corresponding specification with `∗` in place of `∧`, and **prove it in four lines**
   by framing.
4. Articulate the difference in one sentence: the classical rule needs a side condition it cannot
   name; the separating rule needs none, because the precondition already contains it.
5. Say what has and has not been achieved — no allocation, no concurrency, no pointer dereference
   through a variable — and where each is addressed.

**New Lean.** None.

**New mathematics / SL.** Nothing new. **This is the unit that has no new content and is
nonetheless indispensable**, because a course that opens with a question and never visibly answers
it has not told a story. Its content is the *comparison*: nine lines of refutation beside four
lines of proof, with every ingredient of both proved by the reader.

**Corpus.** None — but it cites `hoare_write`, `heapLocal_write`, `preserves_of_heapOnly`,
`heapOnly_pointsTo`, `hoare_frame` and `two_cells_distinct` by name, which is the point.

**New Lean needed** — ✔ `new-m8.lean`: `ptsAtLeast`, `classical_conjunction_rule_is_false`,
`separated_write_ok`.

**Exercises (2).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x55` | `classical_conjunction_rule_is_false` | C | 4 | **the opening question, refuted** — inside the real logic, with the real semantics. The reader has now *proved* the thing they were told on page one |
| `x56` | `separated_write_ok` | D | 1 | **the same specification with `∗`, proved by framing, in four lines.** The contrast is the lesson, and the low difficulty is deliberate: a reader who has just done something hard should immediately be shown what it bought |

**Hook.** "The logic is sound and its central rule is proved. It is not yet a *method*: every
verification so far has been two commands long, and each needed hand-chosen intermediate assertions
and a chain of renormalisation. Making that routine is the next module."

**Size.** ~3 screens, ~18 blocks — the shortest non-lab unit in the course, and budgeted that way
on purpose: 2 `ex`, 1 `cmp` side-by-side of the two theorems, 1 `tbl` of what is and is not
established, 1 `dod`.

---

## D.7 Module 7 · Verification as calculation

---

### Unit 29 · `symbolic` · Symbolic execution
**file** `site/content/32-symbolic.js` · **phase** `Phase 6 · Verification`

**One job.** Establish the working style — split, frame, apply, renormalise — supply the glue
lemmas that make it bearable, and verify two real programs with `Exec` appearing nowhere.

**Inherits.** Unit 28's method-shaped gap, and Unit 23's `readAndFree_spec`, still proved the hard
way.

**Objectives.**
1. State the four-move loop — `hoare_seq`, `hoare_frame`, a small rule, `hoare_consequence` — and
   apply it without unfolding `Exec`. **The rule the reader is held to: if `Exec` appears in one of
   your proofs, you are missing a lemma.**
2. Prove `StoreStable` for `write` and `free` and derive `Preserves` for **every** assertion from
   it — the route Unit 24 said would be needed once `HeapOnly` ran out. Say why it is stronger than
   `HeapOnly` and when each is the right tool.
3. Redo `readAndFree` in four structural rules and no semantics, and measure the difference against
   the proof you wrote by hand six units ago.
4. Use `hoare_write_val` and say why the store-dependent postcondition of `hoare_write` needed
   replacing.
5. Move a pure fact across a `∗` with `pure_star_regroup`; recognise a renormalisation chain and
   shorten it by choosing a better small rule.
6. Choose an intermediate assertion by working out what the *next* command's footprint needs, and
   articulate that this is the *only* creative act — everything else is mechanical.
7. Regroup a `;;` when the specification you want to reuse has the other bracketing.

**New Lean.** No new tactic. New habit: writing `have step : Hoare … := …` to name a framed triple
before consuming it. New skill: reading `refine hoare_consequence (entails_refl _) step ?_` and
knowing that the remaining hole is a pure `∗`-reshaping, then discharging it with an
`entails_trans` chain from Unit 17's toolkit.

**New mathematics / SL.** **Symbolic execution** as a discipline. Store-stability as a strictly
stronger and much cheaper alternative to heap-onlyness. **The idea that a specification's *shape*
determines how painful it is to compose** — which is the motivation for the new load rule below.

**Corpus.** `StoreStable`, `storeStable_write`, `storeStable_free`, `preserves_of_storeStable`,
`hoare_write_val`, `pure_star_regroup`, `copyCell`; `copyCell_spec` (`m9-1`), `exec_seq_assoc`
(`m9-2`), `moveCell`, `moveCell_spec` (`m9-3`).

**New Lean needed** — ✔ `new-m9.lean`: `hoare_load_and`, `and_fact_star`, `and_fact_star_intro`.
Plus, retained from Edition 1 as an `illustration`: `readAndFree_framed`.

**Why the second load rule exists, and why it is presented as a design decision.** Edition 1's
`hoare_load` has postcondition `pure (fun σ => σ x = v) ∗ (l ↦ v)`, which forces a three-step
`entails_trans` chain — `star_assoc_left`, then `star_mono_right _ (star_comm …)`, then
`pure_star_regroup` — before *every* subsequent write. That chain is pure bookkeeping, it is the
bulk of `copyCell_spec`, and it is why `swap_spec` shipped unfinished. Edition 2 teaches **both**
rules and says why each exists: the `pure ∗` form because it is the standard textbook statement and
the cleanest demonstration that `pure` pairs with `∗`; the `aAnd` form because it is what you
calculate with. That is a design decision presented *as* a design decision, with the cost of each
alternative named — exactly the discipline `PEDAGOGY.md` demands and that Edition 1 applies to
`Heap.union` but not to its own rules.

**Exercises (6).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x57` | `storeStable_write`, `storeStable_free`, `preserves_of_storeStable` | D | 2 | promoted from `code`; two-line inversions; the second `Preserves` discharger, needed for every write in this module |
| `x58` | `readAndFree_framed` | D | 2 | **redo Unit 23's defeat in four structural rules.** The promise made in Unit 23 is kept, and the reader can measure the difference against a proof they wrote by hand. The single best before/after in the course |
| `x59` | `pure_star_regroup` | C | 3 | promoted from `code`; the bookkeeping entailment; the reader must find `union_empty_left` inside a two-level destructuring |
| `x60` | `hoare_load_and` and `and_fact_star` | C | 3 | the composable load rule; **a rule's shape is a design choice with a measurable cost** |
| `m9-1` | `copyCell_spec` | C | 4 | **the first genuinely compositional verification.** The four-move loop, twice, with two *different* `Preserves` helpers — heap-only for the load, store-stable for the write — and the unit points at that difference. At no point does the proof mention a heap, a union or a disjointness |
| `m9-2` + `m9-3` | `exec_seq_assoc`, `moveCell_spec` | C | 3 | sequencing is associative semantically and not syntactically — a trap that costs ten minutes if unwarned. `moveCell_spec` is four lines, entirely by composition, ending in `star_emp_left`; the postcondition owns strictly less than the precondition, and the logic tracked the deallocation |

**Hook.** "Two programs, both two commands long, and one of them took a page. A four-command
program will need four intermediate assertions, all chosen by hand — and the only thing you have
not seen is what happens when a *load* has to preserve a fact about a different variable."

**Size.** ~5 screens, ~34 blocks: 1 `txt` of the four-move recipe, 1 `ol` of the `copyCell` plan in
words before any Lean, 3 `trace`, 1 `cmp` of the two load rules, 1 `note kind:info` (the `;;`
associativity trap).

---

### Unit 30 · `swap` · LAB/capstone — swap
**file** `site/content/33-swap.js` · **LAB / CAPSTONE**

**One job.** Verify a four-command program with two temporaries, staged into rungs, as the test of
whether the method has been learned — and, honestly, show the reader the moment when dropping to
the semantics is the right engineering call rather than a failure.

**Inherits.** Unit 29's four-move loop and both load rules.

**Format.** Capstone lab. Differs from the earlier labs:
1. the specification is stated and the reader is asked to **predict the four intermediate
   assertions before seeing any Lean** — they are given outright as hint rung 1;
2. the rungs are separate exercises, each with its own hint ladder;
3. a `cmp` block shows **the same theorem two ways** — the compositional skeleton and the verified
   direct semantic proof — with a paragraph on how to choose.

**Objectives.**
1. Decompose a four-command program into `hoare_seq` steps and write down the intermediate
   assertions before touching Lean.
2. Carry a pure fact past a command that writes a *different* program variable, and prove the
   `Preserves` obligation that requires — including where the hypothesis `tmp₁ ≠ tmp₂` is consumed.
   **This is the store-side analogue of heap disjointness**, and the unit says so.
3. Explain why no hypothesis `l₁ ≠ l₂` is needed: the precondition supplies it via
   `singleton_disjoint_iff` / `two_cells_distinct`.
4. Isolate the heap computation as its own lemma (`swap_heap`) before touching the triple.
5. State the rule for choosing between the two routes: **compose while the footprints are disjoint
   and the reshaping is mechanical; drop to the semantics when the program's effect on the whole
   heap is easier to state than the sequence of reshapings.**

**New Lean.** None. This is a lab and its job is to prove the reader can work unaided.

**Corpus.** `preserves_load_fact` (`m9-4`) — the only part Edition 1 proves.

**New Lean needed** — ✔ `new-m13.lean`: `swap`, `swap_heap`, `swap_spec`.

**This closes the one genuinely open exercise in Edition 1.** Edition 1's `m9-4` has a `goal` field
that is a commented-out signature and a `sol` field containing `preserves_load_fact` plus a
*comment* listing the four remaining `hoare_seq` applications. It is the one exercise in the course
with no verified solution, and `README.md`'s claim of 75 checked solutions is therefore 74 plus a
helper. The verified proof supplied here takes the direct semantic route: destructure the
precondition, extract `l₁ ≠ l₂` from `singleton_disjoint_iff`, prove the heap computation as a
separate lemma, and build the four-step `Exec` derivation explicitly. It is thirty lines and
introduces **no new syntax**.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m9-4` | `preserves_load_fact` | C | 3 | the one genuinely new ingredient, and the place `tmp₁ ≠ tmp₂` is consumed |
| `x61` | `swap_heap` | C | 4 | the heap computation alone, isolated — three regions over a union; a rung the reader can stand on |
| `x62` | `swap_spec` | C | 5 | **the capstone.** Four commands, two temporaries; `l₁ ≠ l₂` never hypothesised |

**Retrospective.** (i) Where did `l₁ ≠ l₂` come from? (ii) Which `Preserves` discharger did each
command need, and why did they differ? (iii) What would change if the program had five commands
instead of four? *(Answer: one more rung, nothing else — and that invariance is the practical
argument for the whole subject.)*

**Hook.** "Four intermediate assertions, all chosen by hand and all forced by what the *next*
command needed. That is a strong hint they can be computed backwards from the postcondition — and
they can."

**Size.** ~2 screens of prose, ~20 blocks plus 3 `ex`: 1 `ol` of the four assertions, 2 `trace` on
`swap_heap`, 1 `steps` for the compositional skeleton, 1 `cmp` (compositional versus direct).

---

### Unit 31 · `wp` · Weakest preconditions
**file** `site/content/34-wp.js`

**One job.** Define `wp`, show that `Hoare P c Q` and `P ⊢ wp c Q` are *the same proposition*, and
prove the equations that turn a definition into a calculus.

**Inherits.** Unit 30's hand-chosen intermediate assertions, each forced by the next command.

**Objectives.**
1. Define `wp c Q` as the set of states from which `c` runs safely into `Q`, and say why it is
   *weakest* — the largest such precondition, and every valid one entails it.
2. Prove `hoare_iff_entails_wp` **by `Iff.rfl`**, and explain exactly what that means: not a
   theorem relating two things, an observation that there is one thing. The two propositions are
   the *same term* after unfolding.
3. Prove `wp_sound` and `wp_weakest`, making "weakest" a pair of theorems instead of a gloss.
4. Compute `wp` for `skip`, `assign` and `seq`, each by the same two moves — forwards, invert the
   derivation; backwards, build one — and read `wp_seq` as the rule that makes backward reasoning
   work: verifying straight-line code becomes a fold from the end.
5. **Compute** `wp` for `free` and `write` against a given postcondition, and observe that what
   comes out is the small-footprint precondition with the irrelevant data existentially
   quantified — the formal content of "the value does not matter". Prove `heap_eq_singleton`
   separately, because it is the mathematical core and should not be hidden inside the wp proof.
6. Judge whether a precondition you wrote is genuinely the weakest one, and name the commonest way
   it is not: pinning down a value the program never reads.
7. Transport the frame rule to `wp` in one line, because the two statements are the same statement.

**New Lean.** `Iff.rfl`; `rfl` at `Prop`; `⊣⊢` goals proved by `constructor` and two `intro`s;
`rename_i old` after `cases` inside a `wp` proof (`rename_i` itself is Unit 19).

**New mathematics / SL.** **Predicate transformers.** Weakest precondition; forwards versus
backwards reasoning, and why every practical verification tool is built on `wp`. The greatest
element of `{P | Hoare P c Q}` in the entailment preorder, unique up to `⊣⊢`. The angelic reading
of `wp` versus the demonic one, and the note that `wp_seq` needs no determinism either way.
Weakest versus merely sufficient.

**Corpus.** `wp`; `hoare_iff_entails_wp`; `wp_skip`/`wp_assign` (`m12-1`), `wp_seq` (`m12-2`),
`wp_mono` (`m12-3`), `heap_eq_singleton`, `wp_free_emp` (`m12-4`), `wp_write` (`m12-5`).

**New Lean needed** — ✔ `new-m12.lean`: `wp_sound`, `wp_weakest`, `wp_frame`.

`wp_frame` is a one-line term proof — `hoare_frame (fun _ _ hp => hp) hlocal hpres` — and it is the
single best demonstration in the course that `Hoare` and `⊢ wp` are the same thing. Edition 1 does
not have it.

**Exercises (6).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m12-1` | `wp_skip` / `wp_assign` | C | 2 | first `⊣⊢`; the semantic `subst` now looks obviously right rather than clever |
| `m12-2` | `wp_seq` | C | 3 | **the rule that makes backwards reasoning work**; the fold from the end |
| `m12-3` | `wp_mono` | D | 2 | `wp c` is a monotone transformer |
| `x63` | `wp_sound` and `wp_weakest` | D | 1 | the two halves of the word "weakest"; the reader can now *state* optimality, not just feel it |
| `m12-4` + `m12-5` | `wp_free_emp`, `wp_write` (with `heap_eq_singleton` proved first) | C | 4 | `wp` **computed**, not postulated; the existential over the irrelevant value. `variants` asks whether `src ↦ a ∗ dst ↦ b` is the weakest precondition of `copyCell` — it is not, because `b` is never read |
| `x64` | `wp_frame` | D | 1 | one line, and the reader must explain why it typechecks. **The punchline of the unit** |

**Hook.** "Every assertion so far describes a *bounded* number of cells. A linked list does not, and
no finite combination of `↦` and `∗` can describe one."

**Size.** ~5 screens, ~32 blocks: 1 `defn` card (weakest precondition), 1 `cmp` (forwards versus
backwards), 2 `trace`, 1 `note kind:key` on `Iff.rfl`, 1 `detail` (unfolding by hand, and where the
same proof fails for `PartialHoare`, with the real error message).

---

## D.8 Module 8 · Unbounded structures and the wand

---

### Unit 32 · `listrep` · Lists in the heap
**file** `site/content/35-listrep.js` · **phase** `Phase 7 · Unbounded structures`

**One job.** Define a recursive assertion, and make the reader see that it says *shape* and
*ownership* in one breath.

**Inherits.** Unit 31's closing observation that every assertion so far is bounded.

**Objectives.**
1. Define an `Assertion`-valued function by structural recursion on a `List`, read the `cons` case
   as an existential over the next pointer, and unfold `listRep [10,20,30] p` in words.
2. Say what the `∗`s guarantee — six *different* cells, so the list cannot secretly be a lasso —
   and what the `pure` conjuncts guarantee (non-nullness).
3. State the fold/unfold interface, all three lemmas `entails_refl _`, and say why naming three
   identities is hygiene rather than pedantry: later proofs cite a lemma instead of relying on how
   the equation compiler happened to unfold a definition, so if the definition changes only these
   three break.
4. Derive `p ≠ p + 1` **from ownership rather than from arithmetic**, as one instance of
   `two_cells_distinct` — and observe that the proof never mentions that this is a fact about
   numbers, so in a model with abstract locations it would still work.
5. Assemble a concrete three-node list from three `node` assertions, choosing five cuts by hand and
   `subst`ing the heap equations first.
6. Say why this unit contains no `Cmd`, no `Exec` and no triple — and why: Unit 18's decision to
   give `load` a literal location means no program in this course can walk one of these structures.
   That is a stated limitation, discharged in Unit 38, not an accident.

**New Lean.** Recursive `def` returning an `Assertion`, with pattern matching on a `List`;
`List Nat`, `[]`, `::`, `[a, b, c]` literal syntax; definitional unfolding of a recursive
definition at a constructor pattern. (Induction on a `List` was introduced in Unit 20 and is first
*used* in Unit 33.)

**New mathematics / SL.** **Recursive predicates**, presented as a structurally recursive
definition, with a foldable aside on why this is a *least fixed point* and what would go wrong with
a non-structural recursion. The **double reading** (shape + ownership) as the key idea, and its
consequence: unfolding one gives you non-aliasing for free, and you can hand an entire data
structure to a subroutine by handing over one assertion. Null as location 0, stated as the
modelling convention it is.

**Corpus.** `node`, `listRep`; `listRep_nil`/`listRep_cons_unfold`/`listRep_cons_fold` (`m10-1`),
`node_cells_distinct` (`m10-2`), `concrete_list` (`m10-3`).

**New Lean needed** — ✔ `new-m10.lean`: `listRep_cons_ne_zero`.

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m10-1` | the three fold/unfold lemmas | D | 1 | why `entails_refl _` suffices, and why you name them anyway |
| `x65` | `listRep_cons_ne_zero` | D | 2 | pure information falls out of a recursive predicate |
| `m10-2` | `node_cells_distinct` | D | 1 | one line; non-aliasing from ownership, not arithmetic; the promise made in Unit 17, kept |
| `m10-3` | `concrete_list` | C | 4 | five layers of witness-then-recurse; the rhythm *witness the existential, split off `Heap.empty` for the `pure`, hand the node its heap, recurse*. **Pitfall:** normalise the hypotheses with `subst` first, or every heap equation becomes a fight with `union_assoc` |

**Hook.** "A predicate for a *complete* list. A traversal splits a list into the part already
visited and the part remaining, and neither of those is a complete list."

**Size.** ~4 screens, ~26 blocks: 1 `svg` (three nodes, six cells, the arrows), 1 `anat` on the
`cons` case, 1 `note kind:key` on the double reading, 1 `detail` on least fixed points.

---

### Unit 33 · `lseg` · LAB — segments and append
**file** `site/content/36-lseg.js` · **LAB**

**One job.** Define segments, prove the classical theorem of the subject by an induction carried
out **entirely in the assertion algebra**, and use the theorem one cannot prove to diagnose a wrong
definition.

**Inherits.** Unit 32's complete-list predicate, which cannot describe a partial traversal.

**Worked example.** The `cons` case of `lseg_append`, read as a chain: pull the `∃` out of the star
with `star_exists_left`, work under the binder with `aExists_mono`, reassociate twice with
`star_assoc_left`, apply the induction hypothesis under `star_mono_right`. **Five lines, five named
Module 3 lemmas, no heap variable, no union, no disjointness** — and the lab names each one. *If
you built the normalisation library in Units 15–17, you are collecting the dividend now.*

**Objectives.**
1. Define `lseg xs start finish` and say what a segment is: the part of a list from `start` up to
   but not including `finish`.
2. Prove `aExists_mono` and use it to work under an existential binder.
3. Prove `lseg_append`, with the cons case done entirely in the algebra.
4. Prove `lseg_listRep`, and recognise that its structural identity with `lseg_append` is evidence
   the definitions are aligned.
5. **Diagnose a wrong definition from the theorem you cannot prove.** With `start ≠ finish` in the
   cons case, `lseg_append` is not provable — after appending you hold `p ≠ q` and the goal wants
   `p ≠ r`, and nothing connects them. The condition must be `start ≠ 0`.
6. Contrast induction *on data* with Unit 20's induction on a *derivation*.

**New Lean.** `induction xs with | nil | cons x xs ih` in earnest (introduced Unit 20); `++` on
`List`. Nothing else — and the lab says so as its own evidence: *the hardest theorem in the second
half introduces no syntax, because by now the algebra does the work.*

**New mathematics / SL.** **List segments** as the raw material of traversal invariants — "already
visited" and "still to visit". Induction over data with the inductive step performed in an algebra
rather than in the model. **A definition debugged by a failed proof**, presented at length, because
"the obvious definition was subtly wrong and the theorem you could not prove is what told you" is
one of the most valuable experiences formalisation offers — and Edition 1 tells this story well and
is retained.

**Corpus.** `lseg`; `aExists_mono`, `lseg_append` (`m10-4`), `lseg_listRep` (`m10-5`).

**New Lean needed** — ✔ `new-m10.lean`: `lseg_nil_iff`, `listRep_null`.

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x66` | `aExists_mono` and `lseg_nil_iff` | D | 2 | work under a binder — the second line of both main proofs — and the empty-segment interface |
| `m10-4` | `lseg_append` | C | 4 | **the classical theorem of the subject.** Two adjacent segments make one; every list-traversal loop invariant is maintained by an application of it |
| `m10-5` | `lseg_listRep` | C | 3 | a segment followed by a complete list is a complete list — the lemma that closes a traversal. Structurally identical to the previous, which is the *sign* the definitions are aligned. **Variants:** this is the proof that fails first under the wrong `lseg`, and the lab shows where |
| `x67` | `listRep_null` | **G** | 3 | *design*: "state and prove that a list at the null pointer is the empty list." The reader must discover that the `cons` case dies on its own `pure` conjunct |

**Retrospective.** (i) Why is the `nil` case of `lseg_append` the only one that touches heaps?
(ii) What would have failed first if `lseg` had used `start ≠ finish`? (iii) Name the five algebra
lemmas the `cons` case used, in order.

**Hook.** "`lseg` describes a list with its tail removed — a structure with a hole, where the hole
is described by another assertion. *I have given away part of my data structure, and here is how to
put it back* is a pattern that recurs constantly, and it has a connective of its own."

**Size.** ~2 screens of prose, ~22 blocks plus 4 `ex`: the worked example, 1 `svg` of a segment,
1 `note kind:warn` on the definitional bug, 2 `trace`.

---

### Unit 34 · `wand` · The magic wand
**file** `site/content/37-wand.js`

**One job.** Define `-∗` as the answer to a question the reader now has, prove it right adjoint to
`∗`, and cash the adjunction out as the algebra of a structure with a hole.

**Inherits.** Unit 33's structure-with-a-hole pattern, and Unit 14's observation that no rule takes
`P ∗ Q ⊢ R` to `P ⊢ R` — nothing anti-monotone exists yet.

**Objectives.**
1. Read `wand P Q σ h := ∀ h', disjoint h h' → P σ h' → Q σ (union h h')` aloud: *I hold a resource
   such that, given a separate heap satisfying `P`, the combination satisfies `Q`.*
2. State the currying adjunction for `∧` and `→` — a fact the reader already knows — then the same
   with `∗` and `-∗`, and see that the definition of `wand` was chosen to make it hold.
3. Prove `wand_intro` and `wand_elim`, recognise them as currying and uncurrying, and note that
   `wand_elim` is modus ponens for resources — the wand and its argument must be in *disjoint*
   heaps, so you cannot apply a wand to memory you have already spent.
4. Prove the adjunction `(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)` **from the two previous lemmas** rather than
   from the model — the reader sees that having named the halves makes the whole free.
5. Prove the variance of `-∗` — contravariant left, covariant right — by reading it off the
   definition rather than memorising it.
6. Say why a wand is a promise that **consumes** resources and can be used once, whereas ordinary
   implication can be used any number of times because assumptions are free.
7. Build and cash a "structure with a hole" in two one-line proofs.

**New Lean.** `infixr:54 " -∗ " => wand` and why the wand binds looser than `∗`. New reading skill:
a `∀` inside an assertion, and the discipline of introducing `h'`, `hd`, `hp` in the right order.

**New mathematics / SL.** **Adjunction**, introduced from currying, not from category theory:
`P ∧ Q → R` iff `P → (Q → R)` is already known, and `-∗` is *defined so that the same holds with
`∗`*. `wand_elim` as the counit. Contravariance. The remark that `(∗, emp, -∗)` makes assertions a
closed symmetric monoidal category — a **BI algebra** — offered as a foldable aside with the
translation supplied, never as assumed vocabulary. The practical pattern: what remains after
handing out one node of a list is `node p x n -∗ listRep xs p`.

**Corpus.** `wand`; `wand_intro` (`m11-1`), `wand_elim` (`m11-2`), `star_wand_adjunction`
(`m11-3`), `wand_mono` (`m11-4`).

**New Lean needed** — ✔ `new-m11.lean`: `wand_unit`, `wand_curry`, `wand_uncurry`, `hole_intro`,
`hole_elim`, `emp_wand_elim`, `emp_wand_intro`.

Edition 1's M11 is the thinnest chapter in the course: four exercises, all mechanical, and no
example that makes the reader *want* a wand. `hole_intro` and `hole_elim` are each **one line built
from lemmas already proved**, and they are the shape every real use of the wand takes.

**Exercises (6).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m11-1` | `wand_intro` | C | 2 | currying; the cleanest instance of "choose the cut" — the heap equation is `rfl` because the wand's definition put the union there |
| `m11-2` | `wand_elim` | C | 2 | cashing a promise; modus ponens for resources |
| `m11-3` | `star_wand_adjunction` | C | 2 | **the adjunction**, with the ⟸ direction proved from the two previous lemmas |
| `m11-4` | `wand_mono` | D | 2 | variance, read off the definition |
| `x68` | `wand_unit`, `hole_intro`, `hole_elim` | C | 2 | **the practical pattern**: hand out a piece, keep the promise, cash it in — in two one-line proofs |
| `x69` | `wand_curry` / `wand_uncurry` | C | 3 | the resource-sensitive currying isomorphism; the sharpest statement of what the adjunction buys. Uses `disjoint_union_left/right` in both directions |

`emp_wand_elim`/`emp_wand_intro` are offered inside `x68`'s `variants` as a design question — *what
is `emp -∗ P`?* — with the answer verified.

**Hook.** "The assertion language is complete: `emp`, `↦`, `∗`, `-∗`, the classical connectives,
recursion. The *language* is not — `ite` and `loop` have sat in `Cmd` since Unit 18 and have never
been used, and the moment they are, a distinction that has been invisible becomes essential."

**Size.** ~4 screens, ~28 blocks: 1 `svg`, 1 `txt` of the two currying rules side by side, 1 `note
kind:key` on the right adjoint, 1 `note kind:info` on where wands appear in practice, 1 `detail`
on BI algebras.

---

## D.9 Module 9 · Control and termination

---

### Unit 35 · `partial` · Partial correctness, and conditionals
**file** `site/content/38-partial.js` · **phase** `Phase 8 · Control and termination`

**One job.** Make the partial/total distinction real, and prove the conditional rules, so that
Unit 36 can be about one thing only.

**Inherits.** Unit 34's observation that `ite` and `loop` are unused, and Unit 22's `PartialHoare`,
defined for contrast and never used since. This unit says why the wait was correct: for the
loop-free fragment the two readings coincide.

**Objectives.**
1. State both readings side by side and say which quantifier moved.
2. Prove `partial_of_total` and identify the one ingredient it needs — determinism, from Unit 20 —
   and say why the implication only runs one way.
3. Prove the partial structural rules, and articulate the contrast with Unit 22: **in the total
   version you *build* an execution; in the partial version you are *given* one and take it apart.**
4. Lift guards into assertions with `bTrue` / `bFalse`, and predict the shape of a guard hypothesis.
5. Prove the partial conditional rule, where inversion hands you exactly the extra conjunct each
   branch hypothesis wants.
6. Prove the **total** conditional rule, where you must `cases hbv : b.eval σ` on the guard
   *before* choosing a branch — the reverse move, and the reason the two rules are not the same
   proof.

**New Lean.** `cases hbv : b.eval s.store with | true => … | false => …` inside a triple proof.
Nothing else.

**New mathematics / SL.** **Partial versus total correctness**, now with a real difference. Guards
as assertions. Why a loop that never runs satisfies every partial specification you can write.

**Corpus.** `partial_of_total` — **promoted from a `code` block to an exercise**, because it is the
reader's first use of `exec_deterministic` since Unit 20 and it makes the dependency visible;
`bTrue`, `bFalse`; `partialHoare_skip`/`_seq`/`_consequence` (`m13-1`), `partialHoare_ite`
(`m13-2`).

**New Lean needed** — ✔ `new-m12.lean`: `hoare_ite`, `wp_ite`.

`hoare_ite` — the **total**-correctness conditional rule — is missing from Edition 1, which proves
only `partialHoare_ite`. Without it the total-correctness fragment cannot handle a conditional at
all, which is a real gap given that `hoare_while_variant` is a total rule. `wp_ite` is offered as a
coda linking back to Unit 31.

**Author warning.** `site/lean/prelude/m13.lean` does not compile (see the header of this plan).
Check this unit's snippets against `prelude/m12.lean` plus local copies of `bTrue`/`bFalse`, or fix
the prelude first.

**Exercises (4).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x70` | `partial_of_total` | D | 2 | promoted from `code`; **where `exec_deterministic` is finally used**, twenty units after it was proved |
| `m13-1` | `partialHoare_skip` / `_seq` / `_consequence` | C | 2 | the structural rules again with one quantifier flipped; the build-versus-invert contrast made concrete |
| `m13-2` | `partialHoare_ite` | D | 2 | two lines; inversion supplies exactly the extra conjunct each branch demands |
| `x71` | `hoare_ite` | C | 3 | the **total** conditional rule; `cases hbv :` on the guard *before* choosing a branch |

**Hook.** "Every rule so far was proved by looking at one derivation, or by building one. A loop's
derivation has unknown height, and the command it is about is *fixed* while the induction wants to
generalise it. That mismatch has a standard fix, you saw it once in Unit 26, and now it is
compulsory."

**Size.** ~4 screens, ~24 blocks: 1 `txt` of the two definitions with the moved quantifier marked,
1 `cmp` (build versus invert), 1 `note kind:key`, 2 `trace`.

---

### Unit 36 · `invariant` · The invariant rule
**file** `site/content/39-invariant.js`

**One job.** One theorem, `partialHoare_while`, and the technique it needs: induct on a derivation
whose index must be kept general, by adding an equation that constrains it.

**Inherits.** Unit 35's partial rules and its stated mismatch.

**Objectives.**
1. Say why `induction hex` fails directly on `Exec (.loop b c) s s'`, and read the error
   (*Invalid target: Index in target's type is not a variable*).
2. Generalise the command and add the constraining equation `cmd = .loop b₀ c₀` — the standard
   technique, previewed in Unit 26 and compulsory here.
3. Kill eight impossible cases with `intro heq; cases heq` (no-confusion between distinct
   constructors).
4. Read the two surviving cases as the informal argument: `loopFalse` exits with `I` and the false
   guard; `loopTrue` re-establishes `I` by the body and recurses.
5. Recover the stated rule from the helper in two lines, and say where the useful information comes
   from on exit — you learn both `I` *and* the negation of the guard.
6. Apply the rule you just proved to a concrete loop, *before* termination is on the table —
   isolating "find the invariant" from "find the variant".

**New Lean.** None new; the index-equation idiom was introduced in Unit 26.

**New mathematics / SL.** **Loop invariants.** The shape of the invariant rule: preserved by one
iteration *given the guard*, and on exit you learn both `I` and `¬b`.

**Corpus.** `loop_invariant`, `partialHoare_while` (`m13-3`).

**New Lean needed** — ✔ `new-m13.lean`: `countdown_keeps_cell`.

**Exercises (2).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m13-3` | `loop_invariant` and `partialHoare_while` | C | 5 | **the invariant rule.** Ten cases, eight of which vanish; the technique transfers to every derivation-with-a-fixed-index proof the reader will ever write |
| `x72` | `countdown_keeps_cell` | C | 3 | apply the rule you just proved to a concrete loop; the invariant is an *ownership* claim the loop body does not touch, which is the smallest possible taste of Unit 37 |

**Hook.** "Partial correctness is silent about termination — and a loop that never runs satisfies
every partial specification you can write. Buying termination back costs one natural number."

**Size.** ~4 screens, ~22 blocks plus 2 `ex`: 1 `state` of the failing direct induction printed
verbatim, 1 `steps` of the generalise-and-constrain idiom in words, 1 `trace` of the two surviving
cases.

---

### Unit 37 · `variant` · LAB/capstone — a loop that terminates, and owns a cell
**file** `site/content/40-variant.js` · **LAB / CAPSTONE**

**One job.** The variant rule, and then the terminal capstone: a loop that reads a bound, writes a
heap cell every iteration, and terminates — verified with an invariant *and* a variant, in the
language the course actually has.

**Inherits.** Unit 36's invariant rule and its silence about termination.

**Format.** Capstone lab.
1. **Brief:** what a variant is, and why the invariant must be indexed by it.
2. **Worked example:** `countdown_spec` in full — the smallest program whose termination is a
   theorem rather than an accident.
3. **The capstone, staged in three rungs:** state the invariant; prove the step obligation; prove
   the stop obligation. The final theorem is then one application.
4. **Retrospective**, and the course's closing question.

**Objectives.**
1. Prove `hoare_while_variant` by induction on the variant, and say why induction on the variant
   *constructs* the terminating execution, so the conclusion is a total triple.
2. Explain why the postcondition must be `∃ m, I m ∧ ¬b` rather than `I 0 ∧ ¬b` — the loop may exit
   early, and writing `I 0` makes the theorem unprovable at exactly that case. The unit presents
   the `I 0` version, shows it is unprovable, and shows which case fails.
3. Verify a loop that terminates for a reason, and see where Unit 18's truncated subtraction earns
   its two lines.
4. **Invent an invariant that carries a store fact *and* an ownership claim** —
   `aAnd (fact (fun σ => σ x = n)) (l ↦ n)` — the first such invariant in the course, and prove the
   step obligation, where the heap is rewritten and `write_singleton` closes it.
5. Say what would change if the invariant owned a linked list instead — and read Unit 38 to find
   out what stops you proving it in this language.

**New Lean.** `induction n with | zero | succ n ih` used to *build* a total-correctness proof;
`show (!(decide (…))) = false` to open a `BExpr.eval` goal — the last `show` in the course and the
gnarliest, because it opens both `BExpr.eval` and the `Bool` decision procedure at once.

**New mathematics / SL.** **Loop variants.** Well-founded descent, in the concrete form of an
invariant indexed by a decreasing `Nat`. The relationship between partial and total correctness,
mediated by determinism.

**Corpus.** `hoare_while_variant` (`m13-4`); `counterGuard`, `countdown`, `countdown_spec`
(`m13-5`).

**New Lean needed** — ✔ `new-m13.lean`: `drainBody`, `drain`, `drainInv`, `drain_step`,
`drain_stop`, `drain_spec`.

**Why this exists.** Edition 1's last two chapters are M13's "the honest limitation" (the
linked-list capstones are not expressible) and M14 (four exercises with empty `goal` and `sol`
fields). A course should not finish on an apology. `drain_spec` is verified, in-language, and uses
invariant *and* variant *and* heap ownership together — which nothing in Edition 1 does.

**Exercises (3).**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `m13-4` | `hoare_while_variant` | C | 4 | induction on the variant *constructs* the execution; the early-exit subtlety |
| `m13-5` | `countdown_spec` | D | 2 | the worked example, done by the reader; both obligations are one `simp` each |
| `x73` | `drain_spec`, with `drain_step` and `drain_stop` as staged rungs | **G** | 5 | **the terminal capstone.** The reader is given the program and must *invent the invariant*. **Variants:** replace the body with `x := 0` and the step obligation fails — the variant must decrease by exactly one, so a program that jumps to zero needs a more general rule |

**Retrospective and closing question.** (i) Why must the invariant be indexed by the variant?
(ii) What happens to the step obligation if the body is changed to `x := 0`? (iii) The invariant
owns exactly one cell. Write down, in words, the invariant you would need if it owned a linked list
— and then read Unit 38 to find out what stops you proving it here.

**Hook.** "The development is complete: a logic, a language, a semantics, the frame rule, verified
programs, recursive predicates, the wand, `wp`, and both loop rules. Two questions are left. Which
of it was about heaps? And what would it take to walk that linked list?"

**Size.** ~2 screens of prose, ~20 blocks plus 3 `ex`: the worked example (`countdown_spec`),
1 `txt` of the variant rule, 2 `trace`.

---

## D.10 Module 10 · Beyond, and the support pages

---

### Unit 38 · `beyond` · Allocation, generalisation, and what is undone
**file** `site/content/41-beyond.js` · **phase** `Phase 9 · Beyond`

**One job.** Not a survey. Three concrete things: break locality with an allocator and show both
repairs; **prove** the generalisation to arbitrary PCMs rather than assert it; and state the
language's real limitation with the exact change that removes it.

**Inherits.** Unit 37's completed development, and Unit 10's `PCM` structure with `heapPCM`, built
twenty-eight units earlier and not yet used for anything.

**Objectives.**
1. Show that "allocate exactly location `l`" makes the frame rule **unsound**, with a satisfiable
   precondition so the failure is genuine and not vacuous: `{emp} alloc-at l {l ↦ 0}` framed with
   `l ↦ 7` yields a postcondition asserting `l` is two disjoint cells, while the precondition
   `emp ∗ l ↦ 7` is satisfiable.
2. State the three honest repairs — a side condition, nondeterministic fresh allocation with an
   existential in the postcondition, or finite heaps — and say what each costs. Specifically:
   nondeterminism destroys `exec_deterministic` and everything derived from it, including
   `partial_of_total`; finite heaps destroy `funext` as the proof method for heap equality.
3. Explain why the existential over the allocated location is **required** for locality rather than
   cosmetic: framing changes which locations are taken, hence which one the allocator picks, so no
   specification naming a location can be local.
4. Define the separating conjunction of an **arbitrary** PCM and prove its commutativity and unit
   law from the four fields alone — and thereby say exactly which parts of Modules 2–3 were about
   heaps. Compare `pcmStar_comm` line by line with Unit 15's `star_comm` and find the same proof
   with `union_comm` replaced by `K.op_comm`.
5. Name one property heaps have that a general PCM does not (`union_cancel_left`, Unit 10) and say
   what relies on it.
6. State the address-expression limitation, give the one-line syntax change that removes it, and
   explain why every theorem downstream survives — none of them inspects how the address was
   obtained.

**New Lean.** None required. The `sketch` tag, used honestly for the allocation semantics, which is
deliberately not built.

**New mathematics / SL.** **Locality as a property you can lose** — the closing statement of the
course's central theme. **Ghost state** and **concurrency**, sketched, with the PCM proof as the
licence: swap heaps for permissions, tokens, protocol states or fractional ownership and every law
of Module 3 holds verbatim, which is why one framework serves all of them. And the honest boundary:
what does *not* transfer.

**Corpus.** None. (M14 and the reference chapter sit outside `corpus.lean` in Edition 1, correctly,
and continue to.)

**New Lean needed** — ✔ `new-m4.lean`: `pcmStar`, `pcmStar_comm`, `pcmStar_unit_left`. Plus, as
`sketch`: the `alloc` constructor, `hoare_alloc` with its existential, and the finite-heap
alternative. Plus, as `illustration`, the address-expression variant of `hoare_load`.

**Exercises (2) and three Projects.**

| id | name | kind | diff | what it buys |
|---|---|---|---|---|
| `x74` | `pcmStar_comm` | C | 3 | **prove commutativity of `∗` over an arbitrary PCM.** The whole generalisation claim, as a theorem |
| `x75` | `pcmStar_unit_left`, then instantiate `PCM` with a second example of your own choosing | **G** | 2 | confirmation that the pattern is not a coincidence; the suggested second example is `(Nat, +, 0, fun _ _ => True)`, a counting/token monoid. The reader leaves able to build a new resource model |

**Projects** (`note kind:info`, headed **Project**, each with a scope estimate and a list of which
existing theorems must be revisited — **not** `ex` blocks with empty fields):

- **P1 · Allocation.** Add `alloc` with a nondeterministic fresh location; ~150 lines; revisit
  `exec_deterministic`, `partial_of_total`, and every `HeapLocal` proof.
- **P2 · Address expressions.** Change `load`/`write`/`free` to take an `Atom`; ~40 lines of
  refactor plus a pure side condition on the primitive rules; every theorem downstream survives.
- **P3 · The two linked-list capstones.** List length and list dispose, on top of P2; the machinery
  is proved, what is missing is ~100 lines of loop bookkeeping. Their invariants are written out in
  full here as `txt` blocks.

Edition 1 ships these as four `ex` blocks with empty `goal` and `sol` fields — exercises in name
only, and the reason its verified-solution count was 75 of 79. An exercise with no solution is not
an exercise; it is a suggestion, and labelling it as one is more honest.

**Hook.** None — this is the last unit and it says so. It closes with the ideas worth keeping
(Edition 1's `16-ref.js` has an excellent version of this list and it is retained) and points at
the two support pages.

**Size.** ~5 screens, ~30 blocks: 1 `txt` of the unsound framed triple, 1 `tbl` of what transfers
and what does not, 1 `ul` of the ideas worth keeping, 1 `dod`.

---

### §`tactics` · Tactic index
**file** `site/content/42-tactics.js` · **badge** `§` · **support page**

Every tactic, keyword and syntactic form in the course, alphabetically, one line each, with the
unit that introduced it and a deep link to it. **Generated mechanically from §E of this plan** so
it cannot drift. Also carries the standing rule: if a tactic you read about elsewhere is not on
this page, it does not exist in this course.

---

### §`ref` · Reference
**file** `site/content/43-ref.js` · **badge** `§` · **support page**

Notation table (with how to type each symbol) · the theorem index, every corpus theorem with the
unit that proves it · the five rules of proof discipline · the ideas worth keeping · what you built
· what comes next. Carried over from Edition 1's `16-ref.js`, trimmed: the "proof discipline" list
stays; the "where this stops" material moves into Unit 38's Projects.

---

# E. THE GLOBAL LEDGER

**Normative.** A unit's author may use, without ceremony and without re-explaining, anything whose
row is at or above their own unit. Anything below their row **does not exist yet** and must not be
mentioned. Introducing something not on this list requires adding a row and telling the editor.

"first use" is the first unit in which the item appears in an exercise `sol`, in a `code` block, or
in a `walk`/`trace` step. The invariant every row satisfies is *introduced ≤ first use*. Where the
gap is large it is deliberate and the reason is given.

## E.1 Tactics

| tactic | introduced | first use | note |
|---|---|---|---|
| `intro` (incl. pattern `intro ⟨a, b⟩`) | **00** | 00 | first met as "suppose not", since `¬P` is `P → False` |
| `simp [f]`, `simp [f, h]` | **00** | 00 | |
| `simp … at h` | **00** | 00 | |
| `exact` | **01** | 01 | |
| `obtain ⟨…⟩ :=` | **01** | 11 | gap deliberate: taught with the connectives, first *needed* by `splits_assoc` |
| `rcases … with … \| …` | **01** | 08 | gap deliberate: taught with `∨`, first needed by `disjoint_symm` |
| `constructor` (on `∧` and on `↔`) | **01** | 08 | `singleton_disjoint_iff` |
| `left` / `right` | **01** | 08 | |
| `·` (focus dot) | **01** | 04 | |
| `rfl` (as a term) | **01** | 01 | as a *tactic*, unit 02 |
| `rw [h]`, `rw [← h]`, `rw … at h` | **02** | 04 | the silent trailing `rfl` is stated in 02 |
| `unfold` | **02** | 04 | used in `update_comm`, then rarely — by design |
| `simp only [f]` | **02** | 06 | first load-bearing in `erase_write_comm` |
| `show` | **02** | 22 | gap deliberate: shown as a readability device in 02, load-bearing from `assign_constant` |
| `have h : T := e`, anonymous `have` / `this` | **02** | 04 | |
| `absurd` | **02** | 08 | |
| `cases h : e with \| c => …` (saved-equation form) | **02** | 09 | **the most-forgotten syntax in the course**; planted early on `Option`, drilled in 09 |
| `funext` | **03** | 04 | |
| `by_cases h : p` | **03** | 04 | with `case pos` / `case neg` |
| `if_pos` / `if_neg` | **03** | 04 | |
| `<;>` | **03** | 04 | when its branches diverge is stated in 03 |
| `;` on one line | **03** | 04 | |
| `subst` | **08** | 08 | `singleton_disjoint_iff` |
| `<;> ·` (bullet block under a combinator) | **08** | 08 | |
| `rwa` | **09** | 09 | `union_eq_none`; used twice in the whole course |
| `refine … ?_`, several holes, `fun l => ?_` | **10** | 10 | `disjoint_union_left` |
| `cases h` (**inversion** on an inductive hypothesis) | **19** | 19 | |
| `cases h with \| ctor a b => …` | **19** | 19 | |
| `rename_i` | **19** | 26 | introduced with `✝`; first *needed* in `heapLocal_seq` |
| `induction n with \| zero \| succ n ih` | **20** | 20 | warm-up `allZeros_length` |
| `induction xs with \| nil \| cons x xs ih` | **20** | 33 | gap deliberate: warm-up in 20, first real use in `lseg_append` |
| `induction h with \| ctor … ih` (derivation) | **20** | 20 | warm-up `exec_id` |
| `induction h generalizing y` | **20** | 20 | `exec_deterministic` — **the unit's lesson** |
| `▸` | **20** | 20 | |
| `cases hl'` as constructor no-confusion | **20** | 20 | reused at scale in 26 and 36 |
| `simp only [f] at h ⊢` | **21** | 21 | ⚠ optional unit; see E.5 |
| `simpa … using` | **21** | 21 | ⚠ optional unit |
| `induction hle with \| refl \| step` | **21** | 21 | ⚠ optional unit |
| `trace_state` | **00** | — | a tool; never in a solution |
| `sorry` | **00** (named) | 24 (displayed) | never in a solution; appears once, in the stranded frame proof |
| `simp?`, `exact?` | §`errors` | — | diagnostics; never in a solution; their real limits stated |

Tactics that **do not exist here** and must never be used: `set`, `omega`, `linarith`, `ring`,
`simp_arith`, `aesop`, `decide` on non-trivial propositions, `Function.funext_iff`. No Mathlib.

## E.2 Keywords, declarations, syntactic forms

| form | introduced | first use | note |
|---|---|---|---|
| `theorem`, `def`, `example`, `abbrev`, `:=`, `:= by` | **00** | 00 | |
| explicit binders `(x : T)`; `Prop`; `Nat` | **00** | 00 | |
| `Option`, `some`, `none`; `if _ then _ else _`; `¬`; `≠` | **00** | 00 | |
| `#check`, `#eval` | **00** | 00 | `#print` in 02; `#print axioms` in 03 |
| Unicode abbreviations (`\to \star \mapsto \vdash \wand`) | **00** | 00 | |
| `fun x => e`; `→` right-associativity; application | **01** | 01 | |
| `∀` as a dependent function type; `∃`; `∧`; `∨`; `↔` | **01** | 01 | |
| `⟨…⟩` anonymous constructor **and its flattening** | **01** | 01 | exercise `x06` is the six-slot `star` shape, thirteen units early |
| `.1`, `.2`; `Or.inl`, `Or.inr`; dot notation and its resolution rule | **01** | 01 | resolution is by the head constant of the *type* |
| implicit binders `{x : T}`, `@f` | **01** | 09 | first matters in `union_of_none h₂ hl`'s argument order |
| `Iff`, `.mp`, `.mpr` | **01** | 08 | |
| `Eq.symm`, `Eq.trans`, `h.symm` | **01** | 04 | |
| `inductive` (non-recursive: `Option`, `Bool`, `Nat`) | **02** | 02 | |
| pattern-matching `def`; leading-dot name resolution | **02** | 02 | |
| definitional vs propositional equality; `rfl`'s limits | **02** | 02 | |
| `Decidable` and a typeclass instance | **02** | 02 | "a value Lean finds for you" |
| `Option.some.inj` | **02** | 13 | gap deliberate: taught with `Option`, first needed by `pointsTo_value_unique` |
| `congrArg` | **02** | 02 | |
| `congrFun` | **03** | 07 | taught as the exact converse of `funext` |
| `Ne`, `Ne.symm`; inaccessible names and `✝` (first sighting) | **03** | 04 | named properly in 19 |
| `namespace … end`; dot-notation display `h.write l v` | **05** | 05 | |
| `match … with` in a `def`, and why it blocks reduction | **09** | 09 | |
| `structure … where` with `Prop` fields; field projection; the `where` instance syntax | **10** | 10 | `PCM`; reused for `State` at 18 |
| `infix:40` and precedence numbers | **12** | 12 | `⊢` |
| `Sort u`, universe polymorphism | **12** | 15 | declared with `aExists`, first exercised by `star_exists_left` |
| `infix:60` (`↦`) | **13** | 13 | |
| `infixr:55` (`∗`); deep destructuring in `intro` | **14** | 14 | |
| `by …` inside a term-mode tuple slot | **15** | 15 | `star_comm`'s equation slot |
| `inductive … where` with recursive constructors; `deriving Repr` | **18** | 18 | |
| structural recursion; `.ctor` dot notation | **18** | 18 | |
| structure eta; `⟨σ, h⟩` for a structure | **18** | 26 | eta first matters in `heapLocal_seq` |
| `infixr:60` (`;;`) | **18** | 18 | |
| `Bool` vs `Prop`; `==`, `!`, `decide` | **18** | 37 | gap deliberate: declared with `BExpr.eval`, first bites in `countdown_spec` |
| truncated `Nat` subtraction | **18** | 37 | flagged early so it never causes a mystery |
| `inductive … : … → Prop`; indices vs parameters | **19** | 19 | |
| `fail to show termination`, `termination_by` | **19** | — | named, never used |
| `List`, `[]`, `::`, `[a,b,c]` | **20** | 32 | introduced as an induction warm-up, first used for real in `listRep` |
| fuel-indexed recursion; equation lemmas; `max`; `Nat.le_max_*` | **21** | 21 | ⚠ optional unit |
| named arguments `(Q := …)` | **22** | 22 | needed by `assign_twice`; *why* you must supply `Q` is discussed in 29 |
| `have h' : T := e` (definitional restatement); `.trans` | **25** | 25 | |
| the constant-command / index-equation induction idiom | **26** | 26 | compulsory again in 36 |
| recursive `def` returning an `Assertion` | **32** | 32 | |
| `infixr:54` (`-∗`) | **34** | 34 | |
| `Iff.rfl`; `rfl` at `Prop` | **31** | 31 | withheld deliberately until it is the punchline |
| `set_option pp.explicit`, `pp.numericTypes` | §`errors` | — | diagnostic |

## E.3 Library names first relied on

| name | introduced | first use |
|---|---|---|
| `if_pos`, `if_neg` | 03 | 04 |
| `Or.symm` (via `.symm` on an `Or`) | 01 | 08 |
| `union_of_none`, `union_of_some`, `union_eq_none` | 09 | 09 |
| `disjoint_union_left`, `disjoint_union_right` | 10 | 11 |
| `union_assoc`, `union_comm` | 10 | 11 |
| `entails_trans` (the glue for every chain) | 12 | 15 |
| `star_mono_left`, `star_mono_right` | 15 | 17 |
| `star_assoc_left`, `star_assoc_right` | 16 | 17 |
| `two_cells_distinct` | 17 | 27, 30, 32 |
| `exec_deterministic` | 20 | 35 |
| `heapOnly_*`, `preserves_of_heapOnly` | 24 | 27 |
| `preserves_of_storeStable` | 29 | 29 |
| `write_singleton`, `erase_singleton` | 06 | 23 |
| `heap_eq_singleton` | 31 | 31 |
| `Nat.le_max_left`, `Nat.le_max_right` | 21 | 21 (⚠ optional) |

## E.4 Mathematics and separation-logic concepts

| concept | introduced | note |
|---|---|---|
| aliasing | 00 | the problem |
| memory as a function; partial function via `Option` | 00 (named) / 02 (properly) | two stages, deliberate |
| ownership versus truth | 00 (named) / 13 (decided) | the course's central thread |
| *unproved* versus *false* | 00 | |
| propositions-as-types; proofs-as-terms | 01 | |
| definitional versus propositional equality | 02 | |
| decidability | 02 | |
| function extensionality as a rule | 03 | |
| locality of an update ("the baby frame rule") | 04 | |
| the interface discipline (never unfold again) | 05 | |
| deallocation; domain of a heap | 05 | |
| disjoint operations commute — the germ of the frame rule | 06 | |
| **footprint**; exact versus inexact ownership | 07 (posed) / 13 (decided) / 23 (justified) | **a three-stage thread, not a loop** |
| disjointness of resources | 08 | |
| **separation implies non-aliasing** | 08 (heaps) / 17 (assertions) | |
| left-biased total union; the register shift | 09 | |
| monoid; commutative monoid; **partial commutative monoid** | 10 | as a Lean `structure`, instantiated |
| cancellativity (what heaps have and PCMs need not) | 10 | bounds the Unit 38 generalisation |
| the splitting relation; associativity of a *partial* operation | 11 | the first genuinely hard step |
| assertion as a predicate on states; entailment; preorder | 12 | |
| pointwise lifting of a logic; `fact` — the trivial embedding | 12 | |
| exact ownership; the first-person reading of an assertion | 13 | |
| separating conjunction | 14 | |
| **weakening, contraction, substructural logic** | 14 | *before* any law |
| monotonicity and congruence | 15 | |
| the commutative monoid of assertions | 16 | |
| `pure` — the `∗`-compatible embedding; normalisation | 17 | *after* `∗`, so it can be derived |
| abstract syntax as an inductive type; the store is not a resource | 18 | |
| **inductively defined relations**; derivations | 19 | |
| **big-step semantics**; stuck versus diverging; inversion | 19 | |
| **structural induction**; the induction hypothesis; generalisation | 20 | its own unit |
| determinism | 20 | consumed at 35 |
| fuel; soundness and completeness of an implementation | 21 | ⚠ optional |
| Hoare triple; safety as an existential; variance | 22 | |
| total versus partial correctness | 22 (named) / 35 (they differ) | |
| shallow embedding; semantic substitution | 22 | |
| small-footprint specification | 23 | |
| **locality**; the commuting square | 24 | |
| non-interference on the store; semantic vs syntactic side conditions | 24 | |
| compositional locality | 26 | |
| **the frame rule as a theorem** | 27 | |
| the classical rule refuted; the separating rule proved | 28 | the debt from 00, paid |
| symbolic execution; store-stability; a rule's shape as a design choice | 29 | |
| **predicate transformers; weakest precondition** | 31 | |
| angelic versus demonic `wp`; weakest versus merely sufficient | 31 | |
| **recursive predicates**; shape + ownership in one definition | 32 | |
| least fixed point | 32 | foldable aside |
| list segments; traversal invariants; debugging a definition with a failed proof | 33 | |
| **adjunction**, from currying; contravariance | 34 | no category theory |
| BI algebra | 34 | aside, with the translation supplied |
| loop invariant | 36 | |
| loop variant; well-founded descent as a decreasing `Nat` | 37 | |
| locality is losable; allocation | 38 | |
| **generalisation to arbitrary PCMs** | 38 | proved, not asserted |
| ghost state; concurrency | 38 | sketched, with the PCM proof as the licence |

## E.5 Notation

| introduced | notation |
|---|---|
| 12 | `⊢`, `⊣⊢` |
| 13 | `↦` |
| 14 | `∗` |
| 18 | `;;` |
| 34 | `-∗` |

The course's notation is complete at Unit 34.

## E.6 The optional-unit fence

Unit 21 (`interpreter`) is optional. Verified against `corpus.lean`: `run`, `run_sound`,
`run_mono`, `run_le` and `run_complete` have **no downstream consumers** — no occurrence of any of
them after line 735 of the corpus. Four items are introduced there and used nowhere else:
`simpa … using`, `induction hle with | refl | step`, `Nat.le_max_*`, and `max`.

**Rule for authors:** no unit after 21 may use any of those four. If a later author finds they want
one, they must either avoid it or introduce it themselves with a note — and the fact that they had
to is a signal that Unit 21 should be made compulsory. As planned, it is not.

Note that `simp only` is **not** fenced: it is introduced in Unit 02 and is load-bearing in
Unit 06, so a reader who skips Unit 21 still has it.

## E.7 Ordering checks performed

Four constraints are load-bearing. Each is satisfied by the numbering above, and each was checked
row by row:

1. **No tactic is used before its introduction.** The riskiest cases: `<;>` (introduced 03, first
   used 04); `subst` (08 / 08); `refine` (10 / 10); `rename_i` (19 / 26); `simp only` (02 / 06);
   `show` (02 / 22); `cases h : e with` (02 / 09).
2. **No definition is used before it exists.** `Heap.union` and `Heap.splits` are *stated* in
   Unit 08 because `splits` mentions `union`, but are not *proved about* until Units 09 and 11 —
   the author of Unit 08 states them and moves on. `PartialHoare` is defined in Unit 22 and not
   used until Unit 35. `PCM` is defined in Unit 10 and not used again until Unit 38; Unit 10 says
   so explicitly so the reader does not expect the rest of the course to be generic.
3. **No mathematics is assumed that was not built.** Inductive relations: 19, before determinism
   (20) and before any use in Modules 5–9. Structural induction: 20, before every induction in the
   course except its own warm-ups. PCM: 10, before `∗` (14). Big-step semantics: 19, before triples
   (22). Substructurality: 14, before the frame rule is wanted (23). Adjunction: 34, and only
   there.
4. **Plain `Nat` induction comes before derivation induction, in the same unit.** Unit 20 runs
   `Nat` → `List` → derivation → `generalizing` in that order. (This is the one place where the
   three draft plans disagreed; putting all four in one unit, escalating, is what removes the
   cliff, and it means no later author has to introduce `Nat` induction as a special case of
   something harder.)

---

# F. THE EXERCISE LADDER

**148 `ex` blocks**, in reading order. **73 of them carry the 75 Edition-1 corpus ids** (two blocks
carry two ids each: `m9-2`+`m9-3`, `m12-4`+`m12-5`), **75 are new**.

**Ids are load-bearing and are preserved.** Every Edition-1 exercise id keeps its id *and* its
`name`, so reader progress survives; new exercises use the disjoint `x01`–`x75` namespace.
Chapter ids change, so `app.js` needs a redirect table from the seventeen Edition-1 chapter hashes
to the unit that now opens that material (§H.6).

Source: **C** corpus (Lean quoted verbatim, tagged `verified`) · **P** promoted from an Edition-1
`code` or `illustration` block to an exercise · **N** new. ✔ = verified Lean exists today in
`site/lean/edition2/`; ⧗ = specified, must be written and compiled before the unit is authored.

Kind: **D** drill · **C** construction · **G** design. Difficulty 1–5; 4 and 5 get `hard: true`.

| # | unit | id | name | kind | d | src | skill it adds |
|---|---|---|---|---|---|---|---|
| 1 | 00 | `x01` | write a heap, prove a lookup | D | 1 | N ⧗ | a heap is a function you can write down |
| 2 | 00 | `x02` | the aliased postcondition is unsatisfiable | D | 1 | N ✔ | *unproved* versus *false* |
| 3 | 01 | `x03` | `comp` | D | 1 | N ✔ | term mode: composition is application |
| 4 | 01 | `x04` | `and_comm'`, `or_comm'` | D | 2 | N ✔ | `⟨…⟩`, `.1`/`.2`; `∨` is eliminated, not projected |
| 5 | 01 | `x05` | `exists_mono` | C | 2 | N ✔ | witness in, witness out — every `star_mono` proof |
| 6 | 01 | `x06` | `nested_pack` / `nested_unpack` | C | 3 | N ⧗ | **the six-slot shape of `star`**, thirteen units early |
| 7 | 02 | `x07` | `double`, and where `rfl` stops | D | 1 | N ✔ | when `rfl` works and when it does not |
| 8 | 02 | `x08` | `Option.some.inj`; `some v ≠ none` two ways | D | 2 | N ⧗ | injectivity as a lemma; constructors are distinct |
| 9 | 02 | `x09` | `defined` via `cases hl : h l` | C | 3 | N ⧗ | **the `hl :` that records the equation** |
| 10 | 03 | `x10` | `funext_drill` | D | 2 | N ⧗ | function equality is not `rfl` |
| 11 | 03 | `x11` | `if_drill` | D | 2 | N ⧗ | `if_pos`/`if_neg` by hand, before `simp` hides them |
| 12 | 03 | `x12` | `by_cases_drill` | C | 2 | N ⧗ | both branches; the `pos` branch rewrites the goal |
| 13 | 04 | `m0-1` | `update_same` | D | 1 | C | first `simp [def]`; the lab's worked example |
| 14 | 04 | `m0-2` | `update_other` | D | 1 | C | hypothesis into `simp`; the `≠` orientation rule |
| 15 | 04 | `m0-3` | `update_shadow` | C | 2 | C | `funext` → `by_cases` → `<;> simp` |
| 16 | 04 | `m0-4` | `update_comm` | C | 3 | C | three regions; **non-aliasing used exactly once** |
| 17 | 04 | `x13` | `update_idem` | **G** | 2 | N ✔ | *design*: state it yourself |
| 18 | 05 | `m1-1` | `singleton_same` | D | 1 | C | the interface begins |
| 19 | 05 | `m1-2` | `singleton_other` | D | 1 | C | a singleton really is a singleton |
| 20 | 05 | `m1-3` | `write_same` / `write_other` | D | 1 | C | the pair that *characterises* write |
| 21 | 05 | `m1-4` | `erase_same` / `erase_other` | D | 1 | C | the mirror pair; interface complete |
| 22 | 06 | `m1-5` | `write_shadow` | C | 2 | C | the schema; the assignment axiom's content |
| 23 | 06 | `m1-6` | `erase_write_same` | C | 2 | C | why `write; free` = `free` |
| 24 | 06 | `m1-7` | `write_comm` | C | 3 | C | **the germ of the frame rule**; the counterexample |
| 25 | 06 | `m1-8` | `write_singleton` / `erase_singleton` | C | 2 | C | the write rule and the free rule, computed in advance |
| 26 | 06 | `x14` | `erase_erase`, `write_of_eq` | C | 3 | N ✔ | a free win, then a heap hypothesis driving the `pos` branch |
| 27 | 06 | `x15` | `erase_write_comm`; refute general commutation | **G** | 3 | N ✔+⧗ | `unfold` versus `simp only`; state a false claim and refute it |
| 28 | 07 | `x16` | a two-cell heap satisfies the loose reading | D | 1 | N ✔ | concreteness |
| 29 | 07 | `x17` | it does *not* satisfy the exact reading | C | 3 | N ✔ | the `congrFun`-at-a-witness pattern |
| 30 | 07 | `x18` | after `free`, the heap is not empty | C | 3 | N ✔ | **the free rule is false under the loose reading** |
| 31 | 08 | `m2-1` | `disjoint_symm` | D | 1 | C | a `def : Prop` unfolds under `intro` |
| 32 | 08 | `m2-2` | `disjoint_empty_left` / `_right` | D | 1 | C | a proof with no tactics at all |
| 33 | 08 | `m2-3` | `singleton_disjoint` (+ `_iff`) | C | 3 | C | **separation proves non-aliasing** |
| 34 | 08 | `x19` | `self_disjoint_iff_empty` | C | 2 | N ✔ | the engine of no-contraction; repairs a dangling reference |
| 35 | 09 | `x20` | `union_of_none` / `union_of_some` | D | 2 | P ✔ | rewrite the scrutinee, let the `match` compute |
| 36 | 09 | `x21` | `union_eq_none` | C | 3 | P ✔ | the only one with content; first `rwa` |
| 37 | 09 | `m2-4` | `union_empty_left` / `_right` | C | 2 | C | one is `rfl` pointwise, its mirror is not |
| 38 | 09 | `x22` | `union_self` | D | 1 | N ✔ | left-biasing, sharply |
| 39 | 10 | `m2-5` | `union_assoc` | C | 3 | C | **associativity needs no hypothesis** |
| 40 | 10 | `m2-6` | `union_comm` | C | 3 | C | **commutativity does**; false without |
| 41 | 10 | `m2-7` | `disjoint_union_left` / `_right` | C | 4 | C | the workhorses; derive, do not reprove |
| 42 | 10 | `x23` | `heapPCM` | D | 1 | N ✔ | **"heaps form a PCM" becomes a term** |
| 43 | 10 | `x24` | `union_cancel_left` | C | 4 | N ✔ | what heaps have that PCMs need not |
| 44 | 11 | `x25` | `splits_empty_right` | D | 1 | N ✔ | symmetry restored; a warm-up before the checkpoint |
| 45 | 11 | `m2-8` | `splits_empty_left` / `splits_comm` | D | 2 | C | term proofs over a conjunction |
| 46 | 11 | `m2-9` | `splits_assoc` | C | 4 | C | **checkpoint.** `star_assoc`, undressed |
| 47 | 11 | `x26` | `union_not_comm` | **G** | 2 | N ⧗ | a negated statement written from scratch |
| 48 | 12 | `m3-2` | `entails_refl` / `entails_trans` | D | 1 | C | identity and composition; the glue for everything after |
| 49 | 12 | `m3-3` | `and_left` / `_right` / `and_intro` | D | 1 | C | projections — **remember that `∧` has them** |
| 50 | 12 | `x27` | `or_left` / `or_right` / `or_elim` | D | 2 | N ✔ | completes the classical picture |
| 51 | 12 | `x28` | `equiv_refl` / `_symm` / `_trans` | D | 1 | N ✔ | makes `⊣⊢` chains legitimate |
| 52 | 12 | `x29` | `aAnd` comm and assoc | D | 2 | N ⧗ | a baseline to measure `∗` against |
| 53 | 13 | `m3-1` | `pointsTo_value_unique`, `pointsTo_not_emp` | C | 3 | C | exactness; the first refutation of an entailment |
| 54 | 13 | `x30` | `emp` as "nothing anywhere" | **G** | 2 | N ⧗ | *design*: state the two readings and prove they agree; the equational style is not a trick |
| 55 | 14 | `x31` | `star_intro` | D | 1 | N ✔ | the construction move, isolated |
| 56 | 14 | `x32` | `star_same_loc_absurd` | C | 2 | N ✔ | the consumption move |
| 57 | 14 | `x33` | `no_star_weakening` | C | 4 | N ✔ | **no weakening** — the frame rule's reason to exist |
| 58 | 14 | `x34` | `no_star_duplication` | C | 4 | N ✔ | **no contraction** — absent from Edition 1 entirely |
| 59 | 14 | `x35` | `starNoDisj_dup` | C | 3 | N ✔ | contraction localised to one conjunct |
| 60 | 15 | `m4-1` | `star_emp_left` / `_right` | C | 2 | C | consume a star |
| 61 | 15 | `m4-2` | `star_emp_*_intro` | C | 2 | C | **choose the cut**; the `.symm` discipline |
| 62 | 15 | `m4-3` | `star_comm` | C | 2 | C | where `union_comm hd` is spent |
| 63 | 15 | `m4-5` | `star_mono` (+ two specialisations) | D | 2 | C | improve one side without touching the other |
| 64 | 15 | `m4-6` | `star_or_left` / `star_exists_left` | C | 2 | C | **the first line of both list proofs** |
| 65 | 15 | `x36` | `star_emp_*_iff`, `star_comm_iff`, `star_congr` | D | 1 | N ✔ | rewriting *inside* a star with `⊣⊢` |
| 66 | 16 | `m4-4` | `star_assoc_left` / `_right` | C | 4 | C | the hardest pure-`∗` proof; both directions |
| 67 | 16 | `x37` | `star_assoc_iff` | D | 1 | N ✔ | packaging |
| 68 | 17 | `m4-7` | `two_cells_distinct` | C | 2 | C | **the punchline of Phase 1** |
| 69 | 17 | `m4-8` | `star_pure_*`, `star_swap_middle`, rotations | C | 3 | C | **proof by composition**; the toolkit, complete |
| 70 | 17 | `x38` | `star_or_right` / `star_exists_right` | C | 2 | N ✔ | the converses, and that they are not automatic |
| 71 | 18 | `x39` | `@Store.set = @update` + the store laws | D | 1 | N ✔ | **the store is `update`** |
| 72 | 18 | `x40` | `Atom` evaluation; truncated subtraction | D | 1 | N ✔ | concreteness, before it can mystify at 37 |
| 73 | 18 | `x41` | `Atom.size` | **G** | 2 | N ✔ | *design*: define a size function and state one equation; structural recursion, before 21 shows its limit |
| 74 | 19 | `m5-1` | `exec_skip_inv` | D | 1 | C | the first inversion |
| 75 | 19 | `x42` | `exec_assign_inv`, `exec_load_inv` | C | 2 | N ✔ | inversion recovering a premise — **the shape of Module 6** |
| 76 | 19 | `x43` | `exec_load_stuck` | C | 2 | N ✔ | **a fault is the absence of a derivation** |
| 77 | 19 | `x44` | `exec_skip_seq_inv` | C | 3 | N ✔ | nested inversion; the inaccessible middle state |
| 78 | 20 | `x45` | `allZeros_length`, `append_nil` | D | 2 | N ✔ | induction with nothing else at stake |
| 79 | 20 | `x46` | `exec_id` | C | 3 | N ✔ | ten cases, ten hypotheses, no content — look at the goals |
| 80 | 20 | `m5-2` | `exec_deterministic` | C | 4 | C | **`generalizing`** — the course's steepest step |
| 81 | 21 | `x47` | `run_example` | D | 1 | N ⧗ | ⚠ execute a program; the unit opens on a win |
| 82 | 21 | `m5-3` | `run_sound` | C | 4 | C | ⚠ definitional reduction under a `match` |
| 83 | 21 | `m5-4` | `run_mono` / `run_le` / `run_complete` | C | 5 | C | ⚠ induction on `≤`; `max` to reconcile two bounds |
| 84 | 22 | `m6-1` | `hoare_consequence` | D | 2 | C | variance; **Module 3 becomes usable here** |
| 85 | 22 | `m6-2` | `hoare_skip` / `hoare_seq` | C | 2 | C | choosing the intermediate assertion *is* verifying |
| 86 | 22 | `m6-3` | `hoare_assign` | D | 2 | C | the payoff of semantic `subst` |
| 87 | 22 | `m6-4` | `assign_constant` | C | 2 | C | **first `show` in anger** |
| 88 | 22 | `m6-5` | `assign_twice` | C | 3 | C | a side condition you assumed you needed, and do not |
| 89 | 23 | `m7-1` | `hoare_load` | C | 3 | C | the `pure` conjunct forces the cut |
| 90 | 23 | `m7-2` | `hoare_write` | C | 2 | C | one application of `write_singleton` |
| 91 | 23 | `m7-3` | `hoare_free` | C | 2 | C | one application of `erase_singleton`; exactness pays |
| 92 | 23 | `m7-4` | `clearCell_spec` | D | 1 | C | instantiation; opens the unit on a win |
| 93 | 23 | `x48` | `writeTwice_spec` | **G** | 2 | N ⧗ | *design*: state and prove a spec for writing twice to one cell. Composition that *does* work — the baseline |
| 94 | 23 | `m7-5` | `readAndFree_spec` | C | 3 | C | **the deliberate defeat**; build `Exec` by hand |
| 95 | 24 | `m8-1` | `heapLocal_skip` / `_assign` / `_load` | C | 2 | C | `union_of_some` is the whole load case |
| 96 | 24 | `x49` | `heapOnly_emp` / `_pointsTo` / `_star` | D | 2 | P ✔ | **covers any frame at any size** |
| 97 | 24 | `x50` | `not_heapOnly_pure` | C | 4 | N ✔ | where the free route stops |
| 98 | 24 | `x51` | the store counterexample, as a refutation | **G** | 4 | N ✔ | **`Preserves` earned, not asserted** |
| 99 | 25 | `m8-2` | `heapLocal_write` | C | 4 | C | disjointness as *bookkeeping* |
| 100 | 25 | `m8-3` | `heapLocal_free` | C | 4 | C | disjointness as *load-bearing*; `none = hFrame x` |
| 101 | 26 | `m8-4` | `heapLocal_seq` | C | 3 | C | locality composes; `rename_i`; structure eta |
| 102 | 26 | `x52` | `heapLocal_ite` | D | 2 | N ✔ | control flow, the easy half |
| 103 | 26 | `x53` | `heapLocal_loop` | C | 4 | N ✔ | **the constant-command induction idiom** |
| 104 | 27 | `m8-5` | `hoare_frame` | C | 4 | C | **the theorem the course exists to prove** |
| 105 | 27 | `m8-6` | `write_with_frame` | D | 2 | C | five lines, no heaps; length independent of the frame |
| 106 | 27 | `x54` | `free_with_frame` | C | 3 | N ✔ | **checkpoint**; `star_emp_left` earns its keep |
| 107 | 28 | `x55` | `classical_conjunction_rule_is_false` | C | 4 | N ✔ | **the opening question, refuted** |
| 108 | 28 | `x56` | `separated_write_ok` | D | 1 | N ✔ | **the opening question, repaired, in four lines** |
| 109 | 29 | `x57` | `storeStable_*`, `preserves_of_storeStable` | D | 2 | P | the second `Preserves` discharger |
| 110 | 29 | `x58` | `readAndFree_framed` | D | 2 | P | **the promise of Unit 23, kept** — the best before/after |
| 111 | 29 | `x59` | `pure_star_regroup` | C | 3 | P | the bookkeeping entailment |
| 112 | 29 | `x60` | `hoare_load_and`, `and_fact_star` | C | 3 | N ✔ | a rule's *shape* is a design choice with a cost |
| 113 | 29 | `m9-1` | `copyCell_spec` | C | 4 | C | **the first compositional verification** |
| 114 | 29 | `m9-2`+`m9-3` | `exec_seq_assoc`, `moveCell_spec` | C | 3 | C | semantic vs syntactic `;;`; memory given back |
| 115 | 30 | `m9-4` | `preserves_load_fact` | C | 3 | C | the store-side analogue of heap disjointness |
| 116 | 30 | `x61` | `swap_heap` | C | 4 | N ✔ | three regions over a union, isolated |
| 117 | 30 | `x62` | `swap_spec` | C | 5 | N ✔ | **the capstone; Edition 1's open exercise, closed** |
| 118 | 31 | `m12-1` | `wp_skip` / `wp_assign` | C | 2 | C | first `⊣⊢`; invert forwards, build backwards |
| 119 | 31 | `m12-2` | `wp_seq` | C | 3 | C | **the rule that makes backwards reasoning work** |
| 120 | 31 | `m12-3` | `wp_mono` | D | 2 | C | a monotone transformer |
| 121 | 31 | `x63` | `wp_sound`, `wp_weakest` | **G** | 1 | N ✔ | *design*: state the two theorems that make the word "weakest" precise |
| 122 | 31 | `m12-4`+`m12-5` | `wp_free_emp`, `wp_write` (+ `heap_eq_singleton`) | C | 4 | C | `wp` **computed**; the irrelevant value quantified |
| 123 | 31 | `x64` | `wp_frame` | D | 1 | N ✔ | one line, because `Hoare` and `⊢ wp` are one statement |
| 124 | 32 | `m10-1` | the three fold/unfold lemmas | D | 1 | C | why `entails_refl _` suffices, and why you name them |
| 125 | 32 | `x65` | `listRep_cons_ne_zero` | D | 2 | N ✔ | pure information falls out of a recursive predicate |
| 126 | 32 | `m10-2` | `node_cells_distinct` | D | 1 | C | non-aliasing from ownership, not arithmetic |
| 127 | 32 | `m10-3` | `concrete_list` | C | 4 | C | five layers of witness-then-recurse; `subst` first |
| 128 | 33 | `x66` | `aExists_mono`, `lseg_nil_iff` | D | 2 | P ✔ | work under a binder |
| 129 | 33 | `m10-4` | `lseg_append` | C | 4 | C | **the classical theorem**, done in the algebra |
| 130 | 33 | `m10-5` | `lseg_listRep` | C | 3 | C | the definitions are aligned; the bug shows here first |
| 131 | 33 | `x67` | `listRep_null` | **G** | 3 | N ✔ | **checkpoint.** The `cons` case dies on its own `pure` |
| 132 | 34 | `m11-1` | `wand_intro` | C | 2 | C | currying; the equation is `rfl` by construction |
| 133 | 34 | `m11-2` | `wand_elim` | C | 2 | C | modus ponens for resources |
| 134 | 34 | `m11-3` | `star_wand_adjunction` | C | 2 | C | **the adjunction**, from the two halves |
| 135 | 34 | `m11-4` | `wand_mono` | D | 2 | C | variance, read off the definition |
| 136 | 34 | `x68` | `wand_unit`, `hole_intro`, `hole_elim` | C | 2 | N ✔ | **structure with a hole**, in one-line proofs |
| 137 | 34 | `x69` | `wand_curry` / `wand_uncurry` | C | 3 | N ✔ | the resource-sensitive currying isomorphism |
| 138 | 35 | `x70` | `partial_of_total` | D | 2 | P | **where `exec_deterministic` is finally used** |
| 139 | 35 | `m13-1` | `partialHoare_skip` / `_seq` / `_consequence` | C | 2 | C | build versus invert |
| 140 | 35 | `m13-2` | `partialHoare_ite` | D | 2 | C | inversion supplies the guard |
| 141 | 35 | `x71` | `hoare_ite` | C | 3 | N ✔ | the **total** conditional rule |
| 142 | 36 | `m13-3` | `loop_invariant`, `partialHoare_while` | C | 5 | C | **generalise-and-constrain**; eight cases vanish |
| 143 | 36 | `x72` | `countdown_keeps_cell` | C | 3 | N ✔ | apply the invariant rule before termination is on the table |
| 144 | 37 | `m13-4` | `hoare_while_variant` | C | 4 | C | induction on the variant *constructs* the execution |
| 145 | 37 | `m13-5` | `countdown_spec` | D | 2 | C | the worked example, done by the reader |
| 146 | 37 | `x73` | `drain_spec` (+ `drain_step`, `drain_stop`) | **G** | 5 | N ✔ | **terminal capstone.** An invariant carrying a store fact *and* an ownership claim |
| 147 | 38 | `x74` | `pcmStar_comm` | C | 3 | N ✔ | **the generalisation, proved** |
| 148 | 38 | `x75` | `pcmStar_unit_left`; instantiate a second PCM | **G** | 2 | N ✔ | build a new resource model |

## F.1 The difficulty curve

```
 5 |                                                    ●                ●        ●   ●
 4 |                    ●   ●   ●     ●       ●     ●   ●  ● ● ●●  ●   ●   ●   ●   ●
 3 |    ● ●  ●● ● ●● ● ● ●● ●  ● ●●  ●●● ●  ●● ●  ●● ●●  ● ● ●  ●●  ●● ● ●●  ● ● ●  ●
 2 |  ●●●●●●●● ●●● ●●● ●● ●●●●● ●●●●●● ●● ●●●● ●●●● ●● ●● ●●●●● ●●● ●●●●●● ●●●● ●●● ●●
 1 | ●●● ●●●  ●●●●● ●   ●   ●    ●   ● ●  ●  ●   ●  ●   ●  ●  ●   ●    ●  ●    ●
   +----------------------------------------------------------------------------------
    00  02  04  06  08  10  12  14  16  18  20  22  24  26  28  30  32  34  36  38
```

Rules the curve obeys, and which reviewers should check:

- **No difficulty-4 exercise before #16** (`update_comm` is a 3, and is the first hard-feeling
  one). Module 0 tops out at 3.
- **Every module opens at difficulty ≤ 2**, and **after every 4 or 5 the next exercise is a 1 or a
  2**: `x14`'s `erase_erase` after `write_comm`; `x23` `heapPCM` after `disjoint_union_left`;
  `x25` after nothing hard but before `splits_assoc`; `x47` `run_example` before `run_sound`;
  `m8-6` after `hoare_frame`; `x56` after `x55`; `x63`/`x64` around `wp_write`.
- **Every difficulty-5 exercise is a capstone**, staged into named rungs, never a monolithic `ex`:
  `m5-4` (three theorems), `x62` (preceded by `x61`), `m13-3` (the two surviving cases named in
  advance), `x73` (three rungs).
- **No unit has more than two exercises at 4 or above.**
- **The one place two consecutive units are majority-hard is 25/26**, and that is flagged in §H.5
  with a mitigation.
- **Eleven design [G] exercises**, roughly one per module: `x13` (M0), `x15` (M1), `x26` (M2),
  `x30` (M3), `x41` (M4), `x48` (M5), `x51` (M6), `x63` (M7), `x67` (M8), `x73` (M9), `x75` (M10).
  Consolidation always means *writing a statement*, not repeating a proof.
- **Drills front-load:** of the 40 drills, 24 are in Units 00–13.

## F.2 Distribution against Edition 1

| | Edition 1 | Edition 2 | why |
|---|---|---|---|
| `ex` blocks | 79 | **148** | decomposition, plus a real Lean runway |
| with verified solutions | 75 | **148** | the 4 empty M14 blocks become labelled Projects |
| Module 0 / Lean runway | 4 | **17** | the audience changed; a zero-Lean reader needs drills |
| promoted from given code | — | **9** | `union_of_*`, `union_eq_none`, `heapOnly_star` and friends, `storeStable_*`, `pure_star_regroup`, `aExists_mono`, `partial_of_total`, `readAndFree_framed` |
| design [G] exercises | 0 | **11** | consolidation means stating something |
| exercises with graded 4-rung hints | partial | **all 148** | see §H.1 of `PEDAGOGY.md` |
| appendix exercises with empty fields | 4 | **0** | replaced by 3 labelled Projects |

---

# G. WHAT CHANGES FROM EDITION 1, AND WHY

Each item names the Edition-1 behaviour concretely, with the file it lives in, and the structural
decision that replaces it.

## G.1 The overview chapter is abolished

**Edition 1.** `content/00-overview.js` is 55 KB and defines, in order: the five `abbrev`s,
`Assertion`, `emp`, `pointsTo` with its `infix:60`, `star` with its `infixr:55` **and a five-part
`anat` block dissecting it**, `Hoare`, and the statement of `hoare_frame` with both side
conditions. Chapters M1–M8 then define all of those again. `content/05-m4.js` opens with a `code`
block of `star` followed by **a second five-part `anat` on the same three lines**. The reader meets
the definition of `∗` twice, dissected twice, 300 KB apart, and in neither place has the question it
answers been posed. Edition 1's own `PEDAGOGY.md` forbids exactly this.

**Edition 2.** No overview. Unit 00 is mathematics from its first paragraph: a false rule, a
counterexample, a rejected repair, and a named promissory note. The five `abbrev`s appear because
the counterexample cannot be written without them. `Assertion`, `↦`, `∗`, `Hoare` and `hoare_frame`
appear **once each**, in Units 12, 13, 14, 22 and 27. There is exactly one `anat` on `star`, in
Unit 14. Orientation material moves to the unnumbered support pages `goalstate` and `errors`,
neither of which is on the reading path, and both of which say so.

*Why.* A map of the territory handed to someone who has not been anywhere is not orientation, it is
noise — and it spends the reader's first hour on definitions they cannot yet want.

## G.2 The audience instruction is inverted

**Edition 1.** `PEDAGOGY.md`: *"A **professional mathematician** who is a beginner in Lean. They are
not confused by partial functions, monoids, induction, fixed points… **Never explain those.**"* And
`AUTHORING.md` house rule 2: *"Explain the Lean, not the mathematics the reader already knows."*
The consequence is visible everywhere: `00-overview.js`'s `orient.needs` reads *"Partial functions,
monoids, induction, inductively defined relations. All assumed. **None of it explained.**"*;
`03-m2.js` announces that heaps form a partial commutative monoid and never says what one is;
`05-m4.js` closes with a sentence about the commutative monoid of assertions that is either already
known or permanently opaque.

**Edition 2.** That instruction is **deleted**, and its replacement is the new `PEDAGOGY.md`. Every
mathematical object above ordinary undergraduate background is introduced in the unit whose story
needs it, before it is used: partial functions (02, 05), monoid and PCM (10), substructurality (14),
inductively defined relations (19), structural induction and generalisation (20 — a whole unit),
predicate transformers (31), least fixed points (32, aside), adjunctions (34).

*Why.* This is the client's stated complaint, and it is not a matter of tone. It changes where units
go: `pure` moves four units later, induction gets its own unit, and `footprint` becomes a unit that
proves no corpus theorem at all.

## G.3 The opening question is answered on the page

**Edition 1.** `00-overview.js` opens with the classical rule and refutes
`¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5)`. That is a true and useful fact about
`Option`, and it is *not* the Hoare rule — it cannot be, because no triple is defined for another
six chapters. Nothing tells the reader a promissory note has been issued, and nothing later redeems
it. The word "aliasing" does not recur after M4.

**Edition 2.** Unit 00 shows the same heap-level fact, then **writes the statement it cannot yet
make as a named theorem with no proof**, explicitly as a debt, in a `note kind:key`. Unit 28 pays it
with two theorems, both verified against `prelude/m8.lean`:
`classical_conjunction_rule_is_false` (the rule, refuted, inside the real logic with the real
semantics) and `separated_write_ok` (the same specification with `∗`, proved in four lines by
framing).

*Why.* A course that opens with a question and never visibly answers it has not told a story. These
two theorems side by side are the entire argument for separation logic, and they are cheap: nine
lines of refutation, four of repair, and every ingredient proved by the reader. **This is the
single most consequential addition in the plan.**

## G.4 Substructurality is taught before the laws, and no-contraction is added

**Edition 1.** `05-m4.js` runs unit → commutativity → associativity → monotonicity → distribution →
non-aliasing → normalisation. `no_star_weakening` appears mid-chapter as an `illustration` in a
section titled "No projection", between exercises 2 and 3. **No-contraction is never stated at
all** — neither `P ⊬ P ∗ P` nor any equivalent appears in the corpus or the content.

**Edition 2.** Unit 14 comes *before* any law and proves both failures as exercises:
`no_star_weakening` and the new, verified `no_star_duplication`, plus `starNoDisj_dup`, which
localises contraction to the single disjointness conjunct. The unit defines weakening and
contraction, names substructural logic, and derives the *necessity* of the frame rule from the
absence of weakening — so that when Unit 23 fails to compose two rules, the reader has already been
told why it must.

The unit also promotes Edition 1's best buried observation to its conclusion: `05-m4.js` hides,
inside a `detail` in `m4-7`'s `deep` array, the correction that exactness is *not* what gives you
non-aliasing (disjointness is) but what gives you the *absence of weakening*. That is the precise
statement of what Unit 07's decision bought, and it should not be three clicks deep.

*Why.* What makes separation logic a different logic is what it cannot do. Presenting the failures
as one exercise among eight, and omitting one of them entirely, teaches `∗` as "conjunction with a
side condition".

## G.5 Exactness becomes a three-stage thread instead of an announcement

**Edition 1.** `00-overview.js` presents `ptsAtLeast` versus `ptsExactly`, the two-cell
counterexample and the `afterFree` refutation — all excellent, and all in chapter 0, before the
reader has `Heap.erase`, before `Assertion` means anything, and before there is any free rule to be
false. M3 re-announces the decision; M7 re-announces it again as "where the exactness of `↦` from M3
pays for itself".

**Edition 2.** Three stages, each adding something, none repeating. **Unit 07** *poses* it, as a
question about heaps, reachable because Unit 06 has just proved `erase_singleton`. **Unit 13**
*decides* it, as the definition of `pointsTo`. **Unit 23** *justifies* it, by making `hoare_free` a
theorem and pointing at exercise `x18` by name for what would otherwise be false.

*Why.* A thread that advances is a story; the same claim made three times is the looping the client
objected to. The test applied throughout: *does this mention of X add something X did not have?*

## G.6 `pure` moves after `∗`, because it cannot be motivated before it

**Edition 1.** `04-m3.js` introduces `fact` and `pure` together and justifies the distinction with
a forward reference — *"`pure` pairs with `∗` (`∗` splits the heap, so the left piece must be
empty)"* — to a connective defined in the next chapter. The reader is asked to accept a distinction
whose criterion does not exist yet.

**Edition 2.** `fact` is introduced in Unit 12 with the classical connectives, where it is simply
the trivial lifting of a proposition and needs no justification. `pure` arrives in **Unit 17**,
after `∗`, as the answer to a question the reader can now ask: *what is the `∗`-analogue of
conjoining a proposition?* The answer is then derivable rather than asserted, and
`star_pure_left`/`star_pure_right` prove it.

*Why.* This is the cleanest example of the organising principle: same material, same theorems, moved
four units later, and the forward reference disappears.

## G.7 The PCM becomes an object, not a slogan

**Edition 1.** `03-m2.js` states that heaps form a partial commutative monoid, and a `note
kind:key` says *"Separating conjunction is not 'a connective about heaps'; it is **the connective
induced by any PCM**."* Both claims are true and neither is checkable. There is no monoid anywhere
in `corpus.lean`; nothing is ever instantiated; no law is ever proved generically. `16-ref.js`
repeats the claim as the course's final and most emphasised takeaway.

**Edition 2.** Unit 10 defines `structure PCM` and instantiates `heapPCM` — every field is a
theorem the reader has just proved, so the instantiation is a five-minute exercise that
retroactively explains why each law carried the hypotheses it did. Unit 38 defines `pcmStar` over an
arbitrary PCM and proves `pcmStar_comm` and `pcmStar_unit_left` **from the four fields only**. The
reader compares Unit 15's `star_comm` with Unit 38's `pcmStar_comm` line by line and finds the same
proof with `union_comm` replaced by `K.op_comm`. Unit 10 additionally proves `union_cancel_left`, so
Unit 38 can say what does **not** generalise. All verified, no Mathlib, no `class`, no typeclass
inference.

*Why.* The course's most important closing claim was the one thing in it that was not machine
checked. Making it a theorem costs about forty lines and converts the final unit from a survey into
an exercise.

## G.8 A whole unit for induction, instead of introducing it inside the hardest proof

**Edition 1.** `induction` first appears in `06-m5.js` at exercise `m5-2`, `exec_deterministic`,
which is `hard: true`, has ten cases, and needs `generalizing`. The hint says: *"`induction h₁
generalizing s₂`, then in each case `cases h₂`. The `generalizing` is essential."* That is the
reader's first `induction` in the course — on a *derivation*, with a *generalised hypothesis*, in a
*ten-case* proof.

**Edition 2.** Unit 20 exists for this. Three verified warm-ups first: `allZeros_length` (on `Nat`),
`append_nil` (on `List`), `exec_id` (on a derivation, explicitly labelled *deliberately pointless —
look at the goals, not at the proof*). Then `exec_deterministic`, with `generalizing` as the unit's
lesson rather than a parenthetical, and the ten cases classified into three shapes. The warm-ups
were chosen so that **no goal is an arithmetic identity** — `omega` and the `Nat.add_succ` family
stay out of the course, because the corpus never needs them and a tactic introduced for a warm-up is
a ledger entry forever.

*Why.* This is the course's steepest cliff and Edition 1 puts no steps on it. The technique recurs
in Units 26, 33 and 36, so the investment amortises.

## G.9 A five-unit Lean runway replaces a four-exercise warm-up

**Edition 1.** M0 introduces "a small, honest tactic vocabulary" as a *list of thirteen names in one
paragraph* and never drills eleven of them; worse, it *opens* with `Decidable` instances, stuck
`Nat.beq` matches, and the difference between a simproc and a lemma — material presupposing
typeclasses, instance resolution and reduction. By M2 the reader is expected to read
`rcases hd l₁ with h | h <;> · rw [singleton_same] at h; exact absurd h (by simp)` — five constructs,
none introduced.

**Edition 2.** Units 00–04 plus two support pages, seventeen exercises, every tactic introduced with
a drill before use. The `Decidable` material moves to Unit 02, where `Option` and `if` are being
built and the reader has the context to absorb it. **Every example in the module is a shard of the
model or of the problem** — Unit 00 refutes the aliasing postcondition, Unit 01's `exists_mono` is
`aExists_mono` in disguise and its `nested_pack` is the shape of `star`, Unit 02 builds `Heap`
itself, Unit 04's `update` is `Heap.write` with `Option` removed — so the module is not a detour.

## G.10 Failure gets a page instead of thirty asides

**Edition 1** is unusually good at showing real errors, but each appears as a `detail` inside an
exercise, so the skills never consolidate and a reader stuck at 2am has nowhere to look.

**Edition 2** has the `errors` support page: twelve real messages indexed by their first three
words, the shrink-a-failure loop, `simp?`/`exact?` and their real limits, the orientation rule, and
the standing rule that a tactic not in the `tactics` index does not exist here — which matters
enormously in a Mathlib-free environment.

## G.11 Nine labs exist, with a fixed four-part format

**Edition 1** has no page whose job is *doing*. Exercises are scattered through expository
chapters, so a reader who wants to practise has nowhere to go and a reader who wants to read is
interrupted. Edition 2 separates them: Units 04, 06, 11, 15, 21, 30, 33, 37 are labs, with the
format in §C.1 and a worked example that is the largest block on the page.

## G.12 Locality is proved for `ite` and `loop`, so the frame rule applies to real programs

**Edition 1** proves `HeapLocal` for `skip`, `assign`, `load`, `write`, `free` and `seq`, and stops.
Its frame rule therefore cannot be applied to any program containing a conditional or a loop. The
gap is invisible only because M9's examples are loop-free and M13's loop example touches no heap.
`heapLocal_ite` and `heapLocal_loop` are new and verified, and they are what makes Unit 37's
`drain_spec` possible.

## G.13 The two open ends are closed, and the course ends with a proof

- **`swap_spec` ships unfinished in Edition 1.** `m9-4` in `content/10-m9.js` has a `goal` field
  that is a commented-out signature and a `sol` field containing `preserves_load_fact` plus a
  *comment* describing the remaining work. `README.md`'s "75 exercise solutions" is therefore 74
  plus a helper. Edition 2 completes it (Unit 30, verified, thirty lines, no new syntax) and
  presents both routes with a rule for choosing.
- **`self_disjoint_empty` is cited and does not exist.** `05-m4.js` says in body prose *"M2's
  `self_disjoint_empty` says…"*; grepping `corpus.lean` returns zero matches — the lemma exists only
  inside the `variants` prose string of `m2-2`. Edition 2 promotes it to a verified exercise
  (`self_disjoint_iff_empty`, Unit 08), strengthened to an `↔`, because Unit 14 needs it.
- **Edition 1's last two chapters are an apology and four empty exercises.** M13 admits the
  linked-list capstones are not expressible; M14 has four `ex` blocks with empty `goal` and `sol`.
  Edition 2 ends on `drain_spec` — a verified, in-language loop that reads a bound, rewrites a heap
  cell every iteration, and terminates, with invariant *and* variant — and turns the inexpressible
  material into three clearly-labelled Projects with scope estimates. A course should not finish on
  an apology, and an exercise with no solution is not an exercise; it is a suggestion.

## G.14 A better load rule, presented as a design decision

Edition 1's `hoare_load` postcondition `pure (fun σ => σ x = v) ∗ (l ↦ v)` forces a three-step
`entails_trans` chain before *every* subsequent write. That chain is the bulk of `copyCell_spec` and
is why `swap_spec` shipped unfinished. Edition 2 teaches **both** rules (Unit 29) and says why each
exists — the `pure ∗` form as the standard statement and the cleanest demonstration that `pure`
pairs with `∗`, the `aAnd` form because it is what you calculate with — which is exactly the "every
design decision gets its rejected alternative" discipline that Edition 1 applies to `Heap.union` but
not to its own rules.

## G.15 Given code becomes proved code

Nine blocks Edition 1 hands over as finished Lean become exercises: the three `union` lookup lemmas
(M2 says "three tiny lookup lemmas … add them", then gives them), `heapOnly_star`, `storeStable_*`,
`pure_star_regroup`, `aExists_mono`, `partial_of_total`, `readAndFree_framed`. Each is a one-to-
three-line proof drilling exactly the skill the *next* exercise assumes.

## G.16 Lean friction is separated from mathematics, physically

`content/09-m8.js` is the strongest chapter of Edition 1 — the derivation of the missing conjunct
from a stuck goal is genuinely excellent teaching — but its main line carries `trace` blocks whose
`state` fields run to twelve lines of
`{ store := { store := σ, heap := h }.store, heap := … }.heap` projection noise. The mathematics of
`heapLocal_write` is four lines; the bulk of the chapter is projection-stripping. Edition 2 imposes
the **eight-line rule** and the **two-column rule** (both specified in `PEDAGOGY.md` §6): any goal
state longer than eight lines goes in a foldable `detail`, and every unit separates *what is being
proved* from *what Lean requires to prove it*, the second going into `detail` blocks, `pitfall`
fields and `walk` — never into the running argument.

Edition 1's M8 is not padded; it is *undifferentiated*, and the effect on a reader who is also
learning Lean is the same as padding.

## G.17 The interpreter is labelled optional

Edition 1 gives `run`, `run_sound`, `run_mono`, `run_le` and `run_complete` a full third of a
substantial milestone with two `hard` exercises. Nothing later in `corpus.lean` uses any of it, and
the reader has no way to know. Edition 2 marks Unit 21 optional in its first sentence and in the
sidebar, with the verification stated, and fences its four exclusive ledger items (§E.6). Honesty
about the critical path is a service; it also protects the ledger.

## G.18 What deliberately does not change

The core definitions — `Heap`, `Assertion`, `star`, `wand`, `Exec`, `Hoare`, `wp`, `HeapLocal`,
`Preserves`, `HeapOnly`, `StoreStable` — are untouched, as the brief requires. All 127 corpus
theorems survive with their statements and proofs quoted verbatim. Every Edition-1 exercise `id`
and `name` is preserved. Edition 1's real goal states, real error messages, real `simp?` reports and
real `#print axioms` output are all retained: they are the current course's best asset and they were
expensive to produce.

---

# H. RISKS

## H.1 Thirty-nine units is a lot of writing, and the later ones could starve

*Likelihood: high. Severity: high.* The usual failure is that the first ten units are excellent and
the last ten are skeletal — which would be worse than Edition 1, because the hardest material is at
the end.

**Mitigation.** (a) Eight of the thirty-nine are labs with explicit small budgets, and every §D entry
carries a **screens + blocks budget** so an author can tell when they are over. (b) Units 24–28 and
31–34 must not starve and are given the largest budgets. (c) **Drafting order:** write Unit 00
first, then **Unit 28 second** — it is short, its Lean is already verified, and having the payoff
written keeps the opening honest — then the rest in dependency order. (d) The block budgets sum to
roughly 1,000 non-`ex` blocks across 44 files, against Edition 1's ~1,500 across 17; the per-file
load *falls*.

## H.2 Module 0 reads as a Lean tutorial and the reader loses the plot

*Likelihood: high. Severity: fatal if it happens.*

**Mitigation.** Every object in Module 0 is a shard of the model or of the problem, and each unit
ends by naming the later unit that consumes it. Unit 00 opens on the aliasing problem and on the
promissory note, so the reader knows what they are heading for before the first `fun x =>`. Unit 01's
`nested_pack` is labelled "this is the shape of `star`; you will meet it for real in Unit 14".
Unit 04's retrospective ends by pointing at `update_comm`'s single use of `hne` and saying: *that
line is the frame rule.*
**Detection:** if an author writing Unit 01 cannot name the later unit each exercise serves, the
exercise is wrong. **Fallback:** merge Units 01 and 02 and move `show`/`congrArg` into Unit 03.

## H.3 Forty-four files is an engineering load, and `gen-contexts.mjs` is the failure point

Each unit needs a `content/NN-id.js`, a `<script>` tag in `index.html` in the right position, a
prelude, a `baseline.json` entry, and regenerated per-exercise contexts. `gen-contexts.mjs` maps
each exercise id to how much of `corpus.lean` precedes it, cut **before** that exercise's own
solution; getting it wrong makes Lean answer "already been declared" instead of checking the
reader's proof. Edition 2 moves 73 corpus exercises between files and adds 75 new ones.

**Mitigation.** Generate the preludes mechanically by splitting an extended corpus at the unit
boundaries listed in §D's **corpus** fields — that is a script, not judgement. Run
`node tools/validate.js`, `--strict`, `render-check.js`, `gen-contexts.mjs` and
`node --stack-size=60000 tools/check-all-exercises.cjs` **on every unit as it lands, not at the
end**. Budget roughly double the CI time (148 solutions against 75).

## H.4 The new Lean is verified per-prelude but not yet in corpus order

Each of the eleven `site/lean/edition2/new-*.lean` files compiles against its stated prelude. They
have **not** been concatenated into a single extended corpus.

**Mitigation — a prerequisite task, before any unit is authored.** Build `corpus-v2.lean` by
splicing the new declarations into course order and run `lean corpus-v2.lean`. Three specific
hazards, all already found and fixed once during planning: `erase_erase` is declared twice across
the two source files that were merged into `new-m1.lean`; `wp_frame` was declared twice across the
two sources merged into `new-m12.lean`; and `heapLocal_loop_aux` uses `rename_i s s' s''`, which
shadows outer names harmlessly in isolation but must be re-checked in context.

## H.5 `site/lean/prelude/m13.lean` does not compile

Confirmed: `lean prelude/m13.lean` reports `` `Cmd` has already been declared `` at line 1278 and
`unexpected end of input`. Anything for Units 35–37 checked against it will produce spurious errors.

**Mitigation.** Fix the prelude — delete the trailing M14-flavoured `Cmd` redeclaration and the
unterminated `hoare_load'` (everything from line 1278) — as a prerequisite task. Until then, check
Units 35–37 snippets against `prelude/m13.lean` truncated to line 1277, as `new-m13.lean` was.

## H.6 Chapter ids change, so deep links break

Reader progress is keyed on exercise ids and those are preserved (§F). But `#m4` in the URL is a
permanent link to a chapter, and Edition 2's chapter ids are all new.

**Mitigation.** Add a redirect table in `app.js` from the seventeen Edition-1 chapter ids to the
unit that inherits each one's opening material (`m0` → `update`, `m1` → `heap`, `m2` → `disjoint`,
`m3` → `assertions`, `m4` → `star`, `m5` → `language`, `m6` → `hoare`, `m7` → `small-footprint`,
`m8` → `locality`, `m9` → `symbolic`, `m10` → `listrep`, `m11` → `wand`, `m12` → `wp`,
`m13` → `partial`, `m14` → `beyond`, `overview` → `aliasing`, `ref` → `ref`). Fifteen lines, and it
keeps every bookmark alive.

## H.7 Units 25 and 26 are both majority-hard and back to back

`heapLocal_write`, `heapLocal_free` and `heapLocal_loop` are three of the five hardest proofs in the
course.

**Mitigation.** Unit 26 opens with `heapLocal_ite`, which is genuinely easy and looks like
`heapLocal_seq`, before the loop case. Unit 25's two exercises are each decomposed into two named
obligations that can be proved separately as `have`s, and that decomposition is the unit's main
teaching device. **Fallback if testing still shows a wall:** supply the disjointness half of
`heapLocal_free` and make only the heap equation an exercise.

## H.8 The ledger drifts

Unit authors see only this plan plus summaries of preceding units, so a tactic used casually in Unit
22 that was never introduced is exactly the Edition-1 failure reproduced.

**Mitigation.** (a) §E is normative, and every author's output summary must include the line
"tactics and syntax used that are not at or above my ledger row: none", or the list. (b) **A
mechanical check that does not yet exist and should be written before authoring begins:** extract
every identifier from every `code.src`, `ex.sol`, `walk[].tac` and `trace.steps[].tac` field, diff
against the ledger prefix for that unit, and fail the build on a new one. It is roughly eighty lines
in `tools/validate.js` and it is the highest-value piece of tooling in the project — it is also the
check that would have caught `self_disjoint_empty`.

## H.9 The "nothing left hanging" rule degenerates into padding

The client named both failure modes: padding is bad, and so is compression that leaves the reader to
reconstruct the argument.

**Mitigation.** The per-unit **one job** and **hook** fields are the test. A paragraph that does not
serve the one job and does not set up the hook goes in a `detail` or goes away. The banned-phrase
list in `PEDAGOGY.md` §4 is mechanical and greppable. The `detail` test is retained and is the
acceptance criterion: *the main text must read straight through with every aside closed; if closing
an aside leaves a hole, its content belongs in the main text.*

## H.10 The eight-line rule could produce dishonest goal states

"Show a `show`-cleaned state instead of the raw one" is one step from "show a tidied-up state",
which is precisely the failure `PEDAGOGY.md` warns about.

**Mitigation.** The rule is mechanical, not editorial: the `show` **must appear in the displayed
tactic sequence**, and the state shown must be the output of `goalstate.sh` *after* that `show`.
Nothing is elided — a tactic was added, in the open, and the reader can type it. The raw pre-`show`
state goes in the adjacent `detail`, so it is available and not hidden. Unit 25's `heapLocal_write`
is the test case and should be written first as the template.

## H.11 Eleven design [G] exercises are unmarkable

"State and prove X" has many correct answers, and the checker compiles one specific theorem.

**Mitigation.** Every [G] exercise ships with (i) the statement the reader is expected to arrive at,
revealed at hint rung 3, and (ii) a `variants` field naming two *other* correct statements and
saying what each buys. The editor checks the reader's own text, so a reader who states it
differently and proves it still gets a green tick — which is the correct behaviour and should be
said on the page.

## H.12 The Mathlib-free environment will bite an author who forgets

`set`, `omega`, `linarith`, `decide` on non-trivial propositions and `Function.funext_iff` are all
unavailable; `exact?` is present but weak.

**Mitigation.** Every snippet goes through `site/tools/goalstate.sh` before it goes in a unit; §E is
the whitelist; the `errors` page makes the constraint explicit to the reader so it never looks like
a bug.

## H.13 `wp` and `wand` could still feel bolted on

They are late, they are short, and nothing after them uses them. In Edition 1 they read as two
isolated essays.

**Mitigation.** Both are motivated from a question the reader demonstrably has: after Unit 30 they
have chosen four intermediate assertions by hand and asked "can these be computed?" — that is `wp`;
after Unit 33 they hold a list with its tail removed and ask "is there a connective for what is
missing?" — that is `-∗`. Both questions are asked out loud in the preceding unit's hook. **If a
reviewer cannot feel those questions arriving, the units are in the wrong place**, and the
alternative placement is `wp` immediately after Unit 27 (so `wp_seq` can be contrasted with
`hoare_seq` while it is fresh). The plan keeps `wp` where it is because a predicate transformer put
in front of a reader who has not yet found intermediate assertions painful is a definition with no
question attached.

## H.14 Fifteen new exercises are specified but not yet verified

The rows marked ⧗ in §F: `x01`, `x06`, `x08`, `x09`, `x10`, `x11`, `x12`, `x26`, `x29`, `x30`,
`x47`, `x48`, and the refutation half of `x15`.

**Mitigation.** All are shallow — one-liners over `Prop`, `Nat` or a two-command program — and every
one sits in a unit whose surrounding Lean is verified, so the preludes are known good. **The rule is
absolute and is a hard sequencing constraint on the authoring agents, not a suggestion: no unit may
be authored until its "new Lean needed" row is compiled and added to the extended corpus.** Nothing
is tagged `verified` that is not literally in `corpus.lean`; new Lean is tagged `illustration` only
after compiling against the chapter prelude via `goalstate.sh`; deliberately incomplete code is
tagged `sketch`.

## H.15 The sidebar becomes unusable at 44 entries

**Mitigation.** Group by module and collapse; only the current module is expanded. This is a change
to `app.js`'s sidebar rendering and is the one engineering task this plan requires outside content.
Estimate: small. If it is not done, the course still ships — the `phase` field already groups the
units — but per-unit progress tracking and per-unit deep links are worth having.

---

# I. HANDOVER — WHAT EACH AUTHOR GETS AND MUST RETURN

Each unit author receives: this plan, the summaries of all preceding units, `AUTHORING.md`,
`PEDAGOGY.md`, `lean/corpus.lean` and `lean/edition2/`.

**Before writing.**
1. Read your unit's §D entry and the **hook** of the preceding unit. Your first paragraph answers
   that hook. No summary of the previous unit, no "recall that", no section called "The idea".
2. Consult §E. Anything at or above your row is known and is used without ceremony. Anything below
   it is forbidden.
3. Compile every ⧗ item in your "new Lean needed" row and add it to the extended corpus **before**
   writing prose.
4. Get every goal state from `site/tools/goalstate.sh`. Never write one from memory.

**Each author must return, alongside the unit file:**
1. **The unit summary** — three sentences: what was established, what was left open (verbatim your
   `hook` field), and what the next unit may now assume.
2. **The ledger line** — "tactics and syntax used that are not at or above my ledger row: none", or
   the list.
3. **The goal-state provenance line** — the `goalstate.sh` invocation that produced every `trace`
   and `state` block in the file. No block without one.
4. **The Lean status line** — which blocks are `verified` (byte-for-byte in `corpus.lean`), which
   `illustration` (compiled against the prelude), which `sketch`. Any `verified` claim not literally
   in `corpus.lean` is a build failure.
5. **The checks** — `node --check`, `node tools/validate.js`, `--strict`,
   `node tools/render-check.js`, `node tools/gen-contexts.mjs`, all green.
