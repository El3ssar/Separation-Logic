# How this course is written — Edition 2

This replaces the first-edition style guide. It is a set of rules, most of them checkable. Where a
rule has a *before* and *after*, the *before* is real text from Edition 1.

The companion documents are `COURSE-PLAN.md` (what each unit contains, and the ledger of what may
be used where) and `AUTHORING.md` (the block schema). This file is about **how to write**.

---

## 1. The reader

Someone with **ordinary undergraduate mathematical maturity** and **no Lean at all**. They are
learning both subjects at once. That is the whole design constraint.

**Assumed, and used without ceremony:** functions and composition; sets, subsets, disjointness of
sets; binary relations and their properties; induction on the natural numbers; proof by cases;
`∧ ∨ ¬ → ↔ ∀ ∃` as notation; what a counterexample is; that a definition is a *choice*.

**Not assumed. Introduce it, in the unit whose story needs it, before it is used:** anything at all
about Lean; partial functions and their `Option` encoding; definitional versus propositional
equality; decidability; function extensionality as a rule; monoids and partial commutative monoids;
weakening, contraction and substructural logic; inductively defined relations; structural induction
and generalisation of the induction hypothesis; big-step operational semantics; Hoare logic;
locality; least fixed points; adjunctions; predicate transformers; loop invariants and variants.

Edition 1's instruction — *"A **professional mathematician** who is a beginner in Lean. They are
not confused by partial functions, monoids, induction, fixed points… **Never explain those.**"* —
is **repealed**, together with `AUTHORING.md` house rule 2 (*"Explain the Lean, not the mathematics
the reader already knows"*). Explain both. In the right place, once.

The consequence, concretely. Edition 1's M2 says:

> **Before.** *"What we are about to prove is that heaps form a **partial commutative monoid**
> (PCM): a set with a partial binary operation `·` and a unit `e` such that, whenever both sides
> are defined, `(a·b)·c = a·(b·c)`, `a·b = b·a`, and `e·a = a`."*

That is a definition of a monoid smuggled into a subordinate clause, for a reader who may never
have met one, announcing something not yet done. Edition 2's Unit 10 defines *monoid* with
`(Nat, +, 0)` and `(List, ++, [])` as the two examples the reader already knows, then adds
*commutative*, then adds *partial* — and then makes the reader **build the structure in Lean and
instantiate it**, so the word denotes an object they can `#check`.

---

## 2. The shape: one story, told once, moving forward

**Every unit opens where the last one closed.** Not with a summary of it — by picking up the
thread. The previous unit ended on a `hook`: a question, a limitation, or a thing that almost
worked. Your first paragraph answers it. `COURSE-PLAN.md` gives you both fields; they are
contractual.

**Banned opening: a heading called "The idea".** Nine of Edition 1's seventeen chapters open with
it, and the heading is the symptom — it announces an essay, not a next step.

> **Before.** `h3: The idea` / *"Separation logic needs one thing from its model: a way to say
> 'this resource splits into these two independent pieces'. For heaps that means two definitions."*
>
> **After.** *"We can say that two heaps do not overlap. We still cannot combine them — and
> 'the heap splits into these two pieces' needs both halves of that sentence. Combining them is one
> definition, and it is not the one you would write on paper."*

**Nothing is explained twice.** §E of `COURSE-PLAN.md` is a ledger of every concept, notation,
tactic and lemma with the unit that introduces it. Anything at or above your row is *already known*
and is used without ceremony. No "recall that", no "as we saw in M4", no re-derivation. If a reader
has forgotten, the search box, the notation drawer and the `tactics` index exist; the prose does not
stop for them.

**Nothing is used before it is introduced.** Anything *below* your row does not exist yet. This is
the rule the first edition broke most often: by M2 the reader is expected to read
`rcases hd l₁ with h | h <;> · rw [singleton_same] at h; exact absurd h (by simp)`, in which five
constructs appear that were never introduced. If you need something that is not on the ledger at or
above your row, you have found a plan bug — say so, do not smuggle it in.

**Each idea appears once, in the place it is needed.** Do not mention a concept three units early
"for motivation" and then define it properly later. Edition 1 dissects the definition of `∗` in an
`anat` block in chapter 0 and then dissects it again in an `anat` block in chapter 5, 300 KB later,
having posed the question it answers in neither place. In Edition 2 there is exactly one `anat` on
`star`, in the unit that needs it.

**Motivate from the difficulty, not the history.** No dates, no attributions in the main text; at
most one sentence per module, in a `detail`. The reader needs to see a concrete difficulty, feel why
the obvious fix fails, and then meet the definition that resolves it. Definitions arrive as
*answers to questions the reader is already asking*.

**A thread may return only if it advances.** The test: *does this mention of X add something X did
not have?* Exactness is mentioned three times in Edition 2 — Unit 07 *poses* it, Unit 13 *decides*
it, Unit 23 *justifies* it. That is a story. Edition 1 announces it in chapter 0 and re-announces
it twice. That is the looping the client objected to.

**Each unit has one job.** It is stated in `COURSE-PLAN.md` in one sentence. Anything that does not
serve it goes in a foldable aside, or goes away.

---

## 3. Register and voice

Write like an excellent lecturer talking a capable student through the subject: **paced, motivated,
worked, with the reasoning visible — and zero filler**.

- Second person. Direct. Present tense.
- Short sentences carry the load. When a sentence can lose a clause and keep its meaning, lose it.
- No cheerleading, no exclamation marks, no "beautifully", "elegantly", "of course", "simply",
  "just", "obviously". If it were obvious the reader would not be reading.
- Every claim is load-bearing. If a sentence would not change what the reader does or believes,
  delete it.
- **Name the moving part.** "This is where non-aliasing enters" beats "now we apply the
  hypothesis".
- **Say what would go wrong.** A rule the reader cannot break is a rule they have not understood.

Both failure modes are real and both are rejected. Padding is bad. So is compression that leaves
the reader to reconstruct the argument — Edition 1's characteristic defect is a series of clipped
assertions where a worked explanation belongs. The cure for compression is *more steps*, not more
words: a `steps` block, a `trace`, a `cmp`, an intermediate goal state.

---

## 4. Banned phrases and constructions

Cut on sight. This list is greppable and reviewers should grep it.

| banned | why |
|---|---|
| "It is important to note that…", "It is worth noting/noticing that…", "Note that…" | if it were not worth noting you would not have written it |
| "As we will see", "as we saw", "later we will", "in the next chapter we will" | either say it now or leave it to its own unit |
| "Let us now turn to", "In this section we will", "We now show that" | headings already say what is coming |
| "Recall that", "As is well known", "Obviously", "Clearly", "Of course" | the ledger says what is known; the rest must be explained |
| "The idea" as a heading | announces an essay instead of continuing the argument |
| "Two remarks about X, both important." | a paragraph whose only content is that another paragraph follows |
| "simply", "just", "merely" applied to a proof step | if it were simple the reader would have found it |
| "beautiful", "elegant", "powerful", "the magic of" | cheerleading |
| a sentence restating the previous sentence in different words | the single most common defect in Edition 1 |

Real examples, with repairs.

> **Before** (`05-m4.js`, `expl` of `m4-6`): *"In `star_exists_left` the witness `x` simply travels
> from the hypothesis to the goal; the heap cut is unchanged. **It is worth noting that** the
> reverse direction also holds and is equally easy — unlike the `∀` case, where only one direction
> is provable."*
>
> **After:** *"The witness `x` travels from the hypothesis to the goal and the heap cut is
> unchanged. The reverse direction holds too, by the same three lines — which is not automatic: for
> `∀` only one direction is provable, and the reason is the order of the quantifier and the cut."*

> **Before** (`13-m12.js`): *"**It is worth noticing that** determinism is *not* used."*
>
> **After:** *"Determinism is not used. The equation holds for nondeterministic languages too,
> provided `wp` is read angelically — *there exists* a terminating run landing in `Q` — rather than
> demonically."*

> **Before** (`03-m2.js`): *"Two remarks about the definition of `union`, both important."*
> followed by a two-item list.
>
> **After:** delete the sentence. The list is the content.

> **Before** (`00-overview.js`, `orient.needs`): *"Partial functions, monoids, induction,
> inductively defined relations. All assumed. None of it explained."*
>
> **After:** that field now lists what the reader must have *proved* to start this unit, and every
> item in the old list is taught somewhere in the course. See `COURSE-PLAN.md` §A.1.

---

## 5. Depth without derailment: the foldable aside

Use `{t:'detail', title:'…', blocks:[…]}` for what is genuinely interesting but would break the
line of the argument:

- the Lean subtlety that only bites in one corner case;
- the alternative definition and exactly what it costs;
- the proof of a side lemma the main thread only needs the statement of;
- a goal state longer than eight lines (§6);
- the "what if we tried it the other way" digression;
- the one sentence of history, if a module needs one.

**The test.** The main text must read straight through with **every aside closed**. If closing an
aside leaves a hole, its content belongs in the main text. If opening one feels like a reward, it
is in the right place.

**At most one `detail` before the first exercise of a unit.** Everything else moves after the
exercise it illuminates. Edition 1's M2 spends three paragraphs and two `detail` blocks on the
weakest-hypothesis question before the reader has proved a single lemma about disjointness.

---

## 6. Lean friction versus mathematics — keep them apart

Edition 1's M8 is its best chapter and also its clearest failure of this rule: the derivation of the
missing conjunct from a stuck goal is genuinely excellent teaching, but the main line carries
`trace` blocks whose `state` fields run to twelve lines of

```
{ store := { store := σ, heap := h }.store,
  heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap
```

The mathematics of `heapLocal_write` is four lines; the bulk of the chapter is
projection-stripping. That chapter is not padded — it is **undifferentiated**, and the effect on a
reader who is also learning Lean is exactly the same as padding.

Two mechanical rules.

**6.1 The eight-line rule.** Any goal state longer than eight printed lines goes in a foldable
`detail`. The main-line `trace` shows a real state obtained by first running `show` to put the goal
in readable form. The `show` **must appear in the displayed tactic sequence** and the state shown
must be `goalstate.sh`'s output *after* it. Nothing is elided: a tactic was added, in the open, and
the reader can type it. The raw pre-`show` state goes in the adjacent `detail`, so it is available
and not hidden.

**6.2 The two-column rule.** Separate *what is being proved* from *what Lean requires in order to
prove it*. The second goes in `detail` blocks, in `pitfall` fields, and in the `walk` of an
exercise — never in the running argument. A reader learning both subjects cannot otherwise tell
which sentences are which.

**Translate register explicitly** when Lean forces something paper does not:

> On paper you would write "the two heaps are disjoint, so define their union". Lean will not let
> you: `Heap.union` has to be total, or every later rewrite carries a disjointness proof around. So
> union is defined for all pairs, left-biased, and disjointness is a separate hypothesis at the
> point of use. That is why the lemmas below all take an explicit `hd : disjoint h₁ h₂` that on
> paper would be invisible.

---

## 7. What "detailed" means here

Not longer. Denser in the right places.

**Every tactic is introduced once, where the ledger says**, with what it does to the goal — before
and after — and why that is the natural move. After that it is used freely.

**Every proof longer than two tactics gets a `trace` block** showing the goal state at each step. A
written-out Lean proof is a transcript with the interesting part deleted. Put it back. Budget: one
`trace` per exercise in `deep`, at most six steps, and a second only where two branches genuinely
differ. The rule is *show the state at each point where the reader would guess wrong*, not *show
every state*.

**Every design decision gets its rejected alternative.** `Heap := Loc → Option Val` is a choice.
Exact ownership rather than "at least this" is a choice. Left-biased union is a choice. The shape of
the load rule's postcondition is a choice. Say what the alternative was and what breaks under it — a
definition without its alternatives cannot be reconstructed.

**Every rule that could be broken gets broken.** Show the counterexample, in Lean, verified.

**Every claim about the subject that can be a theorem should be one.** Edition 1 says in a `note`
that `P ∗ Q ⊢ P` is false and that separating conjunction is the connective induced by any PCM.
Both are true; neither was checkable. In Edition 2 the first is exercise `x33` and the second is
exercise `x74`.

---

## 8. Exercises

Each is a small lesson, not a quiz. Every `ex` block carries all of the following. An exercise
missing any of them is not finished.

- **`why`** — what this buys you, pointing forward, naming the later unit or theorem it serves.
- **`hints`** — graded, **four rungs, always the same four**:

  | rung | job |
  |---|---|
  | 1 | **Restate the goal.** Say what the goal *is*, unfolded, with no strategy. A reader who cannot start has often simply misread it. |
  | 2 | **Name the shape of the argument**, in mathematics, with no Lean. |
  | 3 | **Name the tactic or lemma**, without arranging it. |
  | 4 | **Give the first line verbatim**, and say what it leaves. |

  Rung 4 is a near-giveaway by design. A reader at 2am who has climbed all four and is still stuck
  should open the solution without guilt, and the `solNote` says so. **Rung 3 never names a lemma
  or tactic that is not on the ledger at or above this unit.**

- **`sol`** — verified Lean, quoted verbatim. See §9.
- **`walk`** — every line of the solution, saying what that line *did to the goal*. Not a
  paraphrase of the syntax. "`funext x` turns an equation between functions into an equation at an
  arbitrary point, and gives you `x` to case on" — not "`funext x` applies function extensionality".
- **`deep`** — a `trace` with real goal states, plus whatever else it deserves.
- **`pitfall`** — the mistake a reader will *actually* make. If the hypothesis is `x ≠ l` and
  writing `l ≠ x` makes `simp` fail, say so, and say the fix. If `obtain ⟨sMid, h₁, h₂⟩ := hex`
  silently drops all three names because they collide with `Exec.seq`'s field names, and the error
  arrives on the *next* line as `Unknown identifier`, say that.
- **`variants`** — what happens if a hypothesis is dropped or reversed. Often the theorem becomes
  false at exactly one point; name that point and give the witness.

**Three kinds of exercise**, and `COURSE-PLAN.md` says which each is.

- **Drill [D]** — mechanical, builds fluency, one to three lines.
- **Construction [C]** — the reader chooses the shape of the proof.
- **Design [G]** — *the reader writes the statement*: "state and prove that updating a point with
  the value already there does nothing." A [G] exercise ships with the statement the reader is
  expected to arrive at (revealed at rung 3) and a `variants` field naming two *other* correct
  statements and what each buys. The editor checks the reader's own text, so a different correct
  statement still gets a green tick, and the page says so.

**Difficulty** is graded 1–5 by *Lean* difficulty, not by separation-logic difficulty — which is why
`m4-1` is a 2 despite being mathematically trivial. 4 and 5 carry `hard: true`.

**Ids and names never change.** Reader progress is stored against them. New exercises use the
`x01`–`x75` namespace, which cannot collide with `mN-k`.

---

## 9. The hard constraint: all Lean compiles

**Nothing is shown to the reader that has not been through Lean.**

- `tag: 'verified'` (the default) means **this exact text occurs in `lean/corpus.lean`**, which
  compiles clean under Lean 4.32.2 with no imports, no Mathlib and no `sorry`. Never edit it — not
  to rename a variable, not to reindent. If you believe a proof is wrong, say so in prose and leave
  the code alone.
- `tag: 'illustration'` means you wrote it and it compiled against the chapter prelude. Compile it
  before you write about it.
- `tag: 'sketch'` means deliberately incomplete or schematic and does not compile alone. Use it
  honestly; do not use it to avoid compiling something.

Never tag something `verified` that you did not check.

**To check a snippet you wrote:**

```bash
cat site/lean/prelude/m6.lean my-snippet.lean > /tmp/t.lean && lean /tmp/t.lean
```

Silence means it compiled. Note that `site/lean/prelude/m13.lean` currently **does not compile** —
it redeclares `Cmd` at line 1278 — so truncate it at line 1277 until that is fixed.

**There is no Mathlib.** `set`, `omega`, `linarith`, `ring`, `simp_arith`, `aesop`, `decide` on
non-trivial propositions and `Function.funext_iff` do not exist here. `exact?` and `simp?` do exist
and are worth teaching, but `exact?` without a library is feeble and the `errors` page shows why.
If a tactic is not in the ledger, it does not exist in this course.

---

## 10. Goal states are real

The most useful thing you can put in front of a Lean beginner is what the goal actually looked
like. Get it from Lean, never from memory:

```bash
cat > /tmp/s.lean <<'EOF'
theorem demo (h : Heap) (l : Loc) (v : Val) :
    Heap.write h l v l = some v := by
  trace_state
  simp [Heap.write]
EOF
site/tools/goalstate.sh m1 /tmp/s.lean
```

```
h : Heap
l : Loc
v : Val
⊢ h.write l v l = some v
```

Paste that into a `trace` or a `state` block, hypotheses first, then `⊢ goal`, newlines preserved.

**Never invent one.** A plausible-looking wrong goal state is worse than none, because the reader
will trust it and then be confused when Lean disagrees.

**Every author must report the provenance of every `trace` and `state` block** — the exact
`goalstate.sh` invocation that produced it — in their handover summary. No block without one.

The same applies to error messages: produce them by breaking a real proof and copying what Lean
said. The `errors` support page is built entirely this way, and it is one of the most valuable
pages in the course precisely because none of it is paraphrased.

---

## 11. Labs

Eight units are labs (04, 06, 11, 15, 21, 30, 33, 37). A lab is **not** a lecture with the prose deleted, and its format is fixed:

1. a one-paragraph **brief** saying what the reader is about to build and where it is spent;
2. a **worked example done in full** — the largest block on the page — with every goal state
   printed by `goalstate.sh`, the tactic named, one sentence on what changed, and one sentence on
   what a reader would plausibly have tried instead and why it fails;
3. the **exercises**, in a strict difficulty ramp, with at most one sentence of prose between them
   saying what is new;
4. a **retrospective**: three questions the reader should now be able to answer, with the answers
   in `detail` blocks.

A lab whose worked example is shorter than its brief has failed and must be rejected in review.

---

## 12. The checklist

Before submitting a unit:

- [ ] The first paragraph answers the previous unit's `hook`. There is no section called "The idea".
- [ ] The unit ends on its own `hook`, exactly as `COURSE-PLAN.md` specifies it.
- [ ] Every tactic, lemma and concept used is at or above this unit's row in the ledger.
- [ ] Every `verified` block occurs byte-for-byte in `corpus.lean`; every `illustration` compiled
      against the prelude; every `sketch` is honestly incomplete.
- [ ] Every `trace` and `state` block came out of `goalstate.sh`, and you can say which invocation.
- [ ] No goal state longer than eight lines sits in the main line.
- [ ] Every exercise has `why`, four graded `hints`, `sol`, `walk`, `deep` with a `trace`,
      `pitfall`, `variants`.
- [ ] At most one `detail` before the first exercise.
- [ ] Grep for the banned phrases in §4. Zero hits.
- [ ] No sentence restates its predecessor. No paragraph announces another paragraph.
- [ ] Every design decision in the unit names its rejected alternative and what breaks under it.
- [ ] `node --check site/content/NN-id.js`
- [ ] `node site/tools/validate.js` and `--strict`
- [ ] `node site/tools/render-check.js`
- [ ] `node site/tools/gen-contexts.mjs`
