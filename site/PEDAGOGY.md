# Who this is written for, and how

## The reader

A **professional mathematician** who is a **beginner in Lean**.

Take both halves seriously, because together they are unusual:

- They are not confused by partial functions, monoids, induction, fixed points,
  quantifier alternation, or "the least relation closed under these rules".
  Never explain those. Explaining them is condescending and wastes the page.
- They *are* confused by everything that is Lean-specific and by everything
  that is separation-logic-specific. Not because it is hard, but because nobody
  has told them. They do not yet know why `funext` is needed when the two
  functions are obviously equal, what `simp` actually did, why `Option` instead
  of a subset of the domain, what `case pos` means, why the anonymous
  constructor `⟨_, _⟩` sometimes takes three arguments, or what the difference
  is between `rfl` and `Eq.refl`.

So the rule is: **assume mathematical maturity, assume zero Lean fluency.**

The failure mode to avoid is a chapter that reads like reference documentation.
The reader can already read reference documentation. What they cannot do is
watch someone think.

## What "very detailed" means here

Not longer. *Denser in the right places.* Concretely:

**Every tactic gets introduced once.** The first time `by_cases`, `obtain`,
`refine`, `<;>`, `funext`, `simp [h]`, `rcases`, `subst`, or `show` appears in
the workbook, the chapter it appears in explains what it does to the goal —
before and after — and why that is the natural move. Later chapters may then
use it freely. If you are not sure whether it has been introduced, check the
earlier chapter sources.

**Every proof longer than two tactics gets a `trace` block.** A written-out
Lean proof is a transcript with the interesting part deleted: the goal state.
Put it back. The goal states must be *real* — get them from Lean:

```bash
site/tools/goalstate.sh m1 /tmp/snippet.lean     # trace_state prints the goal
```

Never invent a goal state. A plausible-looking wrong one is worse than none,
because the reader will trust it and then be confused when Lean disagrees.

**Every design decision gets a reason.** `Heap := Loc → Option Val` is a
choice. Exact ownership rather than "at least this" is a choice. Left-biased
union is a choice. `Hoare` as total rather than partial correctness is a
choice. In each case say what the alternative was and what breaks under it.
A definition without its rejected alternatives is a definition the reader
cannot reconstruct.

**Every rule that could be broken gets broken.** Show the counterexample.
"The frame rule needs locality" is a sentence; "here is a command for which
the frame rule fails, and here is the heap that witnesses it" is understanding.

**Translate register explicitly.** A recurring, very useful move:

> On paper you would write "the two heaps are disjoint, so define their union".
> Lean will not let you, because `Heap.union` has to be a total function — it
> cannot demand a proof of disjointness in its type without making every later
> rewrite carry that proof around. So `union` is defined for *all* pairs,
> left-biased, and disjointness is a separate hypothesis you supply at the
> point of use. That is why every lemma below has an explicit `hd : disjoint
> h₁ h₂` argument that on paper would be invisible.

That paragraph is the kind of thing that is worth ten pages of restating
definitions.

## Exercises

The exercises are the course. Treat each one as a small lesson, not a quiz.

For every exercise, in the fields the schema provides:

- `why` — what this buys you. Point forward: "this is the lemma that makes the
  free rule three lines instead of thirty."
- `hints` — graded. The first is a nudge ("what do you do when both sides are
  functions?"). The last is nearly the answer. A reader stuck at 2am should be
  able to climb out one rung at a time without seeing the solution.
- `walk` — **every line of the solution**, in order, each with a sentence or
  two saying what that line did to the goal. Not a paraphrase of the syntax:
  say what changed.
- `deep` — the real explanation. Usually a `trace` block, plus whatever else
  the exercise deserves: a `cmp` of the naive attempt against the working one,
  a `steps` breakdown of the mathematical argument underneath, a `detail`
  aside on a Lean subtlety.
- `pitfall` — the mistake a reader will *actually* make. Not a generic warning.
  If the hypothesis is `x ≠ l` and writing `l ≠ x` makes `simp` fail, say so,
  and say that the fix is `Ne.symm` or `hne.symm`.
- `variants` — what happens if you drop or reverse a hypothesis. Very often the
  theorem becomes false, and the single point where it fails is the whole
  content of the theorem. Name that point.

## Voice

Match the original workbook: direct, second person, unpadded, no cheerleading,
no "Great question!", no "Let's dive in". Short sentences carry the load.
Em-dashes and semicolons are fine. The original is well written — the problem
it has is that it is *too compressed*, not that it is badly phrased. Expand it;
do not restyle it.

Keep every good sentence the original already has. This is an expansion, not a
rewrite. If the original says something well, it stays, and your new material
grows around it.

## The one hard constraint

**All Lean code is fixed and machine-checked.** Definitions, theorem
statements, and proofs are quoted verbatim from `lean/corpus.lean`, which
compiles clean under Lean 4.32.2 with no imports and no Mathlib. You never edit
them — not to rename a variable, not to fix indentation, not to make a proof
"nicer". If you believe a proof is wrong, say so in prose and leave the code
alone.

New Lean you write yourself (a counterexample, an alternative proof, a `#check`)
is welcome, but it must compile against the chapter prelude and must be tagged
`illustration`, or `sketch` if it is deliberately incomplete. `verified` is
reserved for text that is literally in the corpus.
