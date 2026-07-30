# How this course is written

## The reader

A **professional mathematician** who is a **beginner in Lean**.

They are not confused by partial functions, monoids, induction, fixed points,
or "the least relation closed under these rules". Never explain those.

They *are* confused by everything Lean-specific and everything
separation-logic-specific — not because it is hard, but because nobody has told
them. Why `funext` is needed when the two functions are obviously equal, what
`simp` actually did, what `case pos` means, why `Option` rather than a subset of
the domain.

**Assume mathematical maturity. Assume zero Lean fluency.**

## The shape: one story, told once, moving forward

This is the part that matters most, and the part the first draft of this course
got wrong.

The course is **a single narrative read in order**, not seventeen essays about
related topics. A reader starts at the beginning and arrives at the end having
watched one idea grow. Concretely:

**Every chapter opens where the last one closed.** Not with a summary of it — by
picking up the thread. The previous chapter ended with a question, a limitation,
or a thing that almost worked; this chapter is what happens next. If you cannot
say in one sentence what unfinished business you are inheriting, you do not yet
know how to start.

**Nothing is explained twice.** Each author is given a ledger of every concept,
notation, tactic and lemma already introduced. Anything on that ledger is
*already known* and is used without ceremony. No "recall that", no "as we saw in
M4", no re-derivation. If a reader has forgotten, the search box and the notation
drawer exist; the prose does not stop for them.

**Each idea appears once, in the place it is needed.** Do not mention a concept
in passing three chapters early "for motivation" and then define it properly
later. That is the looping the reader complained about: the same material
circled repeatedly, never landing. Introduce a thing when the story needs it,
completely, and then rely on it.

**Motivate from the problem, not from the history.** The reader does not need to
know who invented what or in which order the field developed. They need to see a
concrete difficulty, feel why the obvious fix fails, and then meet the
definition that resolves it. Definitions arrive as *answers to questions the
reader is already asking* — never as a list to be memorised before use.

**Each chapter has one job.** State it to yourself in a sentence. Anything that
does not serve it goes in a foldable aside, or goes away.

## Depth without derailment: the foldable aside

Use `{t:'detail', title:'…', blocks:[…]}` for anything that is genuinely
interesting but would break the line of the argument:

- the Lean subtlety that only bites in one corner case
- the alternative definition and exactly what it costs
- the proof of a side lemma the main thread only needs the statement of
- the "what if we tried it the other way" digression

The main text must read straight through with every aside closed. If closing an
aside leaves a hole, its content belongs in the main text. If opening it feels
like a reward, it is in the right place.

## Prose rules

**No empty phrases.** Cut "it is important to note that", "as we will see",
"let us now turn to", "in this section we will", "it is worth mentioning".
Say the thing.

**No paragraph that only announces another paragraph.** Section headings already
say what is coming.

**No sentence that restates the previous sentence in different words.** This was
the single most common defect in the first draft.

**Short sentences carry the load.** Direct, second person, unpadded, no
cheerleading. When a sentence can lose a clause and keep its meaning, lose it.

**Every claim is load-bearing.** If a sentence would not change what the reader
does or believes, delete it.

## What "detailed" means here

Not longer. Denser in the right places.

**Every tactic is introduced once, where it first appears**, with what it does
to the goal — before and after — and why that is the natural move. After that it
is used freely. The ledger says what has already been introduced; trust it.

**Every proof longer than two tactics gets a `trace` block** showing the goal
state at each step. A written-out Lean proof is a transcript with the interesting
part deleted. Put it back.

The goal states must be **real**. Get them from Lean:

```bash
site/tools/goalstate.sh m1 /tmp/snippet.lean     # trace_state prints the goal
```

Never invent one. A plausible-looking wrong goal state is worse than none,
because the reader will trust it and then be confused when Lean disagrees.

**Every design decision gets its rejected alternative.** `Heap := Loc → Option
Val` is a choice. Exact ownership rather than "at least this" is a choice.
Left-biased union is a choice. Say what the alternative was and what breaks
under it — a definition without its alternatives cannot be reconstructed.

**Every rule that could be broken gets broken.** Show the counterexample.

**Translate register explicitly** when Lean forces something paper does not:

> On paper you would write "the two heaps are disjoint, so define their union".
> Lean will not let you: `Heap.union` has to be total, or every later rewrite
> carries a disjointness proof around. So union is defined for all pairs,
> left-biased, and disjointness is a separate hypothesis at the point of use.
> That is why the lemmas below all take an explicit `hd : disjoint h₁ h₂` that
> on paper would be invisible.

## Exercises

Each is a small lesson, not a quiz.

- `why` — what this buys you, pointing forward.
- `hints` — graded. First a nudge, last nearly the answer. A reader stuck at 2am
  climbs out one rung at a time without seeing the solution.
- `walk` — every line of the solution, saying what that line *did to the goal*.
  Not a paraphrase of the syntax.
- `deep` — a `trace` with real goal states, plus whatever else it deserves.
- `pitfall` — the mistake a reader will actually make. If the hypothesis is
  `x ≠ l` and writing `l ≠ x` makes `simp` fail, say so, and say the fix.
- `variants` — what happens if a hypothesis is dropped or reversed. Often the
  theorem becomes false at exactly one point; name that point.

## The hard constraint

**All Lean is fixed and machine-checked.** Definitions, theorem statements and
proofs are quoted verbatim from `lean/corpus.lean`, which compiles clean under
Lean 4.32.2 with no imports and no Mathlib. Never edit them — not to rename a
variable, not to reindent. If you believe a proof is wrong, say so in prose and
leave the code alone.

New Lean you write yourself must compile against the chapter prelude and be
tagged `illustration`, or `sketch` if deliberately incomplete. `verified` is
reserved for text literally in the corpus.

Exercise `id` and `name` never change: reader progress is stored against them.
