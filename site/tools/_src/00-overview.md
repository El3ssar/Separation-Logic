# CHAPTER SOURCE — id=overview  num=§  index=0
phase: Start here
title: What we are building, and why
blurb: The whole picture in one page: the problem separation logic solves, the model we will build, and how to use this workbook.

Blocks below are given in order. Each begins with `@@ <type> [n]`.

@@ h3 [0]
The problem

@@ p [1]
Ordinary Hoare logic works beautifully for programs over variables and breaks down for programs over memory. The reason is one word: <b>aliasing</b>. If <code>x</code> and <code>y</code> are two pointers, the innocent-looking rule

@@ txt [2]
```
{ [x] = 3 }   [y] := 5   { [x] = 3 ∧ [y] = 5 }
```

@@ p [3]
is simply false when <code>x</code> and <code>y</code> happen to point at the same cell. To repair it classically you must carry, everywhere, a growing swamp of side conditions of the form <i>“and these 40 pointers are pairwise distinct”</i>. Proofs stop being about the program and start being about the bookkeeping.

@@ p [4]
Separation logic’s move is to change what an assertion <i>means</i>. Instead of “this is a true statement about the memory”, an assertion says <b>“I own exactly this much memory, and here is what is in it.”</b> Non-aliasing then stops being a hypothesis you carry around and becomes a <i>consequence</i> of the way assertions are combined.

@@ note [5]
kind: key
title: The one thing to remember
Assertions describe <b>ownership</b>, not just truth. From that single change, everything else — the frame rule, local reasoning, recursive data-structure predicates, concurrency — follows.

@@ h3 [6]
What you will actually build

@@ p [7]
A complete, self-contained separation logic in Lean 4, from the empty file. No Mathlib, no Iris, no separation-logic library, no automation beyond what ships with Lean. Everything below is defined and proved by hand:

@@ ul [8]
  - a model of memory as partial functions, with disjointness and union;
  - the proof that heaps form a <i>partial commutative monoid</i> — the algebraic heart of the whole subject;
  - assertions, entailment, and the separating conjunction <code>∗</code> with all of its laws;
  - a small imperative language with a relational semantics <i>and</i> an executable interpreter, proved to agree;
  - Hoare triples, the small-footprint rules for load / write / free;
  - the frame rule, proved as a theorem about the semantics rather than assumed;
  - verified programs: copy, move, deallocate;
  - recursive predicates for linked lists and list segments, with the append theorem;
  - the magic wand and its adjunction with <code>∗</code>;
  - weakest preconditions, and their equivalence with Hoare triples;
  - conditionals, loops, invariants, and a total-correctness variant rule.

@@ note [9]
kind: info
title: These solutions compile
Every Lean proof shown in this workbook has been checked by Lean 4.15.0 in a single 1300-line file. There are no <code>sorry</code>s and no admitted lemmas. Where the solution differs from the naïve statement, the text says exactly why.

@@ h3 [10]
The model, in one screen

@@ code [11]
```
abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val
```

@@ p [12]
A heap is a <b>partial function</b> from locations to values, encoded as a total function into <code>Option</code>. <code>h l = some v</code> means “<code>l</code> is allocated and holds <code>v</code>”; <code>h l = none</code> means “<code>l</code> is not mine / not allocated”.

@@ svg [13]
```

<svg viewBox="0 0 560 168" role="img" aria-label="A heap is a partial function from locations to values">
  <g class="dg">
    <text x="8" y="18" class="dg-lab">locations (Nat)</text>
    <text x="392" y="18" class="dg-lab">values (Nat)</text>
    <g class="dg-dot">
      <circle cx="60" cy="46" r="5"/><text x="26" y="51" class="dg-t">0</text>
      <circle cx="60" cy="80" r="5"/><text x="26" y="85" class="dg-t">1</text>
      <circle cx="60" cy="114" r="5"/><text x="26" y="119" class="dg-t">2</text>
      <circle cx="60" cy="148" r="5"/><text x="26" y="153" class="dg-t">3</text>
    </g>
    <g class="dg-dot">
      <circle cx="470" cy="60" r="5"/><text x="486" y="65" class="dg-t">7</text>
      <circle cx="470" cy="110" r="5"/><text x="486" y="115" class="dg-t">4</text>
    </g>
    <path class="dg-arr" d="M66 80 C 200 80, 340 60, 464 60"/>
    <path class="dg-arr" d="M66 148 C 200 148, 340 112, 464 110"/>
    <text x="130" y="42" class="dg-note">h 0 = none  (unallocated)</text>
    <text x="130" y="128" class="dg-note">h 1 = some 7  (allocated)</text>
  </g>
</svg>
```

@@ p [14]
This is deliberately the <i>mathematically</i> cleanest representation, not an efficient one. A heap is an immutable value: writing to a heap does not mutate anything, it produces a different function.

@@ p [15]
Assertions will end up with type

@@ code [16]
```
abbrev Assertion := Store → Heap → Prop
```

@@ p [17]
— a predicate on a store (the ordinary program variables) and a heap (the memory you own).

@@ h3 [18]
How to use this workbook

@@ ol [19]
  - Read <b>the idea</b> section first. It is written in words, with no Lean, and it is where the actual mathematics lives.
  - Try each exercise in your own Lean file before opening anything. The <b>Hint</b> tells you the shape of the argument without giving it away.
  - Open <b>Solution</b> only after a real attempt, and then read <b>Why it works</b> — that is where the proof is explained line by line.
  - Tick the checkbox. Progress is stored locally in your browser.

@@ p [20]
Suggested file layout — one file per milestone, each importing only earlier ones:

@@ txt [21]
```
SepLogic/
  Heap.lean              -- M1
  HeapAlgebra.lean       -- M2
  Assertion.lean         -- M3
  Star.lean              -- M4
  Language.lean          -- M5
  Hoare.lean             -- M6, M7
  Locality.lean          -- M8
  Programs.lean          -- M9
  RecursivePredicates.lean -- M10
  Wand.lean              -- M11
  WeakestPrecondition.lean -- M12
  Loops.lean             -- M13
```

@@ note [22]
kind: info
title: Two traps
Two Lean-specific naming notes that will save you an hour. <code>while</code> is a reserved keyword, so the loop constructor here is called <code>loop</code>. And <code>⦃ ⦄</code> is already taken by Lean for strict-implicit binders, so a Hoare-triple notation must use different brackets — we simply write <code>Hoare P c Q</code>.
