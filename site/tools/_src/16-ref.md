# CHAPTER SOURCE — id=ref  num=§  index=16
phase: Reference
title: Reference, discipline, and what to retain
blurb: The notation table, the five rules of proof hygiene, and the ideas that outlive this particular development.

Blocks below are given in order. Each begins with `@@ <type> [n]`.

@@ h3 [0]
Notation

@@ txt [1]
```
  h l = some v      location l is allocated in h and holds v
  h l = none        location l is not in h

  emp               I own nothing
  l ↦ v             I own exactly the cell l, holding v
  P ∗ Q             the heap splits into disjoint parts satisfying P and Q
  P -∗ Q            give me a disjoint P-heap and the union satisfies Q
  P ⊢ Q             every state satisfying P satisfies Q
  P ⊣⊢ Q            P ⊢ Q and Q ⊢ P
  fact φ            φ holds; says nothing about the heap        (pairs with ∧)
  pure φ            φ holds and I own nothing                   (pairs with ∗)
  ⌜φ⌝               common textbook notation for pure φ
```

@@ h3 [2]
Proof discipline

@@ ol [3]
  - <b>Prove semantic lemmas before you introduce notation.</b> Notation hides definitions, which is useful only once you no longer need to see them.
  - <b>Keep primitive specifications small.</b> A write rule mentions one cell. If your rule mentions two, you have baked a frame into it and it will not compose.
  - <b>Separate heap algebra from program semantics.</b> <code>star_assoc</code> must not mention commands; <code>hoare_write</code> must not do a <code>funext</code>. When you catch yourself doing pointwise heap reasoning inside a Hoare proof, stop and extract a lemma.
  - <b>Avoid automation early.</b> <code>simp</code> closing a goal about disjoint union teaches you nothing about disjoint union. Build tactics after the manual proofs, not instead of them.
  - <b>Draw the heap decomposition before writing Lean.</b> Almost every hard proof in this course is bookkeeping about <code>h = (h₁ ∪ h₂) ∪ h₃</code>. Two minutes with a pen saves twenty in the editor.

@@ h3 [4]
The ideas worth keeping

@@ ul [5]
  - <b>Ownership is exact.</b> <code>l ↦ v</code> owns one cell. Everything else follows from taking that literally.
  - <b>Separation implies non-aliasing.</b> <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂</code> <i>proves</i> <code>l₁ ≠ l₂</code>. Side conditions became theorems.
  - <b>Small specifications scale.</b> A one-cell write rule is reusable in a heap of a million cells, unchanged, via one structural rule.
  - <b>The frame rule is a theorem about the semantics.</b> It holds because commands are local. Break locality — with fixed-address allocation, with a “heap size” primitive — and it fails.
  - <b>Recursive predicates fuse shape and ownership.</b> One assertion says both “these pointers form a list” and “I own every cell in it”.
  - <b>∗ and -∗ are an adjoint pair.</b> Not two connectives, one adjunction.
  - <b>The logic is algebraic, and heaps are only one model.</b> Everything in Phase 1 used exactly: a partial commutative monoid. Replace heaps with permissions, tokens, ghost state, protocol states, or fractional ownership, and the same laws hold. That is why one framework can serve concurrency, refinement, and program logic at once — and it is the single most useful thing to carry out of this course.

@@ h3 [6]
What you have built

@@ p [7]
A complete separation logic, from the empty file: a heap PCM; assertions and entailment; <code>∗</code>, <code>emp</code>, and the BI laws; a toy imperative language with relational and executable semantics proved equivalent; safe Hoare triples; small-footprint load / write / free rules; a semantic frame theorem; verified copy and move programs; recursive list and list-segment predicates with the append theorem; the magic wand and its adjunction; weakest preconditions; and the loop rules for partial and total correctness.

@@ quote [8]
That is a small but genuine separation-logic implementation, rather than a collection of Hoare-logic examples.

@@ note [9]
kind: info
title: Next
Two things are deliberately left undone, and both are good next sessions: the address-expression refactor with the two linked-list capstones (M13), and allocation (M14).
