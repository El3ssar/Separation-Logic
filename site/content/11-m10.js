/* M10 — Recursive predicates and linked structures
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  id:    'm10',
  num:   'M10',
  phase: 'Phase 3 · Advanced separation logic',
  title: 'Recursive predicates and linked structures',
  blurb: 'Describing unbounded data with recursive assertions — and the list-segment append theorem.',

  orient: {
    youWill: [
      'Write an assertion whose ∗-chain has no fixed length, and say exactly which cells it claims',
      'Peel a head node off <code>listRep</code> and put it back for nothing, and know which property of the definition makes that free',
      'Build a concrete three-node list by hand, choosing every heap cut and every existential witness yourself',
      'Prove <code>lseg_append</code> — two adjacent segments make one segment — as a chain of ∗-algebra lemmas, with no heap variable anywhere',
      'Read a wrong side condition off the goal state it strands you in'
    ],
    needs: [
      '<code>entails_trans</code>, <code>star_exists_left</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>',
      '<code>pure φ</code> as <code>aAnd (fact φ) emp</code>, and that the <code>emp</code> half is where exactness lives',
      '<code>union_empty_left</code>, <code>disjoint_empty_left</code>, and the six-slot star bracket',
      '<code>induction … with</code>, and M5’s reason for <code>generalizing</code>'
    ],
    payoff: 'Every loop invariant in M13 is a list segment, and the single lemma that maintains it across one iteration is the one you prove here.'
  },

  blocks: [
    { t: 'h3', s: 'An assertion with no fixed length' },

    { t: 'p',
      h: 'The chain has to be generated rather than written down, and the generator has to recurse on something. Not the heap: a heap is a function, with no constructors to descend through and no reason to stop. What does have that structure is the <i>mathematical</i> list of values the program is supposed to be holding. So the list becomes the principal argument, the pointer a parameter, and the result an <code>Assertion</code>.' },

    { t: 'p',
      h: 'Layout: a node at <code>p</code> occupies two consecutive cells — <code>p</code> holds the element, <code>p + 1</code> holds the next pointer. Location <code>0</code> is null.' },

    { t: 'svg',
      src: "\n<svg viewBox=\"0 0 560 150\" role=\"img\" aria-label=\"A linked list in the heap\">\n  <g class=\"dg\">\n    <g class=\"dg-cells\">\n      <rect x=\"24\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"a\"/><text x=\"45\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">10</text>\n      <rect x=\"66\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"b\"/><text x=\"87\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">•</text>\n      <rect x=\"204\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"a\"/><text x=\"225\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">20</text>\n      <rect x=\"246\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"b\"/><text x=\"267\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">•</text>\n      <rect x=\"384\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"a\"/><text x=\"405\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">30</text>\n      <rect x=\"426\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"b\"/><text x=\"447\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">0</text>\n    </g>\n    <path class=\"dg-arr\" d=\"M108 61 L 200 61\"/>\n    <path class=\"dg-arr\" d=\"M288 61 L 380 61\"/>\n    <text x=\"45\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">p</text>\n    <text x=\"225\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">p'</text>\n    <text x=\"405\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">p''</text>\n    <text x=\"45\" y=\"100\" text-anchor=\"middle\" class=\"dg-note\">p ↦ 10</text>\n    <text x=\"87\" y=\"100\" text-anchor=\"middle\" class=\"dg-note\">p+1 ↦ p'</text>\n    <text x=\"490\" y=\"100\" text-anchor=\"middle\" class=\"dg-note\">0 = null</text>\n    <text x=\"12\" y=\"132\" class=\"dg-note\">listRep [10,20,30] p owns all six cells and asserts they are linked in this order.</text>\n  </g>\n</svg>" },

    { t: 'code',
      src: 'def node (p : Loc) (value next : Nat) : Assertion :=\n  (p ↦ value) ∗ ((p + 1) ↦ next)\n\ndef listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next' },

    { t: 'anat',
      src: 'def listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next',
      parts: [
        { m: 'List Nat → Loc → Assertion',
          h: '<code>listRep xs p</code> reads “the heap I own is exactly a linked list holding the values <code>xs</code>, starting at <code>p</code>”. Lean accepts the definition without a hint because it is structurally recursive in the list argument, and it finds that argument itself. Putting the list first is readability, not necessity — the same clauses with the arguments swapped compile too.' },
        { m: '| [],      p => pure (fun _ => p = 0)',
          h: 'Two claims fused: the pointer is null, <i>and</i> I own nothing. The <code>emp</code> half is not decoration — it is what stops a one-element list from claiming extra memory it never uses.' },
        { m: 'aExists fun next =>',
          h: 'A caller who owns a list does not know where its second node lives, so the next pointer cannot be an argument of <code>listRep</code>. It is quantified inside the assertion instead. Unfolding a list <i>gives</i> you this witness; building one <i>costs</i> you it.' },
        { m: 'pure (fun _ => p ≠ 0)',
          h: 'What makes <code>0</code> mean end-of-list. Without it <code>listRep [7] 0</code> is satisfiable and the null pointer no longer decides emptiness. The <code>fun _ =></code> ignores the store: <code>p</code> is a Lean variable, not a program variable.' },
        { m: 'node p x next',
          h: 'This node’s two cells. Because <code>node</code> is a <code>∗</code> and not an <code>∧</code>, owning one already tells you <code>p ≠ p + 1</code>. That is exercise 2.' },
        { m: 'listRep xs next',
          h: 'The tail, in a separate part of the heap. The <code>∗</code> in front of it is the entire non-aliasing argument: the tail’s cells are disjoint from this node’s, hence from every earlier node’s, hence the chain cannot close on itself.' }
      ] },

    { t: 'p',
      h: 'The result type is <code>Assertion</code> rather than <code>Prop</code>, so the recursive call returns a <code>Store → Heap → Prop</code> and the connective joining it to the node in front of it is M4’s <code>∗</code>. Unfold <code>listRep [10,20,30] p</code> by hand: there is a next pointer <code>n₁</code>; <code>p</code> is non-null; I own <code>p ↦ 10</code> and <code>p+1 ↦ n₁</code>; and separately I own a list <code>[20,30]</code> starting at <code>n₁</code>. Six cells, and the stars are what make them six <i>different</i> cells.' },

    { t: 'cmp',
      left:  { t: 'The shape predicate you write first',
               h: 'Quantify over the node addresses and say the cells are linked:<br><code>∃ l₀ l₁ l₂, h l₀ = some 10 ∧ h (l₀+1) = some l₁ ∧ …</code><br>A perfectly good statement about a heap, and useless as a precondition. It does not say the six cells are distinct, it does not say the heap contains nothing else, and it survives the addition of junk. Two such lists may overlap; a “list” may be a lasso.' },
      right: { t: 'The separation-logic predicate', kind: 'good',
               h: 'Replace every <code>∧</code> by <code>∗</code> and make the base case <code>emp</code>. Distinctness stops being a hypothesis you state and carry, and becomes a consequence of the connective; exactness comes with it. The definition is now a shape invariant and a resource at once, which is what lets it be a precondition.' } },

    { t: 'note', kind: 'key', title: 'The one thing to remember',
      h: 'A recursive separation-logic predicate is simultaneously a <b>shape invariant</b> and an <b>ownership claim</b>. That is why unfolding one hands you non-aliasing for nothing, and why an entire structure can be passed to a subroutine as a single assertion.' },

    { t: 'detail', title: 'Why the nil case is <code>pure</code> and not <code>fact</code>', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'Write the empty clause as <code>fact (fun _ => p = 0)</code> instead. <code>fact φ</code> holds of every heap, so <code>listRep [] 0</code> is now satisfied by a heap containing anything at all.' },
        { t: 'p', h: 'Follow that up one layer. <code>listRep [x] p</code> says “own <code>node p x next</code>, and separately satisfy <code>listRep [] next</code>”. With the <code>emp</code> gone the second conjunct constrains nothing, so a one-element list may quietly claim unbounded extra memory. The predicate stops being a footprint and becomes “at least this”.' },
        { t: 'p', h: 'Then the frame rule loses its meaning, because a specification written with the leaky predicate can silently absorb the frame. It is the choice between <code>h = Heap.singleton l v</code> and <code>h l = some v</code>, made one level up.' }
      ] },

    { t: 'p',
      h: 'M9 stopped for want of a lemma that peels the head cell off an assertion whose length is unknown. Here it is. It costs nothing, and the reason it costs nothing is worth more than the lemma.' },

    {
      t: 'ex',
      id: 'm10-1',
      name: 'listRep_nil / listRep_cons_unfold / listRep_cons_fold',
      hard: false,

      why: 'These are the interface to the recursive predicate. Stating them explicitly — even though they are trivial — means later proofs cite a lemma instead of relying on how the equation compiler happened to unfold your definition.',

      setup: 'Three separate theorems. <code>listRep</code> and <code>node</code> are in scope, as is <code>entails_refl : ∀ (P : Assertion), P ⊢ P</code>.',

      goal: 'theorem listRep_nil (p : Loc) :\n    listRep [] p ⊢ pure (fun _ => p = 0)\n\ntheorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next\n\ntheorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p',

      hints: [
        'Do not reach for a tactic. Ask instead: as a <i>term</i>, what is <code>listRep (x :: xs) p</code>? The list argument is already a constructor application, so the pattern match can be evaluated without knowing anything about <code>x</code>, <code>xs</code> or <code>p</code>.',
        'If two assertions are literally the same term after that evaluation, then <code>P ⊢ Q</code> and <code>P ⊢ P</code> are the same proposition, and Lean accepts a proof of one for the other with no coercion.',
        'So each is <code>entails_refl _</code>, with the underscore inferred from the expected type. Write all three in term mode (<code>:= entails_refl _</code>), not as <code>by</code> blocks.'
      ],

      sol: 'theorem listRep_nil (p : Loc) : listRep [] p ⊢ pure (fun _ => p = 0) := entails_refl _\n\ntheorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next :=\n  entails_refl _\n\ntheorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p :=\n  entails_refl _',

      solNote: 'The unfold and the fold have the same proof with the sides swapped. Together they say <code>listRep (x :: xs) p ⊣⊢ …</code>, and neither direction costs anything.',

      expl: 'Because <code>listRep</code> is defined by structural recursion on a <i>constructor</i> pattern, <code>listRep (x :: xs) p</code> reduces definitionally to the right-hand side, and the entailment is the identity. Naming it anyway is hygiene: change the definition later and only these three lemmas break.',

      walk: [
        { tac: 'theorem listRep_nil … := entails_refl _',
          h: 'Lean elaborates <code>entails_refl _</code> against the expected type, which forces the metavariable to <code>listRep [] p</code>, and then checks <code>listRep [] p ⊢ listRep [] p</code> against <code>listRep [] p ⊢ pure (fun _ => p = 0)</code>. It unfolds the pattern match on <code>[]</code>, finds the same term on both sides, and accepts.' },
        { tac: 'theorem listRep_cons_unfold … := entails_refl _',
          h: 'One clause down. <code>listRep (x :: xs) p</code> reduces to <code>aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next</code> — the stated right-hand side, including the right-nesting of the two stars.' },
        { tac: 'theorem listRep_cons_fold … := entails_refl _',
          h: 'Definitional equality is symmetric, so the same term proves the reverse. There is no folding lemma to prove; there is a name to give.' }
      ],

      deep: [
        { t: 'p', h: 'Which equality Lean is using here decides whether a proof is one word or a page.' },
        { t: 'cmp',
          left:  { t: 'Definitional equality',
                   h: 'Terms the kernel sees as the same after unfolding definitions and evaluating pattern matches. <code>listRep (x :: xs) p</code> and its right-hand side are in this relation. Lean applies it <i>silently</i>, every time it checks a term against an expected type. You never invoke it; you notice it when something works that you expected to need a lemma.' },
          right: { t: 'Propositional equality', kind: 'good',
                   h: 'An inhabitant of <code>a = b</code>, driven by <code>rw</code>, <code>subst</code>, <code>simp</code>. <code>rw</code> matches <i>syntactically</i> and will not see through an unfolding for you. That asymmetry is why, later in this chapter, <code>exact hys</code> closes a goal about <code>lseg ([] ++ ys) p r</code> from a hypothesis about <code>lseg ys p r</code>, while <code>rw</code> in the same position wants <code>List.nil_append</code> spelled out.' } },
        { t: 'p', h: '<code>node</code> is a plain <code>def</code> rather than a pattern match, and unfolds for the same reason:' },
        { t: 'code', tag: 'illustration',
          src: 'theorem node_is_two_cells (p : Loc) (x n : Nat) :\n    node p x n ⊢ (p ↦ x) ∗ ((p + 1) ↦ n) := entails_refl _' },
        { t: 'detail', title: 'When would <code>entails_refl</code> stop working?', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Not, as you might guess, if the pattern match were replaced by a decidable test. <code>if xs = [] then … else …</code> still reduces on a literal <code>[]</code> and on a literal <code>x :: xs</code>, because <code>DecidableEq (List Nat)</code> is itself defined by recursion on constructors: given two constructor applications it computes down to <code>isTrue</code> or <code>isFalse</code> and the <code>if</code> unblocks.' },
            { t: 'p', h: 'What breaks it is <i>well-founded</i> recursion. Add a <code>termination_by</code> clause and Lean stops using the structural recursor, compiling through <code>WellFounded.fix</code> instead. That term is blocked on an accessibility proof, so it does not reduce even when the list argument is <code>[]</code>:' },
            { t: 'code', tag: 'sketch',
              cap: 'The last line is the one that fails; everything above it compiles.',
              src: 'def listRepWF : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRepWF xs next\n  termination_by xs _ => xs.length\n\nexample (p : Loc) : listRepWF [] p ⊢ pure (fun _ => p = 0) := entails_refl _' },
            { t: 'state',
              cap: 'Real error. Lean cannot even see that the nil clause is the nil clause.',
              src: 'error: Type mismatch\n  entails_refl ?m.6\nhas type\n  ?m.6 ⊢ ?m.6\nbut is expected to have type\n  listRepWF [] p ⊢ _root_.pure fun x => p = 0' },
            { t: 'p', h: 'The repair is the equation lemmas Lean generated alongside the definition, which is what <code>simp only [listRepWF]</code> fires: rewrite with the defining equations propositionally, rather than hoping the kernel will unfold. After that the two sides are syntactically equal.' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — compiled against the M10 prelude, with the definition above.',
              src: 'theorem listRepWF_nil (p : Loc) : listRepWF [] p ⊢ pure (fun _ => p = 0) := by\n  simp only [listRepWF]\n  exact entails_refl _' },
            { t: 'p', h: 'So structural recursion is not a stylistic preference. It is what makes the definition <i>compute</i>, and computation is what makes trivial lemmas trivial. When a <code>rfl</code>-shaped proof unexpectedly fails in someone else’s development, check how the definition was compiled before you doubt the statement.' }
          ] }
      ],

      pitfall: 'The proof is <code>entails_refl _</code> only if the right-hand side you wrote is <i>exactly</i> the definition, down to the bracketing. <code>∗</code> is <code>infixr</code>, so <code>pure φ ∗ node p x next ∗ listRep xs next</code> means <code>pure φ ∗ (node p x next ∗ listRep xs next)</code>. Write <code>(pure φ ∗ node p x next) ∗ listRep xs next</code> and the two terms are no longer definitionally equal; you then need <code>star_assoc_left</code> or <code>star_assoc_right</code> to repair it. Renaming the bound variable — <code>fun n =></code> for <code>fun next =></code> — is harmless, since Lean identifies alpha-equivalent terms.',

      variants: 'Swapping the sides of <code>listRep_cons_unfold</code> gives <code>listRep_cons_fold</code>: for a definitional unfolding the two directions cost the same. That is <i>not</i> true of the append theorems later — those hold one way only, because the appended segment loses the information about where the join was. Swap the order of the conjuncts instead, to <code>node p x next ∗ pure (fun _ => p ≠ 0) ∗ listRep xs next</code>, and both directions remain true but neither is <code>entails_refl</code>: you have to route through <code>star_comm</code> and <code>star_assoc_left</code>.'
    },

    { t: 'h4', s: 'Why the structure cannot be a lasso' },

    { t: 'p',
      h: 'A cycle would force one node to be owned twice, and owning one cell twice is not merely unsatisfiable — it is absurd:' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus — compiled against the M10 prelude.',
      src: 'theorem cell_not_duplicable (p : Loc) (x y : Val) : (p ↦ x) ∗ (p ↦ y) ⊢ aFalse := by\n  intro σ h hstar\n  exact absurd rfl (two_cells_distinct p p x y σ h hstar)' },

    { t: 'p',
      h: 'There is no arithmetic in that proof. <code>two_cells_distinct p p x y</code> concludes <code>p ≠ p</code> and <code>rfl</code> refutes it; the disequality came out of <code>Heap.disjoint</code>. The same lemma at two <i>different</i> locations is what the next exercise asks for.' },

    {
      t: 'ex',
      id: 'm10-2',
      name: 'node_cells_distinct',
      hard: false,

      why: 'Owning a node proves its two cells are different locations. Trivially true for <code>Nat</code> — the point is <i>where the proof comes from</i>: ownership, not arithmetic.',

      setup: '<code>two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) : (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)</code> is in scope, and <code>node p x next</code> is by definition <code>(p ↦ x) ∗ ((p + 1) ↦ next)</code>.',

      goal: 'theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1)',

      hints: [
        'You are asked to get a <i>disequality between locations</i> out of an <i>ownership assertion</i>. Exactly one lemma in scope does that.',
        'Unfold <code>node p x next</code> in your head to <code>(p ↦ x) ∗ ((p + 1) ↦ next)</code> and line it up against <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂)</code>. Which four arguments does <code>two_cells_distinct</code> want, and in what order?',
        'Both locations, then both values: <code>two_cells_distinct p (p + 1) x next</code>. No <code>by</code> block — it is a term, and the definitional unfolding of <code>node</code> is what lets the types match.'
      ],

      sol: 'theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=\n  two_cells_distinct p (p + 1) x next',

      expl: 'One line, and it never mentions that <code>p ≠ p + 1</code> is a fact about numbers. The separating conjunction supplied it.',

      walk: [
        { tac: 'two_cells_distinct p (p + 1) x next',
          h: 'Instantiating <code>l₁ := p</code>, <code>l₂ := p + 1</code>, <code>v₁ := x</code>, <code>v₂ := next</code> gives a term of type <code>(p ↦ x) ∗ ((p + 1) ↦ next) ⊢ fact (fun _ => p ≠ p + 1)</code>. That is definitionally the stated type, because <code>node</code> is a <code>def</code> and unfolds. There is no tactic block at all.' }
      ],

      deep: [
        { t: 'trace', title: 'The same statement, entered by hand',
          start: 'p : Loc\nx next : Nat\n⊢ node p x next ⊢ fact fun x => p ≠ p + 1',
          steps: [
            { tac: 'intro σ h hn',
              state: 'p : Loc\nx next : Nat\nσ : Store\nh : Heap\nhn : node p x next σ h\n⊢ fact (fun x => p ≠ p + 1) σ h',
              h: 'The bound variable of the <code>fun _ =></code> was given the display name <code>x</code>, colliding visually with the element <code>x : Nat</code>. Different variables; the printer does not care. The lambda prints bare in the first state and parenthesised in the second — same term either way.' },
            { tac: 'exact two_cells_distinct p (p + 1) x next σ h hn',
              h: 'The same lemma, now applied to <code>σ</code>, <code>h</code> and the hypothesis. The solution is this with the last three arguments left off.' }
          ],
          done: 'No goals.' },
        { t: 'p', h: 'There is an arithmetic proof too, and it is worse for a reason that is not aesthetic.' },
        { t: 'cmp',
          left:  { t: 'The arithmetic route',
                   h: 'Throw the ownership away and prove the numeric fact. It works, it needs a <code>show</code> to strip the <code>fact</code> wrapper, and it proves the statement only in a model where locations are <code>Nat</code>.',
                   src: 'example (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) := by\n  intro σ h _\n  show p ≠ p + 1\n  simp',
                   tag: 'illustration' },
          right: { t: 'The ownership route', kind: 'good',
                   h: 'Never mentions numbers. It uses that a heap cannot be disjoint from itself at a location it defines — a fact about M2’s resource monoid. Swap <code>Loc</code> for an abstract type with a field offset and this still compiles.',
                   src: 'two_cells_distinct p (p + 1) x next',
                   tag: 'verified' } },
        { t: 'detail', title: 'A small Lean surprise: <code>omega</code> and <code>abbrev</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'You would expect <code>omega</code> to close <code>p ≠ p + 1</code> in one word. It does — but only if the variable’s declared type is literally <code>Nat</code>. Here <code>Loc</code> is <code>abbrev Loc := Nat</code>, and under Lean 4.32.2 these two behave differently:' },
            { t: 'code', tag: 'sketch',
              src: 'example (p : Nat) : p ≠ p + 1 := by omega   -- succeeds\nexample (p : Loc) : p ≠ p + 1 := by omega   -- fails' },
            { t: 'state',
              cap: 'Real error from the second line.',
              src: 'error: omega could not prove the goal:\nNo usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.' },
            { t: 'p', h: 'It is not about <code>≠</code> and not about the <code>+</code>: <code>example (p : Loc) : p &lt; p + 1 := by omega</code> and <code>example (p q : Loc) (h : p = q) : q = p := by omega</code> fail with the same message. <code>omega</code> decides linear arithmetic over <code>Nat</code> and <code>Int</code>, and it recognises which subterms are arithmetic by inspecting the types <i>as they appear in the goal</i>. <code>Loc</code> is a different expression from <code>Nat</code>, whatever the kernel will unfold on demand, so nothing is recognised and there are genuinely no constraints to feed the procedure. Two lines reproduce it outside the workbook: <code>abbrev L := Nat</code> and <code>example (p : L) : p ≠ p + 1 := by omega</code>.' },
            { t: 'p', h: '<code>simp</code> closes it without complaint. <code>decide</code> does not, for an unrelated reason that bites the <code>Nat</code> version too: it needs a closed proposition, and <code>p ≠ p + 1</code> has a free variable (<i>Expected type must not contain free variables</i>). Reducibility is a property of the kernel, not a promise about tactics; a tactic that pattern-matches on types can be blind to a synonym the kernel considers transparent. When a decision procedure says there is nothing to work with, suspect an abbreviation before you suspect the goal.' }
          ] }
      ],

      pitfall: 'Getting the argument order wrong. <code>two_cells_distinct</code> takes both locations before both values, so <code>two_cells_distinct p (p + 1) next x</code> type-checks as a term but has the wrong type, and Lean reports it against the whole statement rather than one argument:<br><code>has type p ↦ next ∗ p + 1 ↦ x ⊢ fact fun x => p ≠ p + 1</code><br><code>but is expected to have type node p x next ⊢ fact fun x => p ≠ p + 1</code><br>Read the first line, not the second: it says the values are swapped. And the printer drops the parentheses around <code>p + 1 ↦ x</code>, since <code>↦</code> binds tighter than <code>∗</code>.',

      variants: 'Instantiate <code>two_cells_distinct</code> at the <i>same</i> location twice and the conclusion is <code>p ≠ p</code>, so the premise must be unsatisfiable — that is <code>cell_not_duplicable</code>, and it is the whole reason structures built with <code>∗</code> are acyclic. Replace the <code>∗</code> in <code>node</code> by <code>aAnd</code> and the lemma becomes vacuous rather than false: <code>aAnd (p ↦ x) ((p + 1) ↦ n)</code> demands one heap be two different singletons, so it holds of nothing and entails everything. Vacuous truth is the characteristic failure of writing <code>∧</code> where you meant <code>∗</code>, and it is worse than falsehood because the proofs still go through.'
    },

    { t: 'h4', s: 'One list, built by hand' },

    { t: 'p',
      h: 'The next exercise is the only one in the chapter that works in the model rather than the algebra, and it is here so that you can see what the algebra is saving you from. Five anonymous constructors, so count the slots first.' },

    { t: 'steps', title: 'Counting the slots of a nested assertion',
      items: [
        { k: 'Nesting adds slots, not brackets',
          h: 'A star is six fields. If <code>Q</code> is itself a star, its proof is another six written inline rather than nested, so <code>P ∗ (Q ∗ R)</code> is a single bracket with 5 + 6 = 11. That is the <code>obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩</code> below: five for the outer star up to and including the proof of <code>node p a q</code>, then six for the inner one.' },
        { k: 'A layer of listRep is seven',
          h: 'The cons clause is <code>aExists fun next => pure φ ∗ (node p x next ∗ listRep xs next)</code>: one slot for the witness, then the six of the outer star — <code>⟨next, hLeft, hRight, disjoint, heap equation, proof of pure φ, proof of the rest⟩</code>. And the proof of <code>pure φ</code> is itself two fields, written <code>⟨hp, rfl⟩</code>.' },
        { k: 'The pure conjunct always cuts off Heap.empty',
          h: 'The left half of that star has to be the empty heap. So <code>hLeft := Heap.empty</code>, the disjointness is <code>disjoint_empty_left _</code>, and the equation is <code>(union_empty_left _).symm</code> — every time. Recognising that trio on sight is most of the exercise.' },
        { k: 'refine, not exact',
          h: 'Write <code>refine ⟨…, ?_⟩</code> and leave the recursive tail as a hole. Lean then tells you what the next layer must prove, with the heap already computed. Writing the whole nested term as one <code>exact</code> is possible and a bad idea: when it fails you get one error about a thirty-token term instead of one goal you can read.' }
      ] },

    {
      t: 'ex',
      id: 'm10-3',
      name: 'concrete three-node list',
      hard: true,

      why: 'Assemble a concrete structure out of concrete points-to facts, and calibrate what the existentials are doing. It is also the last heap variable you will touch in this chapter; everything after it is algebra, and the contrast is the point.',

      setup: 'The hypotheses <code>hp</code>, <code>hq</code>, <code>hr</code> supply the non-null side conditions of the three cons layers. Nothing supplies non-nullity for the terminal <code>0</code>, and nothing needs to: the nil layer asks for <code>0 = 0</code>.',

      goal: 'theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p',

      hints: [
        'You cannot make progress with <code>refine</code> while the heap is an opaque variable, because every layer has to say what its half of the heap <i>is</i>. Start in the model: <code>intro σ h hstar</code>, then take <code>hstar</code> apart.',
        'Destructure with one bracket — <code>node p a q ∗ (node q b r ∗ node r c 0)</code> has 5 + 6 = 11 fields. Then <code>subst</code> both heap equations, so <code>h</code> disappears and the goal’s heap is literally <code>h₁.union (h₃.union h₄)</code>, a term built out of unions. That is what makes the later equations <code>rfl</code>.',
        'Each <code>listRep</code> layer is seven slots: <code>⟨next, Heap.empty, «the rest of the heap», disjoint_empty_left _, (union_empty_left _).symm, ⟨hNonNull, rfl⟩, ?_⟩</code>. Alternate that with the six-slot star that hands a node its heap.',
        'The witnesses, in order, are the next pointers: <code>q</code>, then <code>r</code>, then <code>0</code>. The last line closes <code>listRep [] 0</code> with <code>⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩</code> — the empty heap on the <i>right</i> this time, since the nil clause is the second conjunct.'
      ],

      sol: 'theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p := by\n  intro σ h hstar\n  obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩ := hstar\n  subst hu\'\n  subst hu\n  refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩\n  refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩\n  refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩\n  refine ⟨h₃, h₄, hd\', rfl, hn₂, ?_⟩\n  refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩\n  exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩',

      expl: 'The rhythm is: witness the existential, split off <code>Heap.empty</code> for the <code>pure</code>, hand the node its heap, recurse. The two <code>subst</code>s at the top are what make every later heap equation <code>rfl</code> — normalise the hypotheses before you start building the goal, or you fight <code>union_assoc</code> at every step.',

      walk: [
        { tac: 'intro σ h hstar',
          h: 'Into the model with a store, a heap and the premise. The goal becomes <code>listRep [a, b, c] p σ h</code>.' },
        { tac: 'obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩ := hstar',
          h: 'Eleven names for the nested star. <code>h₁</code> holds the first node, <code>h₂</code> the other two, <code>hu : h = h₁.union h₂</code>, and then <code>h₂</code> splits again into <code>h₃</code> and <code>h₄</code>. Four heaps and two equations.' },
        { tac: 'subst hu\'',
          h: '<code>hu\' : h₂ = h₃.union h₄</code>, so <code>h₂</code> is erased everywhere: <code>hu</code> becomes <code>h = h₁.union (h₃.union h₄)</code> and <code>hd</code> becomes <code>h₁.disjoint (h₃.union h₄)</code>.' },
        { tac: 'subst hu',
          h: 'Erases <code>h</code> itself, so the goal’s heap is the explicit union tree. From here every heap you name in a bracket is a <i>subterm</i> of that tree, which is why the equations you owe are all <code>rfl</code>.' },
        { tac: 'refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _, (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩',
          h: 'The outermost layer. <code>q</code> witnesses <code>next</code>; the cut is <code>Heap.empty</code> against the whole remaining tree; <code>⟨hp, rfl⟩</code> proves <code>pure (fun _ => p ≠ 0)</code>, with <code>rfl</code> for the <code>emp</code> because <code>emp σ Heap.empty</code> unfolds to <code>Heap.empty = Heap.empty</code>.' },
        { tac: 'refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩',
          h: 'Six slots, for the star <code>node p a q ∗ listRep [b, c] q</code>. <code>h₁</code> is the node’s heap, <code>hd</code> is the disjointness you already have, and the heap equation is <code>rfl</code> because of the two <code>subst</code>s.' },
        { tac: 'refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩',
          h: 'Second layer, same rhythm, one heap smaller. Witness <code>r</code>, empty heap for the pure part, <code>hq</code> for <code>q ≠ 0</code>.' },
        { tac: 'refine ⟨h₃, h₄, hd\', rfl, hn₂, ?_⟩',
          h: 'Hand the second node <code>h₃</code>, leaving <code>h₄</code> for the tail. Again <code>rfl</code>, because the goal’s heap is literally <code>h₃.union h₄</code>.' },
        { tac: 'refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩',
          h: 'The last cons layer. The witness is <code>0</code>: this node’s next pointer is null, which is what makes the list terminate.' },
        { tac: 'exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩',
          h: 'Seven slots for <code>node r c 0 ∗ listRep [] 0</code>. The empty heap is now on the <i>right</i>, hence <code>disjoint_empty_right</code> and <code>union_empty_right</code>. The last two <code>rfl</code>s are the nil clause: <code>0 = 0</code> for the fact, <code>Heap.empty = Heap.empty</code> for the <code>emp</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'concrete_list, tactic by tactic (real Lean output)',
          start: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\n⊢ node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p',
          steps: [
            { tac: 'intro σ h hstar',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh : Heap\nhstar : (node p a q ∗ node q b r ∗ node r c 0) σ h\n⊢ listRep [a, b, c] p σ h',
              h: 'The two <code>⊢</code> in the starting goal have become one. The outer one was <code>Entails</code>, and introducing <code>σ</code>, <code>h</code> and the premise consumed it.' },
            { tac: 'obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩ := hstar',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhu\' : h₂ = h₃.union h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\n⊢ listRep [a, b, c] p σ h',
              h: 'Lean prints <code>h₁.disjoint h₂</code> and <code>h₁.union h₂</code>, not <code>Heap.disjoint h₁ h₂</code>. Dot notation is the printer’s choice, not something in the source; when you type the terms back, either form is accepted.' },
            { tac: 'subst hu\'  ·  subst hu',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [a, b, c] p σ (h₁.union (h₃.union h₄))',
              h: 'The state the whole proof depends on. <code>h</code> and <code>h₂</code> are gone, the goal names an explicit union tree, and <code>hd</code> has been rewritten into exactly the disjointness the first star will ask for. <code>hd</code> has also moved to the bottom of the context: <code>subst</code> reinserts a rewritten hypothesis at the end.' },
            { tac: 'refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _, (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ (node p a q ∗ listRep [b, c] q) σ (h₁.union (h₃.union h₄))',
              h: 'The existential and the pure conjunct are discharged, and the remaining goal has already unfolded one layer, with <code>q</code> substituted for the witness. This is the moment the recursion becomes visible.' },
            { tac: 'refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [b, c] q σ (h₃.union h₄)',
              h: 'One node paid for. The goal is the original statement with the first element removed and the heap shrunk by one subtree — same shape, smaller data. That similarity is what the induction in the later exercises exploits.' },
            { tac: 'refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ (node q b r ∗ listRep [c] r) σ (h₃.union h₄)',
              h: 'Second layer opened, witness <code>r</code>.' },
            { tac: 'refine ⟨h₃, h₄, hd\', rfl, hn₂, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [c] r σ h₄',
              h: 'A one-element list on a single heap. <code>h₁</code> and <code>h₃</code> are spent — still in the context, but nothing left in the goal mentions them.' },
            { tac: 'refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ (node r c 0 ∗ listRep [] 0) σ h₄',
              h: 'The witness <code>0</code> propagated into the tail, so the remaining obligation is <code>listRep [] 0</code>, where the recursion stops.' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'Does the order of the two <code>subst</code>s matter?', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'No. <code>subst hu</code> first erases <code>h</code>, leaving <code>h₁.union h₂</code> in the goal, and <code>subst hu\'</code> then erases <code>h₂</code> inside it. The resulting state is identical down to the order of the context. Trying it is a cheap way to convince yourself that <code>subst</code> is substitution and has no hidden orientation cleverness.' },
            { t: 'p', h: 'What matters is doing them at all, and doing them before the first <code>refine</code> — the subject of the pitfall below.' }
          ] },
        { t: 'p', h: 'Twelve lines for a list of length three. The next exercise proves a statement about lists of every length, in eight.' }
      ],

      pitfall: 'Skipping the <code>subst</code>s and going straight to <code>refine</code>. The heap equation slot then has to prove <code>h = Heap.union Heap.empty (…)</code> with <code>h</code> still opaque, and <code>(union_empty_left _).symm</code> cannot have that type. Lean says so, but it says it about the <i>bracket</i>:<br><code>Application type mismatch: The argument Eq.symm (union_empty_left ?m.108) has type ?m.108 = Heap.empty.union ?m.108 but is expected to have type h = Heap.empty.union (h₁.union (h₃.union h₄))</code><br>The tell is <code>?m.108</code> on both sides of the “has type” line: this lemma can only prove an equation whose left side is the same as its right operand, and yours is not, because nothing has said what <code>h</code> is.',

      variants: 'Drop <code>hp : p ≠ 0</code> and the first <code>⟨hp, rfl⟩</code> has nothing to put in the <code>fact</code> slot — rightly, because the theorem is then false: take <code>p = 0</code> with a heap containing cells <code>0</code> and <code>1</code>, and the left-hand side holds while <code>listRep [a, b, c] 0</code> does not. Drop <code>hr : r ≠ 0</code> and it fails at the third layer instead of the first. There is no hypothesis about the terminal <code>0</code> because the nil clause asks for <code>0 = 0</code>. Reverse the entailment — <code>listRep [a, b, c] p ⊢ node p a q ∗ node q b r ∗ node r c 0</code> — and it is false for a different reason: the list quantifies its next pointers existentially, so it cannot know they are the particular <code>q</code> and <code>r</code> you named.'
    },

    { t: 'sec', s: 'List segments' },

    { t: 'p',
      h: 'A traversal at any moment has a list behind it and a list in front of it, and the part behind it is not a list: it runs from <code>start</code> up to some cursor and then stops. That is a segment, and it is what every loop invariant in M13 is made of.' },

    { t: 'code',
      src: 'def lseg : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next =>\n        pure (fun _ => start ≠ 0) ∗ node start x next ∗ lseg xs next finish' },

    { t: 'txt',
      cap: 'A segment owns the nodes strictly between start and finish. The node at finish, if there is one, belongs to somebody else.',
      src: '  lseg [x₀, x₁, x₂] start finish\n\n      start ──▶ x₀ ──▶ x₁ ──▶ x₂ ──▶ finish\n      └────────── owned ──────────┘   not owned\n\n  lseg [] start finish   ≡   start = finish  and  own nothing' },

    { t: 'tbl',
      head: ['', '<code>listRep xs p</code>', '<code>lseg xs p q</code>'],
      rows: [
        ['base case', '<code>pure (fun _ => p = 0)</code>', '<code>pure (fun _ => p = q)</code>'],
        ['what ends it', 'the null pointer', 'an arbitrary chosen endpoint'],
        ['cons side condition', '<code>p ≠ 0</code>', '<code>start ≠ 0</code> — the <i>same</i> condition'],
        ['owns', 'the whole list', 'only the nodes before <code>q</code>'],
        ['relation', '<code>lseg xs p 0 ⊢ listRep xs p</code>', 'a list is a segment ending at null']
      ],
      cap: 'Line 3 is the one that is easy to get wrong.' },

    { t: 'note', kind: 'warn', title: 'A wrong side condition, and how it announces itself',
      h: 'The obvious cons condition is <code>start ≠ finish</code>: a non-empty segment does not end where it begins. With it, <b><code>lseg_append</code> is not provable</b> — after appending you hold a proof of <code>p ≠ q</code> and the goal demands <code>p ≠ r</code>, with nothing to connect them. It is unprovable because it is <i>false</i>, and the collapsed block exhibits the two-node cycle that refutes it. The condition has to be <b><code>start ≠ 0</code></b>, the same one <code>listRep</code> uses; then both append theorems go through by a clean induction and the two predicates fit together.' },

    { t: 'detail', title: 'The wrong version, in Lean, with the goal state that reveals it', tag: 'worth doing', open: false,
      blocks: [
        { t: 'p', h: 'Define it and start the append proof the same way. Three tactics into the cons case, Lean shows you the problem.' },
        { t: 'code', tag: 'sketch',
          src: 'def lsegBad : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next =>\n        pure (fun _ => start ≠ finish) ∗ node start x next ∗ lsegBad xs next finish\n\nexample : ∀ (xs ys : List Nat) (p q r : Loc),\n    lsegBad xs p q ∗ lsegBad ys q r ⊢ lsegBad (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil => sorry\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      trace_state\n      sorry' },
        { t: 'state',
          cap: 'Real output. Left of the ⊢ you have p ≠ q; right of it the goal wants p ≠ r. No hypothesis relates q and r, and no amount of ∗-algebra will produce one.',
          src: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lsegBad xs p q ∗ lsegBad ys q r ⊢ lsegBad (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ ((_root_.pure fun x => p ≠ q) ∗ node p x n ∗ lsegBad xs n q) ∗ lsegBad ys q r ⊢\n    (_root_.pure fun x => p ≠ r) ∗ node p x n ∗ lsegBad (xs.append ys) n r' },
        { t: 'p', h: 'A stuck goal is not by itself evidence that a theorem is false; you might be proving it badly. Here it <i>is</i> false, and the witness is exactly the thing recursive predicates are supposed to control. Put two nodes at addresses <code>10</code> and <code>20</code> pointing at each other. Then <code>lsegBad [7] 10 20</code> holds (its side condition is <code>10 ≠ 20</code>), <code>lsegBad [8] 20 10</code> holds (<code>20 ≠ 10</code>), and the two own disjoint cells — but the conclusion <code>lsegBad [7, 8] 10 10</code> demands <code>10 ≠ 10</code>.' },
        { t: 'code', tag: 'illustration',
          cap: 'Not in the corpus — compiled against the M10 prelude. The heap is {10 ↦ 7, 11 ↦ 20, 20 ↦ 8, 21 ↦ 10}: two nodes, each pointing at the other.',
          src: 'theorem lsegBad_append_false :\n    ¬ (∀ (xs ys : List Nat) (p q r : Loc),\n        lsegBad xs p q ∗ lsegBad ys q r ⊢ lsegBad (xs ++ ys) p r) := by\n  intro hcontra\n  let hA := Heap.union (Heap.singleton 10 7) (Heap.singleton 11 20)\n  let hB := Heap.union (Heap.singleton 20 8) (Heap.singleton 21 10)\n  have hd : Heap.disjoint hA hB :=\n    disjoint_union_left.mpr\n      ⟨disjoint_union_right.mpr ⟨singleton_disjoint 7 8 (by decide), singleton_disjoint 7 10 (by decide)⟩,\n       disjoint_union_right.mpr ⟨singleton_disjoint 20 8 (by decide), singleton_disjoint 20 10 (by decide)⟩⟩\n  have hprem : (lsegBad [7] 10 20 ∗ lsegBad [8] 20 10) (fun _ => 0) (Heap.union hA hB) :=\n    ⟨hA, hB, hd, rfl,\n     ⟨20, Heap.empty, hA, disjoint_empty_left _, (union_empty_left _).symm,\n       ⟨(by decide : (10:Nat) ≠ 20), rfl⟩,\n       ⟨hA, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm,\n         ⟨Heap.singleton 10 7, Heap.singleton 11 20, singleton_disjoint 7 20 (by decide), rfl, rfl, rfl⟩,\n         ⟨rfl, rfl⟩⟩⟩,\n     ⟨10, Heap.empty, hB, disjoint_empty_left _, (union_empty_left _).symm,\n       ⟨(by decide : (20:Nat) ≠ 10), rfl⟩,\n       ⟨hB, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm,\n         ⟨Heap.singleton 20 8, Heap.singleton 21 10, singleton_disjoint 8 10 (by decide), rfl, rfl, rfl⟩,\n         ⟨rfl, rfl⟩⟩⟩⟩\n  obtain ⟨n, _, _, _, _, ⟨hne, _⟩, _⟩ :=\n    hcontra [7] [8] 10 20 10 (fun _ => 0) (Heap.union hA hB) hprem\n  exact hne rfl' },
        { t: 'p', h: 'That says something about the <i>correct</i> definition too. With <code>start ≠ 0</code>, <code>lseg [7, 8] 10 10</code> is perfectly satisfiable — the same four-cell cycle satisfies it, and <code>lseg_append [7] [8] 10 20 10</code> is what builds the proof. A segment here is a chain of distinct cells from <code>start</code> reaching <code>finish</code>, and nothing rules out <code>finish</code> lying back inside the chain. <code>start ≠ finish</code> tried to rule it out and, in exchange, stopped being closed under append. <code>lseg</code> is deliberately permissive; acyclicity comes back at the point of use, because in M13 the segment is always paired with a <code>listRep</code> running to null, and <code>listRep</code> is acyclic.' },
        { t: 'p', h: 'The moral is not “check your definitions”. It is that in a proof assistant a wrong definition is <i>located</i>, by a goal you cannot close. Notice also that <code>start ≠ finish</code> was not even the property wanted: the empty segment has <code>start = finish</code>, so the cons clause was asserting the segment is non-empty — true, and useless.' }
      ] },

    { t: 'sec', s: 'Two adjacent pieces make one' },

    { t: 'p',
      h: 'Both remaining theorems go by induction on the first list, and how you <i>state</i> them decides whether the induction works at all.' },

    { t: 'cmp',
      left: { t: 'The statement you write first',
              h: 'Variables in the binder list, where they belong:<br><code>theorem lseg_append (xs ys : List Nat) (p q r : Loc) : lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r</code><br>Then <code>induction xs</code> hands you this:',
              src: 'ih : lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',
              tag: 'sketch',
              kind: 'bad' },
      right: { t: 'The statement Lean needs',
               h: 'Everything but the induction variable quantified <i>inside</i> the statement, and <code>intro xs</code> alone:<br><code>theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc), …</code><br>Now the hypothesis quantifies over its own start pointer:',
               src: 'ih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',
               tag: 'sketch',
               kind: 'good' } },

    { t: 'p',
      h: 'In the cons case the tail segment starts at the <i>next pointer</i> <code>n</code>, and the proof ends with <code>ih ys n q r</code>. The left-hand version cannot supply that, because its <code>p</code> is fixed by the enclosing theorem: you get a type mismatch on the very last line and no way to repair it. <code>induction … generalizing</code> would do the same job here; putting the <code>∀</code> in the statement also leaves the lemma more useful to callers, who can instantiate it however they like.' },

    { t: 'p',
      h: 'One lemma is missing from the toolkit. <code>lseg</code>’s cons clause opens with an <code>aExists</code>, and nothing in scope lets you work under that binder, so exercise 4 starts by proving <code>aExists_mono : (∀ x, P x ⊢ Q x) → aExists P ⊢ aExists Q</code>. Everything else it needs — <code>entails_trans</code>, <code>star_exists_left</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>, <code>union_empty_left</code> — you already have.' },

    {
      t: 'ex',
      id: 'm10-4',
      name: 'lseg_append',
      hard: true,

      why: '<b>The classical theorem of the subject.</b> Two adjacent segments make one segment. Every list-traversal loop invariant is maintained by an application of this; in M13 it is the lemma that moves one node from “still to visit” to “already visited”.',

      setup: 'Two theorems, in order: <code>aExists_mono</code> first, then <code>lseg_append</code>. The universe variable <code>u</code> in <code>{α : Sort u}</code> is auto-bound; you do not declare it.',

      goal: 'theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',

      hints: [
        'Prove <code>aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) : aExists P ⊢ aExists Q</code> first. It is two tactics: introduce down to the premise, destructing it on arrival, and rebuild the existential with the same witness.',
        'State the theorem with <code>∀ (xs ys : List Nat) (p q r : Loc),</code> inside it, then <code>intro xs</code> only.',
        'The nil case is <code>pure (fun _ => p = q) ∗ lseg ys q r ⊢ lseg ys p r</code>. Do that one in the model: <code>intro</code> down to the heap, <code>obtain</code> the six fields, substitute <code>p = q</code> and substitute the empty heap, then <code>rw [hu, union_empty_left]</code>. Careful: the equation arrives with type <code>fact (fun x => p = q) σ h₁</code>, which does not <i>look</i> like an equation.',
        'The cons case has no heaps at all. Pull the existential out (<code>star_exists_left</code>), go under the binder (<code>aExists_mono</code>), re-bracket so the <code>pure</code> is the outer left factor (<code>star_assoc_left</code>), discard it (<code>star_mono_right</code>), re-bracket again so the two segments sit together, and finish with <code>star_mono_right _ (ih ys n q r)</code>.'
      ],

      sol: 'theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :\n    aExists P ⊢ aExists Q := by\n  intro σ hh ⟨x, hp⟩\n  exact ⟨x, h x σ hh hp⟩\n\ntheorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq\' : p = q := hpq\n      subst hpq\'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)',

      expl: 'Eight lines in the cons case, no heap variables, no unions. Read as a chain: pull the existential out of the star; work under the binder; reassociate so the pure fact is on the outside; cancel it against the identical factor on the right; reassociate again so the two segments are adjacent; apply the induction hypothesis to them under the node. Every step is an M4 lemma. If you built the normalisation library then, you are collecting the dividend now.',

      walk: [
        { tac: 'intro σ hh ⟨x, hp⟩',
          h: 'In <code>aExists_mono</code>. The third introduction is a pattern: <code>aExists P σ hh</code> is <code>∃ x, P x σ hh</code>, so this hands you the witness and the body in one move.' },
        { tac: 'exact ⟨x, h x σ hh hp⟩',
          h: 'Rebuild the existential with the <i>same</i> witness — the whole content of the lemma is that monotonicity under <code>∃</code> does not change which element you are talking about.' },
        { tac: 'theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc), …',
          h: 'All five variables under a <code>∀</code> in the statement, for the reason above.' },
        { tac: 'intro xs',
          h: 'Introduce only the variable you recurse on. <code>ys</code>, <code>p</code>, <code>q</code>, <code>r</code> stay in the goal, which is what makes the induction hypothesis general.' },
        { tac: 'induction xs with',
          h: 'The two branches are named after <code>List</code>’s constructors and each supplies its own binders. Plain <code>induction xs</code> with <code>·</code> bullets works too, but leaves the case names implicit; the <code>with</code> form fails loudly if you misname one.' },
        { tac: '| nil =>',
          h: 'Goal: <code>∀ ys p q r, lseg [] p q ∗ lseg ys q r ⊢ lseg ([] ++ ys) p r</code>. Since <code>lseg [] p q</code> is <code>pure (fun _ => p = q)</code>, this says an empty segment on the left is the identity.' },
        { tac: 'intro ys p q r σ h hstar',
          h: 'Seven introductions: four from the <code>∀</code>, then store, heap and premise from unfolding <code>⊢</code>. This branch goes through the model because the empty-heap bookkeeping is easier there than through <code>star_pure_left</code>.' },
        { tac: 'obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
          h: 'Six slots, disjointness thrown away with <code>_</code> — genuinely not needed, since one side is empty. The nested <code>⟨hpq, he⟩</code> splits <code>pure φ</code> into its <code>fact</code> and its <code>emp</code>.' },
        { tac: 'have hpq\' : p = q := hpq',
          h: 'Type ascription and nothing else: <code>fact (fun x => p = q) σ h₁</code> unfolds to <code>p = q</code>, so <code>hpq</code> already <i>is</i> a proof of the equation. Under 4.32.2 the line is unnecessary — <code>subst hpq</code> alone works, since <code>subst</code> unfolds far enough to find the equation. Keep it for the reader: a hypothesis displayed as <code>fact (fun x => p = q) σ h₁</code> does not look substitutable, and this is where you record that it is.' },
        { tac: 'subst hpq\'',
          h: 'Replaces <code>q</code> by <code>p</code> throughout. Note the direction: <code>subst</code> eliminated <code>q</code>, so <code>hys</code> becomes <code>lseg ys p r σ h₂</code>, which is what the goal wants.' },
        { tac: 'subst he',
          h: '<code>he : emp σ h₁</code> is definitionally <code>h₁ = Heap.empty</code>, so this erases <code>h₁</code> and turns <code>hu</code> into <code>h = Heap.empty.union h₂</code>. No <code>have</code> is needed here, because <code>emp</code> unfolds directly to an equation between heaps.' },
        { tac: 'rw [hu, union_empty_left]',
          h: 'Rewrite the goal’s heap with <code>hu</code>, then collapse <code>Heap.empty.union h₂</code> to <code>h₂</code>.' },
        { tac: 'exact hys',
          h: 'The goal says <code>[] ++ ys</code> and the hypothesis says <code>ys</code>. Not syntactically equal, but <code>List.append</code> reduces on its first argument, and <code>exact</code> checks up to definitional equality. <code>rw [List.nil_append]</code> would also work and is unnecessary.' },
        { tac: '| cons x xs ih =>',
          h: 'Head, tail, and an induction hypothesis that is itself a <code>∀</code> over four variables.' },
        { tac: 'intro ys p q r',
          h: 'Four introductions, and <i>stop</i>. No <code>σ</code>, no <code>h</code>. Everything below manipulates entailments as objects.' },
        { tac: 'refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_',
          h: 'Composition with the identity on the left factor. It changes nothing — the printed goal is character-for-character the same before and after. It is documentation of what is about to be rewritten; the aside below deletes it and the proof still compiles.' },
        { tac: 'refine entails_trans (star_exists_left _ _) ?_',
          h: 'The first real step. <code>lseg (x :: xs) p q</code> unfolds to an <code>aExists</code>, so the left side is <code>aExists (…) ∗ lseg ys q r</code>, and this pushes the star inside.' },
        { tac: 'refine aExists_mono (fun n => ?_)',
          h: 'Both sides are now existentials — the right one because <code>lseg (x :: xs ++ ys) p r</code> also unfolds to an <code>aExists</code> — so you can go under the binder. <code>n</code> enters the context as the shared next pointer. This is where the proof stops being about lists and becomes about one node plus a smaller problem.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'The left side is <code>(pure φ ∗ (node ∗ lseg xs n q)) ∗ lseg ys q r</code>, because the star <code>star_exists_left</code> introduced sits outside. Re-bracketing to the right makes <code>pure φ</code> the outermost left factor, matching the right-hand side.' },
        { tac: 'refine star_mono_right _ ?_',
          h: 'Both sides start with the same <code>pure φ</code>, so peel it off. The <code>_</code> is that common factor; the hole is the entailment between what remains.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'The same move one level down: <code>(node ∗ lseg xs n q) ∗ lseg ys q r</code> becomes <code>node ∗ (lseg xs n q ∗ lseg ys q r)</code>, which finally places the two segments next to each other.' },
        { tac: 'exact star_mono_right _ (ih ys n q r)',
          h: 'Peel off the node and apply the induction hypothesis to the adjacent pair — <i>at the next pointer</i> <code>n</code>, which is why the statement had to quantify over the start location.' }
      ],

      deep: [
        { t: 'trace', title: 'aExists_mono',
          start: 'α : Sort u\nP Q : α → Assertion\nh : ∀ (x : α), P x ⊢ Q x\n⊢ aExists P ⊢ aExists Q',
          steps: [
            { tac: 'intro σ hh ⟨x, hp⟩',
              state: 'α : Sort u\nP Q : α → Assertion\nh : ∀ (x : α), P x ⊢ Q x\nσ : Store\nhh : Heap\nx : α\nhp : P x σ hh\n⊢ aExists Q σ hh',
              h: 'The pattern did two jobs: introduced the premise and destructed it. <code>intro σ hh hex</code> followed by <code>obtain ⟨x, hp⟩ := hex</code> produces the same state in two lines.' },
            { tac: 'exact ⟨x, h x σ hh hp⟩',
              h: 'The goal <code>aExists Q σ hh</code> is <code>∃ y, Q y σ hh</code>; supply <code>x</code> and push <code>hp</code> along the pointwise entailment.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'lseg_append, the nil case (real Lean output)',
          start: '⊢ ∀ (xs ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',
          steps: [
            { tac: 'intro xs  ·  induction xs with  ·  | nil =>',
              state: 'case nil\n⊢ ∀ (ys : List Nat) (p q r : Loc), lseg [] p q ∗ lseg ys q r ⊢ lseg ([] ++ ys) p r',
              h: 'The four remaining variables are still under the <code>∀</code>. The label <code>case nil</code> is what the <code>| nil =></code> syntax matches on.' },
            { tac: 'intro ys p q r σ h hstar',
              state: 'case nil\nys : List Nat\np q r : Loc\nσ : Store\nh : Heap\nhstar : (lseg [] p q ∗ lseg ys q r) σ h\n⊢ lseg ([] ++ ys) p r σ h',
              h: 'The goal keeps <code>[] ++ ys</code> unevaluated. Lean does not normalise goals for display; it reduces when it needs to, at the very end.' },
            { tac: 'obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
              state: 'case nil\nys : List Nat\np q r : Loc\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhys : lseg ys q r σ h₂\nhpq : fact (fun x => p = q) σ h₁\nhe : emp σ h₁\n⊢ lseg ([] ++ ys) p r σ h',
              h: '<code>left✝</code> is the field discarded with <code>_</code>; the dagger makes it unusable even by typing that name. And <code>hpq : fact (fun x => p = q) σ h₁</code> is the equation you need, in costume.' },
            { tac: 'have hpq\' : p = q := hpq  ·  subst hpq\'',
              state: 'case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhys : lseg ys p r σ h₂\nhpq : fact (fun x => p = p) σ h₁\n⊢ lseg ([] ++ ys) p r σ h',
              h: '<code>q</code> is gone and <code>hys</code> now reads <code>lseg ys p r σ h₂</code>, the shape of the goal. <code>hpq</code> survives as the now-trivial <code>fact (fun x => p = p)</code>, because it was <code>hpq\'</code>, not <code>hpq</code>, that <code>subst</code> consumed.' },
            { tac: 'subst he',
              state: 'case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₂ : Heap\nhys : lseg ys p r σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhpq : fact (fun x => p = p) σ Heap.empty\n⊢ lseg ([] ++ ys) p r σ h',
              h: '<code>h₁</code> is replaced by <code>Heap.empty</code> everywhere. <code>subst</code> took <code>he</code> directly, with no ascription, because <code>emp</code> unfolds to a bare equation between heaps rather than to an application of <code>fact</code>.' },
            { tac: 'rw [hu, union_empty_left]',
              state: 'case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₂ : Heap\nhys : lseg ys p r σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhpq : fact (fun x => p = p) σ Heap.empty\n⊢ lseg ([] ++ ys) p r σ h₂',
              h: 'Only the goal’s heap argument changed: <code>h</code> → <code>Heap.empty.union h₂</code> → <code>h₂</code>. The goal still says <code>[] ++ ys</code>, and <code>exact hys</code> closes it anyway.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'lseg_append, the cons case — step by step, no heaps (real Lean output)',
          start: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\n⊢ ∀ (ys : List Nat) (p q r : Loc), lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r',
          steps: [
            { tac: 'intro ys p q r',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\n⊢ lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r',
              h: 'The goal is an entailment, not a proposition about a heap. Read <code>x :: xs ++ ys</code> as <code>x :: (xs ++ ys)</code> — <code>::</code> binds looser than <code>++</code>.' },
            { tac: 'refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\n⊢ lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r',
              h: 'Identical to the previous state, as composing with an identity must be.' },
            { tac: 'refine entails_trans (star_exists_left _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\n⊢ (aExists fun x_1 => ((_root_.pure fun x => p ≠ 0) ∗ node p x x_1 ∗ lseg xs x_1 q) ∗ lseg ys q r) ⊢\n    lseg (x :: xs ++ ys) p r',
              h: 'Three printer quirks, all harmless. <code>x_1</code> is the bound next pointer, renamed because <code>x</code> is taken. <code>_root_.pure</code> is our <code>pure</code>, qualified because <code>Pure.pure</code> is also in scope. And the entailment is line-wrapped with the right-hand side indented — the <code>⊢</code> ending the first line is the <code>Entails</code> arrow, not a second goal.' },
            { tac: 'refine aExists_mono (fun n => ?_)',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ ((_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg (xs.append ys) n r',
              h: 'Both existentials are gone and <code>n : Nat</code> is in the context. The right-hand side unfolded a layer too, so you can see what has to match what. It prints <code>xs.append ys</code> on the right while <code>ih</code> says <code>xs ++ ys</code>: same term, two notations, no tactic needed to reconcile them.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ (_root_.pure fun x => p ≠ 0) ∗ (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg (xs.append ys) n r',
              h: 'The outermost bracket has moved, and both sides now begin with the same factor.' },
            { tac: 'refine star_mono_right _ ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r',
              h: 'This is where the non-null side condition is discharged: it is carried across unchanged, which is possible only because it is the <i>same</i> condition on both sides — <code>p ≠ 0</code>, not <code>p ≠ q</code> against <code>p ≠ r</code>.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ node p x n ∗ lseg xs n q ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r',
              h: 'The two segments are adjacent under a common <code>node p x n</code>. Strip that prefix from both sides and you have <code>ih ys n q r</code> exactly.' }
          ],
          done: 'No goals — the final <code>exact star_mono_right _ (ih ys n q r)</code> closes it.' },
        { t: 'detail', title: 'The first <code>refine</code> is a no-op, and you can delete it', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The trace shows the goal unchanged across <code>refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_</code>. That is not a display artefact — the proof compiles without the line.' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — the corpus keeps the extra line. This version compiles against the M10 prelude and produces the same theorem.',
              src: 'theorem lseg_append\' : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq\' : p = q := hpq\n      subst hpq\'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)' },
            { t: 'p', h: 'It is in the corpus because it names the thing about to happen: <code>star_exists_left</code> only applies once you accept that <code>lseg (x :: xs) p q</code> <i>is</i> an <code>aExists</code>, and the explicit <code>entails_refl (lseg (x :: xs) p q)</code> is a place to write that down. Whether that is worth a line is taste; knowing it is optional is not. When a tactic leaves the goal untouched, find out whether it did anything — lines that do nothing accumulate, and each is a small lie about what the argument needs.' }
          ] }
      ],

      pitfall: 'Reaching for the induction hypothesis one <code>star_assoc_left</code> too early. After <code>refine star_mono_right _ ?_</code> the goal is still left-bracketed, <code>(node p x n ∗ lseg xs n q) ∗ lseg ys q r</code>, and <code>exact star_mono_right _ (ih ys n q r)</code> fails with a message that shows the problem if you read both halves:<br><code>has type ?m.52 ∗ lseg xs n q ∗ lseg ys q r ⊢ ?m.52 ∗ lseg (xs ++ ys) n r</code><br><code>but is expected to have type (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r</code><br>The two types are identical except for the brackets on the left of the second. One more <code>entails_trans (star_assoc_left _ _ _)</code> fixes it. When a <code>star_mono</code> lemma refuses an argument, check the association before anything else.',

      variants: 'Change the cons side condition to <code>start ≠ finish</code> and the chain gets three steps further and then stops: <code>aExists_mono</code> and the first <code>star_assoc_left</code> both succeed, and the tactic that cannot be taken is <code>refine star_mono_right _ ?_</code>, because the sides no longer begin with the same factor — <code>pure (p ≠ q)</code> against <code>pure (p ≠ r)</code>. Drop the side condition altogether and <code>lseg_append</code> gets <i>easier</i>, which is the trap: this theorem is not what forces you to keep it. Agreement with <code>listRep</code> is, and the counterexample is in the next exercise. Finally, reverse the entailment: <code>lseg (xs ++ ys) p r ⊢ lseg xs p q ∗ lseg ys q r</code> is false for any fixed <code>q</code>, because appending forgets where the join was and no assertion about the combined segment can recover it.'
    },

    {
      t: 'ex',
      id: 'm10-5',
      name: 'lseg_listRep',
      hard: false,

      why: 'A segment followed by a complete list is a complete list. This closes a traversal: at the end, the visited prefix and the remaining suffix reassemble into the original list.',

      setup: 'Same toolkit, with <code>aExists_mono</code> now available. The only change in the statement is that the second conjunct is a <code>listRep</code>, so there is one fewer location variable.',

      goal: 'theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),\n    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p',

      hints: [
        'Same induction, same chain. Set it up exactly as before: <code>∀</code> inside the statement, <code>intro xs</code>, <code>induction xs with</code>.',
        'The nil case is word for word the nil case of <code>lseg_append</code> — the only thing that changed is the predicate on the right of the star, and the proof never mentions it.',
        'The cons case is the previous cons case with one argument fewer at the end: <code>ih ys n q</code>, not <code>ih ys n q r</code>. You will not need the opening <code>star_mono_left</code> line.'
      ],

      sol: 'theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),\n    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq\' : p = q := hpq\n      subst hpq\'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q)',

      expl: 'Structurally identical to <code>lseg_append</code>, which is the sign that the definitions are aligned. Had <code>lseg</code> kept <code>start ≠ finish</code>, this is the proof that would have failed first: the segment’s side condition would be about <code>q</code> while the list’s is about <code>0</code>.',

      walk: [
        { tac: 'intro xs',
          h: 'Only the induction variable, so that the hypothesis can be used at a different start pointer.' },
        { tac: 'induction xs with',
          h: 'Two branches, <code>nil</code> and <code>cons</code>.' },
        { tac: '| nil =>',
          h: 'Goal: <code>∀ ys p q, lseg [] p q ∗ listRep ys q ⊢ listRep ([] ++ ys) p</code>. Unfolded: <code>p = q</code> on the empty heap, starred with a list at <code>q</code>, gives a list at <code>p</code>.' },
        { tac: 'intro ys p q σ h hstar',
          h: 'Six introductions — one fewer than <code>lseg_append</code>, since there is no <code>r</code>.' },
        { tac: 'obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
          h: 'Six fields, disjointness discarded, the <code>pure</code> split into <code>fact</code> and <code>emp</code>. The second conjunct happens to be a <code>listRep</code> now, and <code>hys</code> records it.' },
        { tac: 'have hpq\' : p = q := hpq',
          h: 'Ascribe the <code>fact</code> to its underlying equational type.' },
        { tac: 'subst hpq\'',
          h: 'Eliminates <code>q</code>, so <code>hys : listRep ys p σ h₂</code>.' },
        { tac: 'subst he',
          h: 'Eliminates <code>h₁</code> in favour of <code>Heap.empty</code>.' },
        { tac: 'rw [hu, union_empty_left]',
          h: 'The goal’s heap becomes <code>h₂</code>.' },
        { tac: 'exact hys',
          h: 'Closes up to definitional equality: the goal says <code>listRep ([] ++ ys) p</code>, the hypothesis says <code>listRep ys p</code>, and <code>[] ++ ys</code> reduces.' },
        { tac: '| cons x xs ih =>',
          h: 'Head, tail, and an induction hypothesis quantified over <code>ys</code>, <code>p</code>, <code>q</code>.' },
        { tac: 'intro ys p q',
          h: 'Three introductions, and no descent into the model.' },
        { tac: 'refine entails_trans (star_exists_left _ _) ?_',
          h: 'Pull the existential of <code>lseg (x :: xs) p q</code> out from under the star.' },
        { tac: 'refine aExists_mono (fun n => ?_)',
          h: 'Go under the binder. Both sides are existentials — the right one because <code>listRep (x :: xs ++ ys) p</code> also opens with <code>aExists</code>, which is precisely the alignment the two definitions were built to have.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'Re-bracket so <code>pure (fun _ => p ≠ 0)</code> is the outer left factor on both sides.' },
        { tac: 'refine star_mono_right _ ?_',
          h: 'Cancel it. Impossible if <code>lseg</code>’s side condition were <code>p ≠ q</code> and <code>listRep</code>’s were <code>p ≠ 0</code>.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'Re-bracket again, making <code>lseg xs n q</code> and <code>listRep ys q</code> adjacent.' },
        { tac: 'exact star_mono_right _ (ih ys n q)',
          h: 'Peel off <code>node p x n</code> and apply the induction hypothesis at the next pointer. Three arguments, not four.' }
      ],

      deep: [
        { t: 'p', h: 'The nil case is character-for-character the nil case of <code>lseg_append</code> minus the unused <code>r</code>, so its trace is the one in the previous exercise. The cons case is where the alignment of the two definitions shows.' },
        { t: 'trace', title: 'lseg_listRep, the cons case (real Lean output)',
          start: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\n⊢ ∀ (ys : List Nat) (p q : Loc), lseg (x :: xs) p q ∗ listRep ys q ⊢ listRep (x :: xs ++ ys) p',
          steps: [
            { tac: 'intro ys p q',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\n⊢ lseg (x :: xs) p q ∗ listRep ys q ⊢ listRep (x :: xs ++ ys) p',
              h: 'Two different predicates in one entailment. Nothing in the proof will ever need to know that they are different, which is the point.' },
            { tac: 'refine entails_trans (star_exists_left _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\n⊢ (aExists fun x_1 => ((_root_.pure fun x => p ≠ 0) ∗ node p x x_1 ∗ lseg xs x_1 q) ∗ listRep ys q) ⊢\n    listRep (x :: xs ++ ys) p',
              h: 'The left side has unfolded and the existential is outermost. The right side is untouched — <code>aExists_mono</code> will unfold it by unifying against the goal.' },
            { tac: 'refine aExists_mono (fun n => ?_)',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ ((_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ listRep (xs.append ys) n',
              h: 'Two <code>_root_.pure fun x => p ≠ 0</code>, one on each side, and they are the <i>same assertion</i>. This one line is the entire content of the warning earlier in the chapter.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ (_root_.pure fun x => p ≠ 0) ∗ (node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ listRep (xs.append ys) n',
              h: 'Both sides now begin with the identical factor.' },
            { tac: 'refine star_mono_right _ ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ (node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢ node p x n ∗ listRep (xs.append ys) n',
              h: 'Cancelled. What is left is the node plus a strictly smaller instance of the theorem.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ node p x n ∗ lseg xs n q ∗ listRep ys q ⊢ node p x n ∗ listRep (xs.append ys) n',
              h: 'Strip <code>node p x n ∗</code> from both sides and compare with <code>ih</code>: identical at <code>p := n</code>.' }
          ],
          done: 'No goals — the final <code>exact star_mono_right _ (ih ys n q)</code> closes it.' },
        { t: 'p', h: 'One corollary is the form the lemma takes at the end of a traversal: a segment that runs to null <i>is</i> a list.' },
        { t: 'code', tag: 'illustration',
          cap: 'Not in the corpus — compiled against the M10 prelude.',
          src: 'theorem lseg_null_is_listRep (xs : List Nat) (p : Loc) :\n    lseg xs p 0 ⊢ listRep xs p := by\n  intro σ h hl\n  have hstar : (lseg xs p 0 ∗ listRep [] 0) σ h :=\n    ⟨h, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hl, rfl, rfl⟩\n  have hres := lseg_listRep xs [] p 0 σ h hstar\n  rw [List.append_nil] at hres\n  exact hres' },
        { t: 'p', h: 'The star is manufactured by hand with <code>Heap.empty</code> on the right, because <code>listRep [] 0</code> is satisfied by the empty heap and nothing else. And <code>rw [List.append_nil]</code> <i>is</i> needed here, unlike the <code>[] ++ ys</code> of the nil cases: <code>List.append</code> recurses on its <b>first</b> argument, so <code>[] ++ ys</code> reduces to <code>ys</code> definitionally while <code>xs ++ []</code> does not reduce to <code>xs</code> at all. That one is a theorem, proved by induction.' },
        { t: 'detail', title: 'Breaking it: what the <code>p ≠ 0</code> conjunct is actually buying', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'Neither append theorem needs the non-null side condition — delete it from both definitions and both proofs get shorter. Keep it because without it the null pointer no longer decides emptiness, and the predicate stops describing linked lists. A concrete heap, checked by Lean:' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — compiled against the M10 prelude. With <code>p ≠ 0</code> removed, the two-cell heap {0 ↦ 7, 1 ↦ 0} satisfies “the one-element list [7] starting at the null pointer”.',
              src: 'def listRepBad : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p => aExists fun next => node p x next ∗ listRepBad xs next\n\nexample : listRepBad [7] 0 (fun _ => 0)\n    (Heap.union (Heap.singleton 0 7) (Heap.singleton 1 0)) :=\n  ⟨0,\n   Heap.union (Heap.singleton 0 7) (Heap.singleton 1 0), Heap.empty,\n   disjoint_empty_right _, (union_empty_right _).symm,\n   ⟨Heap.singleton 0 7, Heap.singleton 1 0, singleton_disjoint 7 0 (by decide), rfl, rfl, rfl⟩,\n   ⟨rfl, rfl⟩⟩' },
            { t: 'p', h: 'That heap does <i>not</i> satisfy <code>listRepBad [] 0</code> — the nil clause still demands the empty heap — so the two assertions are not literally interchangeable. What is gone is the implication you rely on. With the side condition in place, a null start pointer forces the list to be empty, in three lines:' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — compiled against the M10 prelude. The seventh field of the bracket is the tail; the sixth splits <code>pure φ</code>, and its first component is <code>0 ≠ 0</code>.',
              src: 'theorem listRep_cons_null (x : Nat) (xs : List Nat) :\n    listRep (x :: xs) 0 ⊢ aFalse := by\n  intro σ h ⟨_, _, _, _, _, ⟨hne, _⟩, _⟩\n  exact hne rfl' },
            { t: 'p', h: 'Delete <code>p ≠ 0</code> and that lemma is false, so a traversal that stops when <code>p = 0</code> is being verified against a predicate which permits it to stop with elements still in the list — and the logic will not object. The side condition is what makes “the pointer is null” and “the list is empty” the <i>same</i> statement, and that equivalence is the contract every traversal relies on.' }
          ] }
      ],

      pitfall: 'Copying the cons case from <code>lseg_append</code> without dropping the fourth argument. <code>ih</code> here takes three, and <code>ih ys n q q</code> produces an error that does not mention arity at all:<br><code>Application type mismatch: The last q argument has type Loc but is expected to have type Store — in the application ih ys n q q</code><br>After three arguments the induction hypothesis is an <code>Entails</code>, which unfolds to <code>∀ σ h, …</code>, so the fourth argument is read as the store. Whenever Lean says your <code>Loc</code> should be a <code>Store</code>, you have over-applied something whose result was an entailment.',

      variants: 'Swap the two conjuncts — <code>listRep ys q ∗ lseg xs p q ⊢ listRep (xs ++ ys) p</code> — and the statement stays true, but the proof needs a <code>star_comm</code> at the top and the chain no longer lines up; the order in the statement is not arbitrary. Replace <code>listRep ys q</code> by <code>lseg ys q r</code> and you are back at <code>lseg_append</code>. Take <code>xs = []</code> and the theorem degenerates to its own nil case, which is a cheap check that the statement says what you meant. And removing <code>p ≠ 0</code> from <code>listRep</code> leaves the theorem true and the predicate useless; the counterexample is in the collapsed block above.',

      solNote: 'The two proofs are the same proof, and that is a claim about the definitions rather than about the proofs: <code>lseg</code> and <code>listRep</code> differ only in their base case, and neither induction ever inspects a base case of the <i>second</i> argument. Add a third linked-structure predicate and expect a third copy — then consider whether one parametrised lemma would do.'
    },

    { t: 'h3', s: 'Where the algebra stops' },

    { t: 'p',
      h: 'Both theorems run one way. You own two adjacent pieces and you get one, and nothing here runs backwards — <code>lseg (xs ++ ys) p r ⊢ lseg xs p q ∗ lseg ys q r</code> is false for any <code>q</code> fixed in advance, because the joined segment does not record where the join was. That is survivable as long as everything you own stays in your hands.' },

    { t: 'p',
      h: 'It stops being survivable the moment you lend a piece out. A traversal reaches the node at <code>cur</code> and hands <code>node cur x n</code> to a subroutine. Write down what you are still holding. You have <code>lseg visited p cur</code>, you have <code>listRep rest n</code>, and you have one more thing that is worth more than either: the standing promise that when the node comes back, these become a list again. The first two are assertions. The third is what makes the remainder worth keeping, and there is no <code>∗</code> of anything you own that states it — every connective so far describes memory you have, and this one has to describe memory you will get. M11 is the connective for that.' },

    { t: 'dod',
      h: 'You can define, unfold, fold and recombine ownership of recursive pointer structures, and you can do it with the ∗-algebra rather than by hand.' }
  ]
});
