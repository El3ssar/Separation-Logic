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
      'Write a recursive assertion in Lean and say exactly which heap cells it claims',
      'Read goals like <code>(aExists fun x_1 =&gt; ((_root_.pure fun x =&gt; p ≠ 0) ∗ …) ∗ …) ⊢ …</code> without flinching',
      'Build a concrete three-node list by hand, choosing every heap cut and every existential witness yourself',
      'Prove <code>lseg_append</code> — two adjacent segments make one segment — as a chain of ∗-algebra lemmas, with no heap variables anywhere',
      'Recognise a wrong side condition in a definition from the shape of the proof obligation it leaves behind'
    ],
    needs: [
      'M4: <code>entails_trans</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>, <code>star_exists_left</code>',
      'M3: <code>emp</code>, <code>fact</code>, and that <code>pure φ</code> is by definition <code>aAnd (fact φ) emp</code>',
      'M2: <code>Heap.union</code>, <code>Heap.disjoint</code>, <code>union_empty_left</code>, <code>disjoint_empty_left</code>',
      'The tactic habits from M8–M9: <code>intro σ h hstar</code>, <code>obtain ⟨…⟩</code>, <code>refine … ?_</code>, <code>subst</code>'
    ],
    payoff: 'Every loop invariant in M13 is a list segment, and the single lemma that maintains it across an iteration is the one you prove here.'
  },

  blocks: [
    { t: 'h3', s: 'The idea' },

    { t: 'p',
      h: 'So far every assertion has described a bounded number of cells. To describe a linked list you need recursion, and the striking thing about the definition is that it says two things at once: <b>what shape the pointers form</b>, and <b>which cells you own</b>.' },

    { t: 'p',
      h: 'Layout: a node at <code>p</code> occupies two consecutive cells — <code>p</code> holds the element, <code>p + 1</code> holds the next pointer. Location <code>0</code> is null.' },

    { t: 'svg',
      src: "\n<svg viewBox=\"0 0 560 150\" role=\"img\" aria-label=\"A linked list in the heap\">\n  <g class=\"dg\">\n    <g class=\"dg-cells\">\n      <rect x=\"24\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"a\"/><text x=\"45\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">10</text>\n      <rect x=\"66\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"b\"/><text x=\"87\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">•</text>\n      <rect x=\"204\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"a\"/><text x=\"225\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">20</text>\n      <rect x=\"246\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"b\"/><text x=\"267\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">•</text>\n      <rect x=\"384\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"a\"/><text x=\"405\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">30</text>\n      <rect x=\"426\" y=\"46\" width=\"42\" height=\"30\" rx=\"4\" class=\"b\"/><text x=\"447\" y=\"66\" text-anchor=\"middle\" class=\"dg-t sm\">0</text>\n    </g>\n    <path class=\"dg-arr\" d=\"M108 61 L 200 61\"/>\n    <path class=\"dg-arr\" d=\"M288 61 L 380 61\"/>\n    <text x=\"45\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">p</text>\n    <text x=\"225\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">p'</text>\n    <text x=\"405\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">p''</text>\n    <text x=\"45\" y=\"100\" text-anchor=\"middle\" class=\"dg-note\">p ↦ 10</text>\n    <text x=\"87\" y=\"100\" text-anchor=\"middle\" class=\"dg-note\">p+1 ↦ p'</text>\n    <text x=\"490\" y=\"100\" text-anchor=\"middle\" class=\"dg-note\">0 = null</text>\n    <text x=\"12\" y=\"132\" class=\"dg-note\">listRep [10,20,30] p owns all six cells and asserts they are linked in this order.</text>\n  </g>\n</svg>" },

    { t: 'p',
      h: 'Two Lean-specific things happen in the definition below before any separation logic does, and both are worth naming. First, <code>listRep</code> is written as a <i>pattern-matching</i> definition — one clause for <code>[]</code>, one for <code>x :: xs</code>. Lean compiles that into a function that reduces the moment its list argument is a literal constructor application. That single fact is why the three folding lemmas in the first exercise are all <code>entails_refl</code>. Second, the result type is <code>Assertion</code>, not <code>Prop</code>. So <code>listRep xs p</code> is a function <code>Store → Heap → Prop</code>, the recursion produces assertions rather than propositions, and the connective between them is the <code>∗</code> of M4 — not <code>∧</code>, and not Lean’s <code>And</code>.' },

    { t: 'code',
      src: 'def node (p : Loc) (value next : Nat) : Assertion :=\n  (p ↦ value) ∗ ((p + 1) ↦ next)\n\ndef listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next' },

    { t: 'anat',
      src: 'def listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next',
      parts: [
        { m: 'List Nat → Loc → Assertion',
          h: 'The recursion is on the <i>mathematical</i> list, not on the heap. <code>listRep xs p</code> means “the heap I own is exactly a linked list holding the values <code>xs</code>, starting at <code>p</code>”. Lean accepts the definition because it is structurally recursive in the list argument — every recursive call drops one constructor — and it finds that argument by itself. Putting the list first is a readability choice, not a requirement: the same clauses with the two arguments swapped, matching on the second, compile equally well.' },
        { m: '| [],      p => pure (fun _ => p = 0)',
          h: 'The empty list. Two claims fused into one: the pointer is null, <i>and</i> I own nothing. <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so the <code>emp</code> half is doing real work — it is what makes <code>listRep</code> an exact ownership claim rather than “at least this”.' },
        { m: 'aExists fun next =>',
          h: 'The next pointer is not an argument of <code>listRep</code>, because a caller who owns a list does not know where the second node lives. So it is existentially quantified <i>inside</i> the assertion. <code>aExists</code> is the assertion-level ∃ from M3: <code>aExists P = fun σ h => ∃ x, P x σ h</code>. When you unfold a list you will be <i>given</i> this witness; when you build one you must <i>supply</i> it.' },
        { m: 'pure (fun _ => p ≠ 0)',
          h: 'The side condition that makes <code>0</code> mean “end of list”. Without it, <code>listRep [7] 0</code> would be satisfiable and the null pointer would no longer decide whether the list is empty. Note the <code>fun _ =></code>: a <code>fact</code> takes the store as an argument, and this one ignores it — <code>p</code> is a Lean variable, not a program variable.' },
        { m: 'node p x next',
          h: 'The two cells of this node: <code>(p ↦ x) ∗ ((p + 1) ↦ next)</code>. Because it is <code>∗</code> and not <code>∧</code>, owning a node already tells you <code>p ≠ p + 1</code>. That is exercise 2.' },
        { m: 'listRep xs next',
          h: 'The tail, in a <i>separate</i> part of the heap. This is the recursive call, and the <code>∗</code> in front of it is the entire non-aliasing argument: the tail’s cells are disjoint from this node’s cells, hence from every earlier node’s cells, hence the structure cannot loop back on itself.' }
      ] },

    { t: 'p',
      h: 'Unfold <code>listRep [10,20,30] p</code> mentally and you get: “there is a next pointer <code>n₁</code>, <code>p</code> is non-null, I own <code>p ↦ 10</code> and <code>p+1 ↦ n₁</code>, and separately I own a list <code>[20,30]</code> starting at <code>n₁</code>”. The <code>∗</code>s do all the work: they guarantee that the six cells are <i>six different cells</i>, so the list cannot secretly be a lasso.' },

    { t: 'dl', items: [
      { k: 'aExists', h: 'Assertion-level existential, <code>aExists P = fun σ h => ∃ x, P x σ h</code>. Unfolding gives you a witness; folding costs you one.' },
      { k: 'pure φ', h: '<code>aAnd (fact φ) emp</code>. A store-level fact <i>plus</i> a claim to own nothing. The pure conjunct of a recursive predicate always sits on an empty heap — that is why every heap equation involving it comes out as <code>union_empty_left</code>.' },
      { k: 'fact φ', h: '<code>fun σ _ => φ σ</code>. True of <i>any</i> heap. Use it when you want to state a consequence and do not want to claim memory — the right-hand side of exercise 2 is a <code>fact</code>, not a <code>pure</code>.' },
      { k: '∗ associativity', h: '<code>∗</code> is declared <code>infixr</code>, so <code>A ∗ B ∗ C</code> parses as <code>A ∗ (B ∗ C)</code>. Every star in <code>listRep</code>’s cons clause is right-nested, and half the work in the append proofs is re-bracketing to match.' }
    ] },

    { t: 'detail', title: 'Why <code>pure</code> in the nil case, and not <code>fact</code>', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'Suppose the empty clause were <code>fact (fun _ => p = 0)</code> instead. <code>fact φ</code> holds of <i>every</i> heap, so <code>listRep [] 0</code> would be satisfied by a heap containing anything at all.' },
        { t: 'p', h: 'Now look at <code>listRep [x] p</code>. It unfolds to “own <code>node p x next</code>, and separately satisfy <code>listRep [] next</code>”. With the <code>emp</code> gone, that second conjunct places no constraint on its half of the heap — so a single-element list could quietly claim an unbounded amount of extra memory. The predicate stops being an exact footprint and becomes “at least this”.' },
        { t: 'p', h: 'Everything downstream breaks with it. The frame rule of M8 works because a precondition names exactly what a command may touch; a leaky <code>listRep</code> would let a specification silently absorb the frame. This is the same design choice as <code>l ↦ v</code> being <code>h = Heap.singleton l v</code> rather than <code>h l = some v</code>, made one level up.' }
      ] },

    { t: 'cmp',
      left:  { t: 'The shape predicate you would write first',
               h: 'Quantify over the node addresses and say the cells are linked:<br><code>∃ l₀ l₁ l₂, h l₀ = some 10 ∧ h (l₀+1) = some l₁ ∧ …</code><br>This is a perfectly good statement about a heap. It is also useless as a precondition: it does not say the six cells are distinct, it does not say the heap contains nothing else, and it stays true when you add junk. Two such lists can overlap; a “list” can be a lasso.' },
      right: { t: 'The separation-logic predicate', kind: 'good',
               h: 'Replace every <code>∧</code> by <code>∗</code> and make the base case <code>emp</code>. Distinctness is no longer an extra hypothesis you have to state and carry — it is a <i>consequence</i> of the connective. Exactness is likewise automatic. The recursive definition is now simultaneously a shape invariant and a resource, which is the whole reason separation logic scales to pointer programs.' } },

    { t: 'note', kind: 'key', title: 'The one thing to remember',
      h: 'A recursive separation-logic predicate is simultaneously a <b>shape invariant</b> and an <b>ownership claim</b>. That is why unfolding one gives you non-aliasing for free, and why you can hand the whole structure to a function by handing over a single assertion.' },

    { t: 'p',
      h: 'Here is the non-aliasing in its smallest form. You cannot own the same cell twice, because the two halves of a <code>∗</code> must be disjoint heaps and a singleton heap is not disjoint from itself:' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus — compiled against the M10 prelude. This is the reason a <code>listRep</code> cannot be a lasso: a cycle would force some node to be owned twice.',
      src: 'theorem cell_not_duplicable (p : Loc) (x y : Val) : (p ↦ x) ∗ (p ↦ y) ⊢ aFalse := by\n  intro σ h hstar\n  exact absurd rfl (two_cells_distinct p p x y σ h hstar)' },

    { t: 'p',
      h: 'Two Lean details before the mathematics. After <code>intro σ h hstar</code> the goal is <code>aFalse σ h</code>, and <code>aFalse</code> is <code>fun _ _ => False</code>, so the goal <i>is</i> <code>False</code> — no unfolding tactic required. And <code>absurd : a → ¬a → b</code> is the standard term for “from a proposition and its negation, conclude anything”; here <code>b</code> is <code>False</code>. So read the proof as: <code>two_cells_distinct p p x y</code> concludes <code>p ≠ p</code>, and <code>rfl : p = p</code> refutes it. There is no arithmetic anywhere. The contradiction comes from <code>Heap.disjoint</code>, and it would survive a change of location type.' },

    { t: 'h3', s: 'List segments' },

    { t: 'p',
      h: 'A segment describes the part of a list from <code>start</code> up to, but not including, <code>finish</code>. Segments are what loop invariants are made of: a traversal splits a list into “already visited” and “still to visit”.' },

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
      cap: 'The two definitions are deliberately parallel. Line 3 is the one that is easy to get wrong, and the next note is about exactly that.' },

    { t: 'note', kind: 'warn', title: 'A bug in the definition, and how it announces itself',
      h: 'The original syllabus puts the side condition <code>start ≠ finish</code> in the cons case. With that definition <b><code>lseg_append</code> is not provable</b>: after appending, you have a proof that <code>p ≠ q</code> but the goal demands <code>p ≠ r</code>, and nothing connects them. It is unprovable because it is <i>false</i> — the collapsed block below exhibits the two-node cycle that refutes it. The condition must be <b><code>start ≠ 0</code></b> — the same non-null condition <code>listRep</code> uses. Then both <code>lseg_append</code> and <code>lseg_listRep</code> go through by a clean induction, and the two predicates fit together. This is worth pausing on: the “obvious” definition was subtly wrong, and the theorem you could not prove is what told you.' },

    { t: 'detail', title: 'The bug, in Lean, with the goal state that reveals it', tag: 'worth doing', open: false,
      blocks: [
        { t: 'p', h: 'Define the wrong version and start the append proof the same way. Three tactics into the cons case, Lean shows you the problem directly.' },
        { t: 'code', tag: 'sketch',
          src: 'def lsegBad : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next =>\n        pure (fun _ => start ≠ finish) ∗ node start x next ∗ lsegBad xs next finish\n\nexample : ∀ (xs ys : List Nat) (p q r : Loc),\n    lsegBad xs p q ∗ lsegBad ys q r ⊢ lsegBad (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil => sorry\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      trace_state\n      sorry' },
        { t: 'state',
          cap: 'Real output. Left of the ⊢ you have p ≠ q; right of it the goal wants p ≠ r. There is no hypothesis relating q and r, and no amount of ∗-algebra will produce one.',
          src: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lsegBad xs p q ∗ lsegBad ys q r ⊢ lsegBad (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ ((_root_.pure fun x => p ≠ q) ∗ node p x n ∗ lsegBad xs n q) ∗ lsegBad ys q r ⊢\n    (_root_.pure fun x => p ≠ r) ∗ node p x n ∗ lsegBad (xs.append ys) n r' },
        { t: 'p', h: 'A stuck goal is not by itself evidence that a theorem is false — you might merely be proving it badly. Here it <i>is</i> false, and the witness is exactly the thing recursive predicates are supposed to control: a cycle. Put two nodes at addresses <code>10</code> and <code>20</code> pointing at each other. Then <code>lsegBad [7] 10 20</code> holds (its side condition is <code>10 ≠ 20</code>), <code>lsegBad [8] 20 10</code> holds (<code>20 ≠ 10</code>), and the two own disjoint cells — but the conclusion <code>lsegBad [7, 8] 10 10</code> demands <code>10 ≠ 10</code>.' },
        { t: 'code', tag: 'illustration',
          cap: 'Not in the corpus — compiled against the M10 prelude. The heap is {10 ↦ 7, 11 ↦ 20, 20 ↦ 8, 21 ↦ 10}: two nodes, each pointing at the other.',
          src: 'theorem lsegBad_append_false :\n    ¬ (∀ (xs ys : List Nat) (p q r : Loc),\n        lsegBad xs p q ∗ lsegBad ys q r ⊢ lsegBad (xs ++ ys) p r) := by\n  intro hcontra\n  let hA := Heap.union (Heap.singleton 10 7) (Heap.singleton 11 20)\n  let hB := Heap.union (Heap.singleton 20 8) (Heap.singleton 21 10)\n  have hd : Heap.disjoint hA hB :=\n    disjoint_union_left.mpr\n      ⟨disjoint_union_right.mpr ⟨singleton_disjoint 7 8 (by decide), singleton_disjoint 7 10 (by decide)⟩,\n       disjoint_union_right.mpr ⟨singleton_disjoint 20 8 (by decide), singleton_disjoint 20 10 (by decide)⟩⟩\n  have hprem : (lsegBad [7] 10 20 ∗ lsegBad [8] 20 10) (fun _ => 0) (Heap.union hA hB) :=\n    ⟨hA, hB, hd, rfl,\n     ⟨20, Heap.empty, hA, disjoint_empty_left _, (union_empty_left _).symm,\n       ⟨(by decide : (10:Nat) ≠ 20), rfl⟩,\n       ⟨hA, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm,\n         ⟨Heap.singleton 10 7, Heap.singleton 11 20, singleton_disjoint 7 20 (by decide), rfl, rfl, rfl⟩,\n         ⟨rfl, rfl⟩⟩⟩,\n     ⟨10, Heap.empty, hB, disjoint_empty_left _, (union_empty_left _).symm,\n       ⟨(by decide : (20:Nat) ≠ 10), rfl⟩,\n       ⟨hB, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm,\n         ⟨Heap.singleton 20 8, Heap.singleton 21 10, singleton_disjoint 8 10 (by decide), rfl, rfl, rfl⟩,\n         ⟨rfl, rfl⟩⟩⟩⟩\n  obtain ⟨n, _, _, _, _, ⟨hne, _⟩, _⟩ :=\n    hcontra [7] [8] 10 20 10 (fun _ => 0) (Heap.union hA hB) hprem\n  exact hne rfl' },
        { t: 'p', h: 'That is worth reading twice, because it says something about the <i>correct</i> definition too. With <code>start ≠ 0</code>, <code>lseg [7, 8] 10 10</code> is perfectly satisfiable — that same four-cell cycle satisfies it, and <code>lseg_append [7] [8] 10 20 10</code> applied to the two halves is what builds the proof. A segment in this logic is a chain of distinct cells starting at <code>start</code> and reaching <code>finish</code>; nothing rules out <code>finish</code> being back inside the chain. <code>start ≠ finish</code> tried to rule it out and, as a consequence, failed to be closed under append. The honest reading is that <code>lseg</code> is deliberately permissive, and acyclicity comes back at the point of use: in M13 the segment is always paired with a <code>listRep</code> running to null, and <code>listRep</code> <i>is</i> acyclic, because every node is separately owned and the chain terminates at <code>0</code>.' },
        { t: 'p', h: 'The moral is not “check your definitions”. It is that in a proof assistant a wrong definition is <i>discovered</i>, at a precise location, by a goal you cannot close. On paper you would have written “clearly” and moved on. Notice also that <code>start ≠ finish</code> is not even the property you wanted: the empty segment has <code>start = finish</code>, so the cons clause was asserting the segment is non-empty — true, but useless, and not what makes the pointer arithmetic work.' }
      ] },

    { t: 'p',
      h: 'The payoff of using the <i>same</i> side condition in both definitions is that segments and lists compose. A segment that ends at null is a complete list, and once you have <code>lseg_listRep</code> from the last exercise, that is four lines:' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus — compiled against the M10 prelude. The star is built by hand with the empty heap on the right, because <code>listRep [] 0</code> is satisfied by <code>Heap.empty</code>.',
      src: 'theorem lseg_null_is_listRep (xs : List Nat) (p : Loc) :\n    lseg xs p 0 ⊢ listRep xs p := by\n  intro σ h hl\n  have hstar : (lseg xs p 0 ∗ listRep [] 0) σ h :=\n    ⟨h, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hl, rfl, rfl⟩\n  have hres := lseg_listRep xs [] p 0 σ h hstar\n  rw [List.append_nil] at hres\n  exact hres' },

    { t: 'sec', s: 'Exercises · folding and unfolding' },

    {
      t: 'ex',
      id: 'm10-1',
      name: 'listRep_nil / listRep_cons_unfold / listRep_cons_fold',
      hard: false,

      why: 'These are the interface to the recursive predicate. State them explicitly even though they are trivial — it means later proofs cite a lemma instead of relying on how the equation compiler happened to unfold your definition.',

      setup: 'Three separate theorems. <code>listRep</code> and <code>node</code> are in scope; so is <code>entails_refl : ∀ (P : Assertion), P ⊢ P</code> from M3.',

      goal: 'theorem listRep_nil (p : Loc) :\n    listRep [] p ⊢ pure (fun _ => p = 0)\n\ntheorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next\n\ntheorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p',

      hints: [
        'Do not reach for a tactic. Ask first: as a <i>term</i>, what is <code>listRep (x :: xs) p</code>? The list argument is already a constructor application, so Lean can evaluate the pattern match without knowing anything about <code>x</code>, <code>xs</code> or <code>p</code>.',
        'If two assertions are literally the same term after that evaluation, then <code>P ⊢ Q</code> and <code>P ⊢ P</code> are the same proposition up to definitional equality — and Lean accepts a proof of one as a proof of the other with no coercion.',
        'So each is <code>entails_refl _</code>. The underscore is the assertion, which Lean infers from the expected type. Write all three as term-mode definitions (<code>:= entails_refl _</code>), not <code>by</code> blocks.'
      ],

      sol: 'theorem listRep_nil (p : Loc) : listRep [] p ⊢ pure (fun _ => p = 0) := entails_refl _\n\ntheorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next :=\n  entails_refl _\n\ntheorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p :=\n  entails_refl _',

      solNote: 'Note that <code>listRep_cons_unfold</code> and <code>listRep_cons_fold</code> have the same proof with the two sides swapped. Together they say <code>listRep (x :: xs) p ⊣⊢ …</code>: unfolding is reversible, and neither direction costs anything.',

      expl: 'Because <code>listRep</code> is defined by structural recursion on a <i>constructor</i> pattern, <code>listRep (x :: xs) p</code> reduces definitionally to the right-hand side. So the entailment is the identity. Naming it anyway is good hygiene: if you later change the definition, only these three lemmas break.',

      walk: [
        { tac: 'theorem listRep_nil … := entails_refl _',
          h: 'The stated conclusion is <code>listRep [] p ⊢ pure (fun _ => p = 0)</code>. Lean elaborates <code>entails_refl _</code> against that expected type, which forces the metavariable to be <code>listRep [] p</code>, and then has to check <code>listRep [] p ⊢ listRep [] p</code> against <code>listRep [] p ⊢ pure (fun _ => p = 0)</code>. It unfolds the pattern match on <code>[]</code>, sees the same term on both sides, and accepts.' },
        { tac: 'theorem listRep_cons_unfold … := entails_refl _',
          h: 'Same move, one clause down. <code>listRep (x :: xs) p</code> reduces to <code>aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next</code> — the exact right-hand side of the statement, including the right-nesting of the two stars.' },
        { tac: 'theorem listRep_cons_fold … := entails_refl _',
          h: 'Definitional equality is symmetric, so the same term proves the reverse entailment. There is no “folding lemma” to prove; there is only a name to give.' }
      ],

      deep: [
        { t: 'p', h: 'The thing to internalise here is <i>which</i> equality Lean is using. There are two, and the difference decides whether a proof is <code>rfl</code> or a page of work.' },
        { t: 'cmp',
          left:  { t: 'Definitional equality',
                   h: 'Two terms that the kernel can see are the same by unfolding definitions and evaluating pattern matches. <code>listRep (x :: xs) p</code> and its right-hand side are definitionally equal. Lean applies this <i>silently</i>, whenever it type-checks a term against an expected type. You never invoke it; you only notice when something works that you expected to need a lemma.' },
          right: { t: 'Propositional equality', kind: 'good',
                   h: 'An inhabitant of <code>a = b</code>, manipulated with <code>rw</code>, <code>subst</code>, <code>simp</code>. <code>rw</code> matches <i>syntactically</i>: it will not see through a definitional unfolding for you. That asymmetry is why, later in this chapter, <code>exact hys</code> closes a goal about <code>lseg ([] ++ ys) p r</code> from a hypothesis about <code>lseg ys p r</code>, while <code>rw</code> in the same position would need <code>List.nil_append</code> spelled out.' } },
        { t: 'p', h: 'The same phenomenon applies to <code>node</code>, which is a plain <code>def</code> rather than a pattern match — so it also unfolds definitionally:' },
        { t: 'code', tag: 'illustration',
          src: 'theorem node_is_two_cells (p : Loc) (x n : Nat) :\n    node p x n ⊢ (p ↦ x) ∗ ((p + 1) ↦ n) := entails_refl _' },
        { t: 'detail', title: 'When would <code>entails_refl</code> stop working?', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Not, as you might guess, if you replaced the pattern match by a decidable test. <code>if xs = [] then … else …</code> still reduces on both a <code>[]</code> and a <code>x :: xs</code>, because <code>DecidableEq (List Nat)</code> is itself defined by recursion on constructors: given two literal constructor applications it computes down to <code>isTrue</code> or <code>isFalse</code>, and the <code>if</code> unblocks. <code>entails_refl _</code> still works.' },
            { t: 'p', h: 'What does break it is <i>well-founded</i> recursion. Add a <code>termination_by</code> clause and Lean stops using the structural recursor and compiles the definition through <code>WellFounded.fix</code> instead. That term is blocked on an accessibility proof, so it does not reduce even when the list argument is <code>[]</code>:' },
            { t: 'code', tag: 'sketch',
              cap: 'The last line is the one that fails; everything above it compiles.',
              src: 'def listRepWF : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRepWF xs next\n  termination_by xs _ => xs.length\n\nexample (p : Loc) : listRepWF [] p ⊢ pure (fun _ => p = 0) := entails_refl _' },
            { t: 'state',
              cap: 'Real error. Lean cannot even see that the nil clause is the nil clause.',
              src: 'error: Type mismatch\n  entails_refl ?m.6\nhas type\n  ?m.6 ⊢ ?m.6\nbut is expected to have type\n  listRepWF [] p ⊢ _root_.pure fun x => p = 0' },
            { t: 'p', h: 'The repair is to use the equation lemmas Lean generated alongside the definition, which is what <code>simp only [listRepWF]</code> means: rewrite with the defining equations, propositionally, rather than hoping the kernel will unfold. After that the two sides are syntactically equal and <code>entails_refl</code> applies.' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — compiled against the M10 prelude, with the definition above.',
              src: 'theorem listRepWF_nil (p : Loc) : listRepWF [] p ⊢ pure (fun _ => p = 0) := by\n  simp only [listRepWF]\n  exact entails_refl _' },
            { t: 'p', h: 'So structural recursion is not a stylistic preference. It is the thing that makes the definition <i>compute</i>, and computation is what makes trivial lemmas trivial. When you meet a recursive definition in someone else’s development and a <code>rfl</code>-shaped proof unexpectedly fails, check whether it was defined by well-founded recursion before you doubt the statement.' }
          ] }
      ],

      pitfall: 'The proof is only <code>entails_refl _</code> if the right-hand side you wrote is <i>exactly</i> the definition, down to the bracketing. <code>∗</code> is <code>infixr</code>, so <code>pure φ ∗ node p x next ∗ listRep xs next</code> means <code>pure φ ∗ (node p x next ∗ listRep xs next)</code>. If you write <code>(pure φ ∗ node p x next) ∗ listRep xs next</code> instead, the two terms are no longer definitionally equal and <code>entails_refl</code> fails; you then need <code>star_assoc_left</code> or <code>star_assoc_right</code> to repair it. Renaming the bound variable — <code>fun n =></code> instead of <code>fun next =></code> — is harmless, because Lean identifies alpha-equivalent terms.',

      variants: 'Swap the two sides of <code>listRep_cons_unfold</code> and you get <code>listRep_cons_fold</code>: for a definitional unfolding, the two directions cost the same. That is <i>not</i> true of the exercises later in this chapter — <code>lseg_append</code> holds in one direction only, since the appended segment loses the information about where the join was. If you also swap the order of the conjuncts, say to <code>node p x next ∗ pure (fun _ => p ≠ 0) ∗ listRep xs next</code>, both directions are still true but neither is <code>entails_refl</code>: you have to route through <code>star_comm</code> and <code>star_assoc_left</code>.'
    },

    {
      t: 'ex',
      id: 'm10-2',
      name: 'node_cells_distinct',
      hard: false,

      why: 'Owning a node proves its two cells are different locations. Trivially true for <code>Nat</code>, but the point is <i>how</i> you prove it — from ownership, not from arithmetic.',

      setup: 'From M4 you have <code>two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) : (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)</code>. Recall <code>node p x next</code> is by definition <code>(p ↦ x) ∗ ((p + 1) ↦ next)</code>.',

      goal: 'theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1)',

      hints: [
        'You are asked to derive a <i>disequality between locations</i> from an <i>ownership assertion</i>. There is exactly one lemma in scope that does that, and you proved it in M4.',
        'Unfold <code>node p x next</code> in your head to <code>(p ↦ x) ∗ ((p + 1) ↦ next)</code> and line it up against <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂)</code>. Which four things does <code>two_cells_distinct</code> want, and in what order?',
        'Locations first, then values: <code>two_cells_distinct p (p + 1) x next</code>. No <code>by</code> block — it is a term. The definitional unfolding of <code>node</code> is what lets the types match.'
      ],

      sol: 'theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=\n  two_cells_distinct p (p + 1) x next',

      expl: 'One line, and it is worth noticing that the proof never mentions that <code>p ≠ p + 1</code> is a fact about numbers. The separating conjunction supplied it. In a model where locations are abstract, this would still work.',

      walk: [
        { tac: 'two_cells_distinct p (p + 1) x next',
          h: 'Instantiating <code>l₁ := p</code>, <code>l₂ := p + 1</code>, <code>v₁ := x</code>, <code>v₂ := next</code> gives a term of type <code>(p ↦ x) ∗ ((p + 1) ↦ next) ⊢ fact (fun _ => p ≠ p + 1)</code>. That is definitionally the stated type, because <code>node</code> is a <code>def</code> and unfolds. Lean checks it and is done — there is no tactic block at all.' }
      ],

      deep: [
        { t: 'p', h: 'For orientation, here is what the goal actually looks like if you do open a tactic block. The entailment is a <code>∀ σ h, …</code> in disguise, so <code>intro σ h hn</code> is what puts you in the model:' },
        { t: 'trace', title: 'The same statement, entered by hand',
          start: 'p : Loc\nx next : Nat\n⊢ node p x next ⊢ fact fun x => p ≠ p + 1',
          steps: [
            { tac: 'intro σ h hn',
              state: 'p : Loc\nx next : Nat\nσ : Store\nh : Heap\nhn : node p x next σ h\n⊢ fact (fun x => p ≠ p + 1) σ h',
              h: 'Note what Lean printed: the bound variable of the <code>fun _ =></code> got the display name <code>x</code>, colliding visually with the element <code>x : Nat</code>. They are different variables; the printer does not care. Also note <code>fact fun x => …</code> without parentheses in the first state and <code>fact (fun x => …) σ h</code> with them in the second — pure pretty-printing, same term.' },
            { tac: 'exact two_cells_distinct p (p + 1) x next σ h hn',
              h: 'Applying the same lemma, now fully applied to <code>σ</code>, <code>h</code> and the hypothesis. The one-line term proof in the solution is this with the three arguments left off.' }
          ],
          done: 'No goals.' },
        { t: 'p', h: 'Now the interesting comparison. There <i>is</i> an arithmetic proof, and it is worse for a reason that has nothing to do with elegance.' },
        { t: 'cmp',
          left:  { t: 'The arithmetic route',
                   h: 'Throw the ownership away and prove the numeric fact. It works, but it needs a <code>show</code> to strip the <code>fact</code> wrapper, and it only proves this statement in a model where locations are <code>Nat</code>.',
                   src: 'example (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) := by\n  intro σ h _\n  show p ≠ p + 1\n  simp',
                   tag: 'illustration' },
          right: { t: 'The ownership route', kind: 'good',
                   h: 'Never mentions numbers. What it uses is that a heap cannot be disjoint from itself at a location it defines — a fact about the resource monoid of M2, not about <code>Nat</code>. Swap <code>Loc</code> for an abstract type with a successor-like field offset and the proof still compiles.',
                   src: 'two_cells_distinct p (p + 1) x next',
                   tag: 'verified' } },
        { t: 'detail', title: 'A small Lean surprise: <code>omega</code> and <code>abbrev</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'You might expect <code>omega</code> to close <code>p ≠ p + 1</code> in one word. It does — but only if the variable’s declared type is literally <code>Nat</code>. In this development <code>Loc</code> is <code>abbrev Loc := Nat</code>, and with Lean 4.32.2 the following two behave differently:' },
            { t: 'code', tag: 'sketch',
              src: 'example (p : Nat) : p ≠ p + 1 := by omega   -- succeeds\nexample (p : Loc) : p ≠ p + 1 := by omega   -- fails' },
            { t: 'state',
              cap: 'Real error from the second line.',
              src: 'error: omega could not prove the goal:\nNo usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.' },
            { t: 'p', h: 'It is not about <code>≠</code>, and not about the <code>+</code>. <code>example (p : Loc) : p &lt; p + 1 := by omega</code> and <code>example (p q : Loc) (h : p = q) : q = p := by omega</code> both fail with the same message. <code>omega</code> decides linear arithmetic over <code>Nat</code> and <code>Int</code>, and it identifies which subterms are arithmetic by looking at the types <i>as they appear in the goal</i>. <code>Loc</code> is a different expression from <code>Nat</code>, even though the kernel will unfold one to the other on demand — so nothing in the goal is recognised, and there are genuinely no constraints to feed the procedure. Reproduce it outside the workbook with two lines: <code>abbrev L := Nat</code> and <code>example (p : L) : p ≠ p + 1 := by omega</code>.' },
            { t: 'p', h: '<code>simp</code> closes it without complaint. <code>decide</code> does not — but for an unrelated reason, and it fails on the <code>Nat</code> version too: <code>decide</code> needs a closed proposition, and <code>p ≠ p + 1</code> has a free variable in it (<i>Expected type must not contain free variables</i>). The general lesson is that reducibility is a property of the kernel, not a promise about tactics. A tactic that pattern-matches on types can be blind to a synonym the kernel considers transparent. When a decision procedure claims there is nothing to work with, suspect an abbreviation before you suspect the goal.' }
          ] }
      ],

      pitfall: 'Getting the argument order wrong. <code>two_cells_distinct</code> takes both locations before both values, so <code>two_cells_distinct p (p + 1) next x</code> type-checks as a term but has the wrong type, and Lean reports it as a mismatch on the whole statement rather than on one argument:<br><code>has type p ↦ next ∗ p + 1 ↦ x ⊢ fact fun x => p ≠ p + 1</code><br><code>but is expected to have type node p x next ⊢ fact fun x => p ≠ p + 1</code><br>Read the first line, not the second: it is telling you the values are swapped. Note also that the printer drops the parentheses around <code>p + 1 ↦ x</code> — <code>↦</code> binds tighter than <code>∗</code>, so that really is <code>(p + 1) ↦ x</code>.',

      variants: 'Instantiate <code>two_cells_distinct</code> at the <i>same</i> location twice and the conclusion becomes <code>p ≠ p</code>, which is false — so the premise must be unsatisfiable. That is exactly the <code>cell_not_duplicable</code> illustration above, and it is the whole reason linked structures built with <code>∗</code> are acyclic. Replace the <code>∗</code> in <code>node</code> by <code>aAnd</code> and the lemma becomes vacuous rather than false: <code>aAnd (p ↦ x) ((p + 1) ↦ n)</code> demands one heap be two different singletons, so it holds of nothing and entails everything. Vacuous truth is the characteristic failure mode of using <code>∧</code> where you meant <code>∗</code>; it is worse than falsehood because the proofs still go through.'
    },

    { t: 'h4', s: 'Building an assertion by hand' },

    { t: 'p',
      h: 'The next exercise is the only one in the chapter that works in the model rather than the algebra, and it exists so that you see what the algebra is saving you from. Before starting it, get the shape of an anonymous constructor straight, because you are about to write five of them.' },

    { t: 'steps', title: 'How ⟨…⟩ flattens, and how to count the slots',
      items: [
        { k: 'A star is a six-slot bracket',
          h: [
            { t: 'p', h: 'The definition is <code>def star (P Q : Assertion) : Assertion := fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>. Lean’s anonymous constructor flattens nested <code>∃</code> and <code>∧</code>, so one proof of it is written' },
            { t: 'txt', src: '⟨h₁, h₂, disjointness, heap equation, proof of P, proof of Q⟩' },
            { t: 'p', h: 'Six slots: two heaps and four proofs. The same bracket, used in <code>obtain</code>, takes it apart again.' }
          ] },
        { k: 'Nesting adds slots, it does not add brackets',
          h: 'If <code>Q</code> is itself a star, its proof is another six-slot bracket — but you may write it inline, so <code>P ∗ (Q ∗ R)</code> is a single bracket with 5 + 6 = 11 fields. That is exactly the <code>obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩</code> in the solution: five for the outer star up to and including the proof of <code>node p a q</code>, then six for the inner one.' },
        { k: 'A layer of listRep is seven',
          h: 'The cons clause is <code>aExists fun next => pure φ ∗ (node p x next ∗ listRep xs next)</code>. One slot for the witness <code>next</code>, then the six of the outer star: <code>⟨next, hLeft, hRight, disjoint, heap equation, proof of pure φ, proof of the rest⟩</code>. And the proof of <code>pure φ</code> is itself <code>⟨fact, emp⟩</code>, written <code>⟨hp, rfl⟩</code>.' },
        { k: 'Always cut the pure conjunct off with Heap.empty',
          h: 'Because <code>pure φ = aAnd (fact φ) emp</code>, the left half of that star must be the empty heap. So <code>hLeft := Heap.empty</code>, the disjointness is <code>disjoint_empty_left _</code>, and the heap equation is <code>(union_empty_left _).symm</code> — every single time. Recognising that trio on sight is most of the exercise.' },
        { k: 'refine, not exact',
          h: 'Write <code>refine ⟨…, ?_⟩</code> and leave the recursive tail as a hole. Lean then <i>tells you</i> what the next layer must prove, with the heap already computed. Trying to write the whole nested term as one <code>exact</code> is possible and is a bad idea: when it fails you get one error about a term thirty tokens long instead of one goal you can read.' }
      ] },

    {
      t: 'ex',
      id: 'm10-3',
      name: 'concrete three-node list',
      hard: true,

      why: 'Assemble a concrete structure from concrete points-to facts. Good for calibrating your intuition about what the existentials are doing. It is also the last time in this chapter you will touch a heap variable — everything after this is algebra, and the contrast is the point.',

      setup: 'The three hypotheses <code>hp</code>, <code>hq</code>, <code>hr</code> supply the non-null side conditions of the three cons layers. Nothing supplies non-nullity for the final <code>0</code>, and nothing needs to: the nil layer asks for <code>0 = 0</code>.',

      goal: 'theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p',

      hints: [
        'You cannot make progress with <code>refine</code> while the heap is an opaque variable, because every layer has to say what its half of the heap <i>is</i>. So start in the model: <code>intro σ h hstar</code>, then take <code>hstar</code> apart.',
        'Destructure with one bracket. <code>node p a q ∗ (node q b r ∗ node r c 0)</code> has 5 + 6 = 11 fields. Then <code>subst</code> both heap equations, so that <code>h</code> disappears and the goal’s heap is literally <code>h₁.union (h₃.union h₄)</code> — a term built out of unions, which is what makes the later equations <code>rfl</code>.',
        'Each <code>listRep</code> layer is seven slots: <code>⟨next, Heap.empty, «the rest of the heap», disjoint_empty_left _, (union_empty_left _).symm, ⟨hNonNull, rfl⟩, ?_⟩</code>. Alternate that with the six-slot star that hands the node its heap.',
        'The witnesses, in order, are the next pointers: <code>q</code>, then <code>r</code>, then <code>0</code>. The last line closes <code>listRep [] 0</code> with <code>⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩</code> — empty heap on the <i>right</i> this time, since the nil clause is the second conjunct.'
      ],

      sol: 'theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p := by\n  intro σ h hstar\n  obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩ := hstar\n  subst hu\'\n  subst hu\n  refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩\n  refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩\n  refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩\n  refine ⟨h₃, h₄, hd\', rfl, hn₂, ?_⟩\n  refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩\n  exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩',

      expl: 'The rhythm is: witness the existential, split off <code>Heap.empty</code> for the <code>pure</code>, hand the node its heap, recurse. The two <code>subst</code>s at the top are what make every subsequent heap equation <code>rfl</code> — always normalise the hypotheses before you start building the goal, or you will be fighting <code>union_assoc</code> at every step.',

      walk: [
        { tac: 'intro σ h hstar',
          h: '<code>P ⊢ Q</code> is <code>∀ σ h, P σ h → Q σ h</code>, so three <code>intro</code>s put you in the model with a store, a heap and the hypothesis. The goal becomes <code>listRep [a, b, c] p σ h</code>.' },
        { tac: 'obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩ := hstar',
          h: 'Eleven names for the nested star. <code>h₁</code> holds the first node, <code>h₂</code> the other two; <code>hu : h = h₁.union h₂</code>; then <code>h₂</code> splits again into <code>h₃</code> and <code>h₄</code>. After this, <code>hstar</code> is gone and you have four heaps and two equations.' },
        { tac: 'subst hu\'',
          h: '<code>hu\' : h₂ = h₃.union h₄</code>, so this erases <code>h₂</code> everywhere, rewriting <code>hu</code> into <code>h = h₁.union (h₃.union h₄)</code> and <code>hd</code> into <code>h₁.disjoint (h₃.union h₄)</code>.' },
        { tac: 'subst hu',
          h: 'Now erases <code>h</code> itself. The goal’s heap becomes the explicit union tree <code>h₁.union (h₃.union h₄)</code>. From here on, every heap you name in a bracket is a <i>subterm</i> of that tree, which is why the equations you owe will all be closed by <code>rfl</code>.' },
        { tac: 'refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _, (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩',
          h: 'The outermost <code>listRep</code> layer. <code>q</code> is the witness for <code>next</code>; the cut is <code>Heap.empty</code> against the whole remaining tree; <code>⟨hp, rfl⟩</code> proves <code>pure (fun _ => p ≠ 0)</code> — <code>hp</code> for the <code>fact</code>, <code>rfl</code> for the <code>emp</code>, since <code>emp σ Heap.empty</code> unfolds to <code>Heap.empty = Heap.empty</code>. The hole is the rest.' },
        { tac: 'refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩',
          h: 'Six slots: this is the star <code>node p a q ∗ listRep [b, c] q</code>. <code>h₁</code> is the node’s heap, <code>hd</code> is the disjointness you already have, and the heap equation is <code>rfl</code> precisely because of the two <code>subst</code>s. <code>hn₁</code> discharges the node.' },
        { tac: 'refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩',
          h: 'Second layer, identical rhythm, one heap smaller. Witness <code>r</code>, empty heap for the pure part, <code>hq</code> for <code>q ≠ 0</code>.' },
        { tac: 'refine ⟨h₃, h₄, hd\', rfl, hn₂, ?_⟩',
          h: 'Hand the second node its heap <code>h₃</code>, leaving <code>h₄</code> for the tail. Again <code>rfl</code>, again because the goal’s heap is literally <code>h₃.union h₄</code>.' },
        { tac: 'refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩',
          h: 'Third and last cons layer. The witness is <code>0</code>: this node’s next pointer is null, which is what makes the list terminate. <code>hr</code> discharges <code>r ≠ 0</code>.' },
        { tac: 'exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩',
          h: 'Seven slots for <code>node r c 0 ∗ listRep [] 0</code>. The empty heap is now on the <i>right</i>, so it is <code>disjoint_empty_right</code> and <code>union_empty_right</code>. The last two <code>rfl</code>s are the nil clause: <code>0 = 0</code> for the fact, <code>Heap.empty = Heap.empty</code> for the <code>emp</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'concrete_list, tactic by tactic (real Lean output)',
          start: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\n⊢ node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p',
          steps: [
            { tac: 'intro σ h hstar',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh : Heap\nhstar : (node p a q ∗ node q b r ∗ node r c 0) σ h\n⊢ listRep [a, b, c] p σ h',
              h: 'The two <code>⊢</code> in the starting goal have become one. The outer <code>⊢</code> was the <code>Entails</code> notation; introducing <code>σ</code>, <code>h</code> and the premise consumed it.' },
            { tac: 'obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd\', hu\', hn₂, hn₃⟩ := hstar',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhu\' : h₂ = h₃.union h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\n⊢ listRep [a, b, c] p σ h',
              h: 'Read the printed types carefully: Lean writes <code>h₁.disjoint h₂</code> and <code>h₁.union h₂</code>, not <code>Heap.disjoint h₁ h₂</code> and <code>Heap.union h₁ h₂</code>. Dot notation is the printer’s choice, not something in the source. When you type the terms back you may write either form.' },
            { tac: 'subst hu\'  ·  subst hu',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [a, b, c] p σ (h₁.union (h₃.union h₄))',
              h: 'This is the state the whole proof depends on. <code>h</code> and <code>h₂</code> are gone; the goal names an explicit union tree; <code>hd</code> has been rewritten into exactly the disjointness the first star will ask for. Note that <code>hd</code> has moved to the bottom of the context — <code>subst</code> reinserts a rewritten hypothesis at the end.' },
            { tac: 'refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _, (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ (node p a q ∗ listRep [b, c] q) σ (h₁.union (h₃.union h₄))',
              h: 'The existential and the pure conjunct are both discharged, and the remaining goal has <i>already unfolded one layer of the list</i>: <code>listRep [a, b, c] p</code> became <code>node p a q ∗ listRep [b, c] q</code>, with <code>q</code> substituted for the witness. This is the moment the recursion becomes visible.' },
            { tac: 'refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [b, c] q σ (h₃.union h₄)',
              h: 'One node paid for, and the goal is the original statement with the first element removed and the heap shrunk by one subtree. Compare it with the state three steps ago: same shape, smaller data. That similarity is what the induction in the next exercises exploits.' },
            { tac: 'refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ (node q b r ∗ listRep [c] r) σ (h₃.union h₄)',
              h: 'Second layer opened, witness <code>r</code>.' },
            { tac: 'refine ⟨h₃, h₄, hd\', rfl, hn₂, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [c] r σ h₄',
              h: 'Down to a one-element list on a single heap. <code>h₁</code> and <code>h₃</code> are spent — they are still in the context, but nothing left in the goal mentions them.' },
            { tac: 'refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩',
              state: 'p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd\' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ (node r c 0 ∗ listRep [] 0) σ h₄',
              h: 'The witness <code>0</code> propagated into the tail, so the remaining obligation is <code>listRep [] 0</code> — which is where the recursion stops. The final <code>exact</code> gives <code>h₄</code> to the node and <code>Heap.empty</code> to the nil clause.' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'Does the order of the two <code>subst</code>s matter?', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'No. Doing <code>subst hu</code> first erases <code>h</code>, leaving <code>h₁.union h₂</code> in the goal; <code>subst hu\'</code> then erases <code>h₂</code> inside it. The resulting state is identical to the one shown above, down to the order of the context. Try it — it is a cheap way to convince yourself that <code>subst</code> is just substitution and has no hidden orientation cleverness.' },
            { t: 'p', h: 'What <i>does</i> matter is doing them at all, and doing them before the first <code>refine</code>. That is the subject of the pitfall below.' }
          ] },
        { t: 'p', h: 'Finally, look at what this proof costs and what the algebra costs. Twelve lines here for a list of length three; the next exercise proves a statement about lists of <i>every</i> length in six.' }
      ],

      pitfall: 'Skipping the <code>subst</code>s and going straight to <code>refine</code>. The heap equation slot then has to prove <code>h = Heap.union Heap.empty (…)</code> where <code>h</code> is still an opaque variable, and <code>(union_empty_left _).symm</code> cannot possibly have that type. Lean says so, but it says it about the <i>bracket</i>, which is confusing the first time:<br><code>Application type mismatch: The argument Eq.symm (union_empty_left ?m.108) has type ?m.108 = Heap.empty.union ?m.108 but is expected to have type h = Heap.empty.union (h₁.union (h₃.union h₄))</code><br>The tell is the metavariable <code>?m.108</code> appearing on both sides of the “has type” line: Lean is saying <i>this lemma can only prove an equation whose left side is the same as its right operand</i>, and yours is not, because you never told it what <code>h</code> is.',

      variants: 'Drop <code>hp : p ≠ 0</code> and the first <code>⟨hp, rfl⟩</code> has nothing to put in the <code>fact</code> slot — and rightly so, because the theorem becomes false: take <code>p = 0</code> and a heap containing cells <code>0</code> and <code>1</code>, and the left-hand side holds while <code>listRep [a, b, c] 0</code> does not. Drop <code>hr : r ≠ 0</code> and it fails at the third layer, not the first. There is no hypothesis about the terminal <code>0</code> because the nil clause asks for <code>0 = 0</code>. Reverse the entailment — <code>listRep [a, b, c] p ⊢ node p a q ∗ node q b r ∗ node r c 0</code> — and it is false for a different reason: the list existentially quantifies its next pointers, so it cannot know they are the particular <code>q</code> and <code>r</code> you named.'
    },

    { t: 'sec', s: 'Exercises · the append theorems' },

    { t: 'p',
      h: 'The remaining two theorems are proved by induction on the first list, and how you <i>state</i> them decides whether the induction works. This is the single most important Lean move in the chapter, so it is worth being explicit about.' },

    { t: 'cmp',
      left: { t: 'The statement a mathematician writes',
              h: 'Put the variables in the binder list, where they belong:<br><code>theorem lseg_append (xs ys : List Nat) (p q r : Loc) : lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r</code><br>Then <code>induction xs</code> and you are handed this induction hypothesis:',
              src: 'ih : lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',
              tag: 'sketch',
              kind: 'bad' },
      right: { t: 'The statement Lean needs',
               h: 'Quantify everything except the induction variable <i>inside</i> the statement, and <code>intro xs</code> alone:<br><code>theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc), …</code><br>Now the induction hypothesis quantifies over its own start pointer:',
               src: 'ih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',
               tag: 'sketch',
               kind: 'good' } },

    { t: 'p',
      h: 'Why it matters: in the cons case the tail segment starts at the <i>next pointer</i> <code>n</code>, not at <code>p</code>. The proof ends with <code>ih ys n q r</code> — the induction hypothesis applied at <code>n</code>. The left-hand version cannot supply that, because its <code>p</code> is fixed by the enclosing theorem. You would get a type mismatch on the very last line and no way to repair it. (Lean has a <code>generalizing</code> clause on <code>induction</code> that achieves the same thing; putting the <code>∀</code> in the statement is the version that also makes the lemma more useful to callers, since they can instantiate it however they like.)' },

    { t: 'dl', items: [
      { k: 'entails_trans', h: '<code>(P ⊢ Q) → (Q ⊢ R) → (P ⊢ R)</code>. Used as <code>refine entails_trans lemma ?_</code>: you name the first step and leave the rest of the road as a hole. A chain of these is how you compose an entailment left to right.' },
      { k: 'star_exists_left', h: '<code>aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q)</code>. Pulls an existential out from under a star. This is what turns “a segment (which begins with ∃) starred with something” into “∃ n, (that segment’s body starred with something)”.' },
      { k: 'aExists_mono', h: '<code>(∀ x, P x ⊢ Q x) → aExists P ⊢ aExists Q</code>. Lets you drop under the binder and work pointwise. It is not in M4 — you prove it as part of exercise 4, because this is the first chapter that needs it.' },
      { k: 'star_assoc_left', h: '<code>(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)</code>. Re-brackets to the right. You need it twice per step: once to get the <code>pure</code> conjunct out of the way, once to make the two segments adjacent.' },
      { k: 'star_mono_right', h: '<code>(Q ⊢ Q\') → P ∗ Q ⊢ P ∗ Q\'</code>. Leaves the left factor alone and works on the right. Each use peels one conjunct off the front of both sides of the goal.' }
    ] },

    {
      t: 'ex',
      id: 'm10-4',
      name: 'lseg_append',
      hard: true,

      why: '<b>The classical theorem of the subject.</b> Two adjacent segments make one segment. Every list-traversal loop invariant is maintained by an application of this. In M13 it is the lemma that moves one node from “still to visit” to “already visited”.',

      setup: 'You need one lemma that is not in M4: <code>aExists_mono</code>, stated and proved as part of the solution below. Everything else — <code>entails_trans</code>, <code>star_exists_left</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>, <code>union_empty_left</code> — you already have.',

      goal: 'theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',

      hints: [
        'Two theorems, in this order. Prove <code>aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) : aExists P ⊢ aExists Q</code> first — it is two tactics, and without it you cannot get under the existential that <code>lseg</code>’s cons clause opens with.',
        'State the theorem with <code>∀ (xs ys : List Nat) (p q r : Loc),</code> <i>inside</i> it and then <code>intro xs</code> only. If <code>p q r</code> are theorem parameters, the induction hypothesis is nailed to <code>p</code>, and the cons case needs it at the next pointer.',
        'The nil case is <code>pure (fun _ => p = q) ∗ lseg ys q r ⊢ lseg ys p r</code>. That one you do in the model: <code>intro</code> down to the heap, <code>obtain</code> the six fields, then substitute <code>p = q</code> and substitute the empty heap, and <code>rw [hu, union_empty_left]</code>. Careful: the equation arrives with type <code>fact (fun x => p = q) σ h₁</code>, which does not <i>look</i> like an equation.',
        'The cons case has no heaps at all. Five moves, in order: pull the existential out (<code>star_exists_left</code>), go under the binder (<code>aExists_mono</code>), re-bracket so the <code>pure</code> is the outer left factor (<code>star_assoc_left</code>), discard it (<code>star_mono_right</code>), re-bracket again so the two segments sit together (<code>star_assoc_left</code>), and finish with <code>star_mono_right _ (ih ys n q r)</code>.'
      ],

      sol: 'theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :\n    aExists P ⊢ aExists Q := by\n  intro σ hh ⟨x, hp⟩\n  exact ⟨x, h x σ hh hp⟩\n\ntheorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq\' : p = q := hpq\n      subst hpq\'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)',

      expl: 'Look at the cons case: eight lines, no heap variables, no unions. That is the difference between grinding semantics and using the logic. Reading it as a chain: pull the existential out of the star (<code>star_exists_left</code>); work under the binder (<code>aExists_mono</code>); reassociate so the pure fact is on the outside (<code>star_assoc_left</code>); cancel it against the identical factor on the right (<code>star_mono_right</code>); reassociate again so the two segments are adjacent; apply the induction hypothesis to them under the node (<code>star_mono_right</code> again). Every step is one of the M4 lemmas. If you built the normalisation library then, you are collecting the dividend now.',

      walk: [
        { tac: 'intro σ hh ⟨x, hp⟩',
          h: 'In <code>aExists_mono</code>. Three introductions, and the third is a <i>pattern</i>: instead of naming the hypothesis and destructing it afterwards, you write the anonymous constructor directly in <code>intro</code>. Since <code>aExists P σ hh</code> is <code>∃ x, P x σ hh</code>, this hands you the witness <code>x</code> and the body <code>hp</code> in one move.' },
        { tac: 'exact ⟨x, h x σ hh hp⟩',
          h: 'Rebuild the existential with the <i>same</i> witness — that is the whole content of the lemma: monotonicity under <code>∃</code> does not change which element you are talking about. <code>h x</code> is the pointwise entailment, applied to <code>σ</code>, <code>hh</code> and the proof.' },
        { tac: 'theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc), …',
          h: 'All five variables under a <code>∀</code> in the statement. This is not decoration; see the comparison above.' },
        { tac: 'intro xs',
          h: 'Introduce only the variable you are going to recurse on. <code>ys</code>, <code>p</code>, <code>q</code>, <code>r</code> stay in the goal, which is exactly what makes the induction hypothesis general.' },
        { tac: 'induction xs with',
          h: 'Structured induction: the two branches are named after <code>List</code>’s constructors, and each supplies its own binders. The alternative, plain <code>induction xs</code> followed by <code>·</code> bullets, works but leaves the case names implicit; the <code>with</code> form documents itself and fails loudly if you misname a case.' },
        { tac: '| nil =>',
          h: 'Goal: <code>∀ ys p q r, lseg [] p q ∗ lseg ys q r ⊢ lseg ([] ++ ys) p r</code>. Since <code>lseg [] p q</code> is <code>pure (fun _ => p = q)</code>, this says “an empty segment on the left is the identity”.' },
        { tac: 'intro ys p q r σ h hstar',
          h: 'Seven introductions in one: four from the <code>∀</code>, then the store, heap and premise from unfolding <code>⊢</code>. This branch is done in the model because the empty-heap bookkeeping is easier there than through <code>star_pure_left</code>.' },
        { tac: 'obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
          h: 'Six slots for the star, with the disjointness thrown away as <code>_</code> — it is genuinely not needed, since one side is empty. The nested <code>⟨hpq, he⟩</code> splits <code>pure φ = aAnd (fact φ) emp</code> into its two conjuncts. Lean names the discarded field <code>left✝</code> and marks it inaccessible; you cannot refer to it, which is the point.' },
        { tac: 'have hpq\' : p = q := hpq',
          h: 'Type ascription, and nothing more. <code>fact φ</code> is <code>fun σ _ => φ σ</code>, so <code>fact (fun x => p = q) σ h₁</code> unfolds to <code>p = q</code>: <code>hpq</code> already <i>is</i> a proof of the equation, and the <code>have</code> only gives it a name at its visible type. Under 4.32.2 the line is not needed — <code>subst hpq</code> on its own works, because <code>subst</code> unfolds far enough to find the equation. Keep it anyway for the reader: a hypothesis displayed as <code>fact (fun x => p = q) σ h₁</code> does not look like something you can substitute with, and the <code>have</code> is where you record that it is.' },
        { tac: 'subst hpq\'',
          h: 'Replaces <code>q</code> by <code>p</code> throughout. Note the direction: <code>subst</code> eliminates the variable, and here it chose to eliminate <code>q</code>, so <code>hys</code> becomes <code>lseg ys p r σ h₂</code> — which is what the goal wants.' },
        { tac: 'subst he',
          h: '<code>he : emp σ h₁</code> is definitionally <code>h₁ = Heap.empty</code>, so this erases <code>h₁</code> and turns <code>hu</code> into <code>h = Heap.empty.union h₂</code>. Same trick as the previous line, without needing the <code>have</code>, because <code>emp</code> unfolds directly to an equation between heaps.' },
        { tac: 'rw [hu, union_empty_left]',
          h: 'Rewrite the goal’s heap with <code>hu</code>, then collapse <code>Heap.empty.union h₂</code> to <code>h₂</code>. Now the goal is <code>lseg ([] ++ ys) p r σ h₂</code>.' },
        { tac: 'exact hys',
          h: 'And <code>hys : lseg ys p r σ h₂</code>. These are not syntactically equal — the goal says <code>[] ++ ys</code> — but <code>List.append</code> reduces on its first argument, so they are definitionally equal, and <code>exact</code> checks up to definitional equality. This is the payoff of the <code>rfl</code>-versus-<code>rw</code> distinction from exercise 1: <code>rw [List.nil_append]</code> would also work, and is unnecessary.' },
        { tac: '| cons x xs ih =>',
          h: 'Three binders: the head <code>x</code>, the tail <code>xs</code>, and the induction hypothesis <code>ih</code>, which is itself a <code>∀</code> over four variables.' },
        { tac: 'intro ys p q r',
          h: 'Introduce the four quantified variables — and <i>stop</i>. No <code>σ</code>, no <code>h</code>. Everything from here is a manipulation of entailments as objects.' },
        { tac: 'refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_',
          h: 'Composing with the identity on the left factor. It changes nothing — the printed goal before and after is character-for-character the same. It is there as documentation of what is about to be rewritten; see the aside below, where the line is deleted and the proof still compiles.' },
        { tac: 'refine entails_trans (star_exists_left _ _) ?_',
          h: 'The first real step. <code>lseg (x :: xs) p q</code> unfolds to an <code>aExists</code>, so the left side is <code>aExists (…) ∗ lseg ys q r</code>, and this lemma pushes the star inside: <code>aExists (fun n => (…) ∗ lseg ys q r)</code>. The remaining goal is an entailment out of that.' },
        { tac: 'refine aExists_mono (fun n => ?_)',
          h: 'Now both sides are existentials — the right one because <code>lseg (x :: xs ++ ys) p r</code> also unfolds to an <code>aExists</code> — so you can go under the binder. <code>n</code> enters the context as the shared next pointer, and the goal loses both <code>aExists</code>. This is where the proof stops being about lists and becomes about one node plus a smaller problem.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'The left side is <code>(pure φ ∗ (node ∗ lseg xs n q)) ∗ lseg ys q r</code> — the star introduced by <code>star_exists_left</code> is on the outside. Re-bracketing to the right makes <code>pure φ</code> the outermost left factor, matching the right-hand side.' },
        { tac: 'refine star_mono_right _ ?_',
          h: 'Both sides now start with the same <code>pure φ</code>, so peel it off. The <code>_</code> is that common factor; the hole is the entailment between what remains.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'Same move one level down: <code>(node ∗ lseg xs n q) ∗ lseg ys q r</code> becomes <code>node ∗ (lseg xs n q ∗ lseg ys q r)</code>, which finally places the two segments next to each other.' },
        { tac: 'exact star_mono_right _ (ih ys n q r)',
          h: 'Peel off the node and apply the induction hypothesis to the adjacent pair — <i>at the next pointer</i> <code>n</code>, which is why the statement had to quantify over the start location. <code>ih ys n q r : lseg xs n q ∗ lseg ys q r ⊢ lseg (xs ++ ys) n r</code>, and that is precisely the remaining goal.' }
      ],

      deep: [
        { t: 'trace', title: 'aExists_mono',
          start: 'α : Sort u\nP Q : α → Assertion\nh : ∀ (x : α), P x ⊢ Q x\n⊢ aExists P ⊢ aExists Q',
          steps: [
            { tac: 'intro σ hh ⟨x, hp⟩',
              state: 'α : Sort u\nP Q : α → Assertion\nh : ∀ (x : α), P x ⊢ Q x\nσ : Store\nhh : Heap\nx : α\nhp : P x σ hh\n⊢ aExists Q σ hh',
              h: 'The pattern in <code>intro</code> did two jobs at once: it introduced the premise and destructed it. Compare with <code>intro σ hh hex</code> followed by <code>obtain ⟨x, hp⟩ := hex</code>, which produces the same state in two lines.' },
            { tac: 'exact ⟨x, h x σ hh hp⟩',
              h: 'The goal <code>aExists Q σ hh</code> is <code>∃ y, Q y σ hh</code>; supply <code>x</code> and push <code>hp</code> along the pointwise entailment.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'lseg_append, the nil case (real Lean output)',
          start: '⊢ ∀ (xs ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r',
          steps: [
            { tac: 'intro xs  ·  induction xs with  ·  | nil =>',
              state: 'case nil\n⊢ ∀ (ys : List Nat) (p q r : Loc), lseg [] p q ∗ lseg ys q r ⊢ lseg ([] ++ ys) p r',
              h: 'The four remaining variables are still under the <code>∀</code>. Lean labels the branch <code>case nil</code>; that label is what the <code>| nil =></code> syntax matches on.' },
            { tac: 'intro ys p q r σ h hstar',
              state: 'case nil\nys : List Nat\np q r : Loc\nσ : Store\nh : Heap\nhstar : (lseg [] p q ∗ lseg ys q r) σ h\n⊢ lseg ([] ++ ys) p r σ h',
              h: 'Note that the goal keeps <code>[] ++ ys</code> unevaluated. Lean does not normalise goals for display; it will reduce when it needs to, at the very end.' },
            { tac: 'obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
              state: 'case nil\nys : List Nat\np q r : Loc\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhys : lseg ys q r σ h₂\nhpq : fact (fun x => p = q) σ h₁\nhe : emp σ h₁\n⊢ lseg ([] ++ ys) p r σ h',
              h: 'Two things to read here. <code>left✝</code> is the field you discarded with <code>_</code>; the dagger marks it inaccessible, so you cannot use it even by typing that name. And <code>hpq : fact (fun x => p = q) σ h₁</code> is the equation you need, wearing a costume — this is what the next line is for.' },
            { tac: 'have hpq\' : p = q := hpq  ·  subst hpq\'',
              state: 'case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhys : lseg ys p r σ h₂\nhpq : fact (fun x => p = p) σ h₁\n⊢ lseg ([] ++ ys) p r σ h',
              h: '<code>q</code> is gone from the context and every occurrence has become <code>p</code>. In particular <code>hys</code> now reads <code>lseg ys p r σ h₂</code>, which is the shape of the goal. Notice that <code>hpq</code> survives as the now-trivial <code>fact (fun x => p = p)</code>, because it was <code>hpq\'</code>, not <code>hpq</code>, that <code>subst</code> consumed.' },
            { tac: 'subst he',
              state: 'case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₂ : Heap\nhys : lseg ys p r σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhpq : fact (fun x => p = p) σ Heap.empty\n⊢ lseg ([] ++ ys) p r σ h',
              h: '<code>h₁</code> has been replaced by <code>Heap.empty</code> everywhere. <code>subst</code> accepted <code>he : emp σ h₁</code> directly, without a <code>have</code>, because <code>emp</code> unfolds to a bare equation between heaps rather than to an application of <code>fact</code>.' },
            { tac: 'rw [hu, union_empty_left]',
              state: 'case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₂ : Heap\nhys : lseg ys p r σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhpq : fact (fun x => p = p) σ Heap.empty\n⊢ lseg ([] ++ ys) p r σ h₂',
              h: 'Only the goal changed, and only its heap argument: <code>h</code> → <code>Heap.empty.union h₂</code> → <code>h₂</code>. The goal still says <code>[] ++ ys</code>, and <code>exact hys</code> closes it anyway.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'lseg_append, the cons case — step by step, no heaps (real Lean output)',
          start: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\n⊢ ∀ (ys : List Nat) (p q r : Loc), lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r',
          steps: [
            { tac: 'intro ys p q r',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\n⊢ lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r',
              h: 'The goal is an entailment, not a proposition about a heap. Everything below manipulates it as a term. Read <code>x :: xs ++ ys</code> as <code>x :: (xs ++ ys)</code> — <code>::</code> binds looser than <code>++</code>.' },
            { tac: 'refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\n⊢ lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r',
              h: 'Identical to the previous state. Composing with the identity entailment is a no-op, as it must be. Keep reading — the next line is the one that moves.' },
            { tac: 'refine entails_trans (star_exists_left _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\n⊢ (aExists fun x_1 => ((_root_.pure fun x => p ≠ 0) ∗ node p x x_1 ∗ lseg xs x_1 q) ∗ lseg ys q r) ⊢\n    lseg (x :: xs ++ ys) p r',
              h: 'Three printer quirks in one line, all harmless. <code>x_1</code> is the bound next pointer, renamed because <code>x</code> is taken. <code>_root_.pure</code> is our <code>pure</code>, qualified because Lean’s <code>Pure.pure</code> is also in scope. And the whole entailment is line-wrapped with the right-hand side indented — the <code>⊢</code> at the end of the first line is the <code>Entails</code> arrow, not a second goal.' },
            { tac: 'refine aExists_mono (fun n => ?_)',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ ((_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg (xs.append ys) n r',
              h: 'Both existentials are gone and <code>n : Nat</code> is in the context. The right-hand side has unfolded one layer too, so you can now see what has to match what. Note it prints <code>xs.append ys</code> on the right while the induction hypothesis says <code>xs ++ ys</code>: same term, two notations, and no tactic is needed to reconcile them.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ (_root_.pure fun x => p ≠ 0) ∗ (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg (xs.append ys) n r',
              h: 'The outermost bracket has moved. Both sides now begin with the same <code>pure</code> factor, which is the precondition for the next step.' },
            { tac: 'refine star_mono_right _ ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r',
              h: 'The <code>pure</code> is gone from both sides. This is where the non-null side condition is discharged: it is carried across unchanged, which is only possible because it is the <i>same</i> condition on both sides — <code>p ≠ 0</code>, not <code>p ≠ q</code> versus <code>p ≠ r</code>.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nn : Nat\n⊢ node p x n ∗ lseg xs n q ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r',
              h: 'The two segments are now adjacent on the left, under a common <code>node p x n</code>. Compare this goal with <code>ih</code>: strip the leading <code>node p x n ∗</code> from both sides and you have <code>ih ys n q r</code> exactly.' }
          ],
          done: 'No goals — the final <code>exact star_mono_right _ (ih ys n q r)</code> closes it.' },
        { t: 'detail', title: 'The first <code>refine</code> is a no-op, and you can delete it', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The trace above shows the goal unchanged across <code>refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_</code>. That is not a display artefact: the line composes the proof with an identity, and the proof compiles without it.' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — the corpus keeps the extra line. This version compiles against the M10 prelude and produces the same theorem.',
              src: 'theorem lseg_append\' : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq\' : p = q := hpq\n      subst hpq\'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)' },
            { t: 'p', h: 'Why is it in the corpus, then? Because it names the thing that is about to happen. <code>star_exists_left</code> only applies once you accept that <code>lseg (x :: xs) p q</code> <i>is</i> an <code>aExists</code>, and the explicit <code>entails_refl (lseg (x :: xs) p q)</code> is a place to write that down. Whether that is worth a line is a matter of taste; knowing that it is optional is not.' },
            { t: 'p', h: 'This is a good habit in general: when a tactic leaves the goal untouched, find out whether it did anything at all. Lines that do nothing accumulate in proofs, and each one is a small lie about what the argument needs.' }
          ] },
        { t: 'detail', title: 'Reading Lean’s output: <code>_root_.pure</code>, <code>xs.append ys</code>, <code>x_1</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'dl', items: [
              { k: '_root_.pure', h: 'The workbook defines <code>pure</code> at the top level, and Lean’s own <code>Pure.pure</code> is always in scope. When the printer must disambiguate it writes the fully qualified name. You never have to type it; <code>pure</code> resolves to the workbook’s definition in this file.' },
              { k: 'xs.append ys', h: 'The same term as <code>xs ++ ys</code>. <code>++</code> is notation for <code>HAppend.hAppend</code>, which for lists reduces to <code>List.append</code>; whether you see the notation or the projection depends on how the term was built. They are interchangeable and no lemma is needed to convert.' },
              { k: 'x_1', h: 'Lean renames a bound variable when its preferred name is taken. The cons clause of <code>lseg</code> binds <code>next</code>, but here the pretty-printer had already used <code>x</code> for the list head, so the binder came out as <code>x_1</code>. Nothing about the term changed.' },
              { k: 'left✝', h: 'An inaccessible name, produced when you write <code>_</code> in a destructuring pattern. The dagger means you cannot refer to it. If you find you need it after all, go back and give it a name.' }
            ] }
          ] }
      ],

      pitfall: 'Reaching for the induction hypothesis one <code>star_assoc_left</code> too early. After <code>refine star_mono_right _ ?_</code> the goal is still left-bracketed, <code>(node p x n ∗ lseg xs n q) ∗ lseg ys q r</code>, and <code>exact star_mono_right _ (ih ys n q r)</code> fails with a message that shows you the problem if you read both halves:<br><code>has type ?m.52 ∗ lseg xs n q ∗ lseg ys q r ⊢ ?m.52 ∗ lseg (xs ++ ys) n r</code><br><code>but is expected to have type (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r</code><br>The types are identical except for the brackets on the left of the second one. One more <code>entails_trans (star_assoc_left _ _ _)</code> fixes it. Whenever a <code>star_mono</code> lemma refuses an argument, check the association before you check anything else.',

      variants: 'Change the cons side condition to <code>start ≠ finish</code> — the version in the original syllabus — and the chain gets three steps further and then stops. <code>aExists_mono</code> and the first <code>star_assoc_left</code> both succeed; the tactic that cannot be taken is <code>refine star_mono_right _ ?_</code>, because the two sides no longer begin with the same factor: <code>pure (p ≠ q)</code> on the left, <code>pure (p ≠ r)</code> on the right. The detail block earlier in the chapter shows the goal state one step before that, which is where you can read the problem off. Drop the side condition altogether and <code>lseg_append</code> becomes <i>easier</i>, which is the trap: the append theorem is not what forces you to keep it. What forces you is agreement with <code>listRep</code> — see the counterexample in the next exercise. Finally, reverse the entailment: <code>lseg (xs ++ ys) p r ⊢ lseg xs p q ∗ lseg ys q r</code> is false for any fixed <code>q</code>, because appending forgets where the join was and no assertion about the combined segment can recover it.'
    },

    {
      t: 'ex',
      id: 'm10-5',
      name: 'lseg_listRep',
      hard: false,

      why: 'A segment followed by a complete list is a complete list. This is the lemma that closes a traversal: at the end, the visited prefix and the remaining suffix reassemble into the original list.',

      setup: 'Same toolkit as the previous exercise, and <code>aExists_mono</code> is now available as a lemma. The only difference in the statement is that the second conjunct is a <code>listRep</code>, so there is one fewer location variable.',

      goal: 'theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),\n    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p',

      hints: [
        'Same induction, same five-step chain. Set it up exactly as before: <code>∀</code> inside the statement, <code>intro xs</code>, <code>induction xs with</code>.',
        'The nil case is word-for-word the nil case of <code>lseg_append</code> — the only thing that changed is the name of the predicate on the right of the star, and the proof never mentions it. Copy it.',
        'The cons case is the previous cons case with one argument fewer at the end: <code>ih ys n q</code>, not <code>ih ys n q r</code>. And you will not need the opening <code>star_mono_left</code> line.'
      ],

      sol: 'theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),\n    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq\' : p = q := hpq\n      subst hpq\'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q)',

      expl: 'Structurally identical to <code>lseg_append</code>, which is the sign that the definitions are aligned. If you had kept <code>start ≠ finish</code> in <code>lseg</code>, this is the proof that would have failed first — the segment’s side condition would be about <code>q</code> while the list’s is about <code>0</code>.',

      walk: [
        { tac: 'intro xs',
          h: 'Only the induction variable. Same reason as before: <code>ys</code>, <code>p</code>, <code>q</code> must stay quantified so that the induction hypothesis can be used at a different start pointer.' },
        { tac: 'induction xs with',
          h: 'Two branches, <code>nil</code> and <code>cons</code>.' },
        { tac: '| nil =>',
          h: 'Goal: <code>∀ ys p q, lseg [] p q ∗ listRep ys q ⊢ listRep ([] ++ ys) p</code>. Unfolded, “<code>p = q</code> on the empty heap, starred with a list at <code>q</code>, gives a list at <code>p</code>”.' },
        { tac: 'intro ys p q σ h hstar',
          h: 'Six introductions — one fewer than <code>lseg_append</code>, since there is no <code>r</code>.' },
        { tac: 'obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
          h: 'Six fields, disjointness discarded, the <code>pure</code> split into <code>fact</code> and <code>emp</code>. Identical to the previous exercise; the second conjunct just happens to be a <code>listRep</code> now, and <code>hys</code> records it.' },
        { tac: 'have hpq\' : p = q := hpq',
          h: 'Ascribe the <code>fact</code> to its underlying equational type. As in the previous exercise, <code>subst hpq</code> would do without it under 4.32.2; the line is there so the equation is visible on the page.' },
        { tac: 'subst hpq\'',
          h: 'Eliminates <code>q</code>. Now <code>hys : listRep ys p σ h₂</code>.' },
        { tac: 'subst he',
          h: 'Eliminates <code>h₁</code> in favour of <code>Heap.empty</code>, since <code>emp σ h₁</code> is that equation.' },
        { tac: 'rw [hu, union_empty_left]',
          h: 'The goal’s heap becomes <code>h₂</code>.' },
        { tac: 'exact hys',
          h: 'Closes up to definitional equality: the goal says <code>listRep ([] ++ ys) p</code>, the hypothesis says <code>listRep ys p</code>, and <code>[] ++ ys</code> reduces.' },
        { tac: '| cons x xs ih =>',
          h: 'Head, tail, and an induction hypothesis quantified over <code>ys</code>, <code>p</code>, <code>q</code>.' },
        { tac: 'intro ys p q',
          h: 'Three introductions, and no descent into the model. Everything below is entailment algebra.' },
        { tac: 'refine entails_trans (star_exists_left _ _) ?_',
          h: 'Pull the existential of <code>lseg (x :: xs) p q</code> out from under the star.' },
        { tac: 'refine aExists_mono (fun n => ?_)',
          h: 'Go under the binder. Both sides are existentials — the right one because <code>listRep (x :: xs ++ ys) p</code> also opens with <code>aExists</code>, which is precisely the alignment the two definitions were designed to have.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'Re-bracket so the <code>pure (fun _ => p ≠ 0)</code> is the outer left factor on both sides.' },
        { tac: 'refine star_mono_right _ ?_',
          h: 'Cancel it. This is the step that would be impossible if <code>lseg</code>’s side condition were <code>p ≠ q</code> and <code>listRep</code>’s were <code>p ≠ 0</code>.' },
        { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
          h: 'Re-bracket again to make <code>lseg xs n q</code> and <code>listRep ys q</code> adjacent.' },
        { tac: 'exact star_mono_right _ (ih ys n q)',
          h: 'Peel off <code>node p x n</code> and apply the induction hypothesis at the next pointer. Three arguments, not four.' }
      ],

      deep: [
        { t: 'p', h: 'The nil case is character-for-character the nil case of <code>lseg_append</code> minus the unused <code>r</code>, so its trace is the one in the previous exercise. Here is the cons case, which is where the alignment of the two definitions actually shows.' },
        { t: 'trace', title: 'lseg_listRep, the cons case (real Lean output)',
          start: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\n⊢ ∀ (ys : List Nat) (p q : Loc), lseg (x :: xs) p q ∗ listRep ys q ⊢ listRep (x :: xs ++ ys) p',
          steps: [
            { tac: 'intro ys p q',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\n⊢ lseg (x :: xs) p q ∗ listRep ys q ⊢ listRep (x :: xs ++ ys) p',
              h: 'Two different predicates in one entailment. Nothing in the proof will ever need to know that they are different, which is the whole point.' },
            { tac: 'refine entails_trans (star_exists_left _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\n⊢ (aExists fun x_1 => ((_root_.pure fun x => p ≠ 0) ∗ node p x x_1 ∗ lseg xs x_1 q) ∗ listRep ys q) ⊢\n    listRep (x :: xs ++ ys) p',
              h: 'The left side has unfolded and the existential is now outermost. The right side has not been touched yet — <code>aExists_mono</code> will unfold it by unifying against the goal.' },
            { tac: 'refine aExists_mono (fun n => ?_)',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ ((_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ listRep (xs.append ys) n',
              h: 'Look at the two <code>_root_.pure fun x => p ≠ 0</code>, one on each side. They are the <i>same assertion</i>, because <code>lseg</code> and <code>listRep</code> use the same non-null condition. This one line is the entire content of the warning note earlier in the chapter.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ (_root_.pure fun x => p ≠ 0) ∗ (node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ listRep (xs.append ys) n',
              h: 'Both sides now begin with the identical factor.' },
            { tac: 'refine star_mono_right _ ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ (node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢ node p x n ∗ listRep (xs.append ys) n',
              h: 'Cancelled. What is left is the node plus a strictly smaller instance of the theorem.' },
            { tac: 'refine entails_trans (star_assoc_left _ _ _) ?_',
              state: 'case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q : Loc), lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p\nys : List Nat\np q : Loc\nn : Nat\n⊢ node p x n ∗ lseg xs n q ∗ listRep ys q ⊢ node p x n ∗ listRep (xs.append ys) n',
              h: 'Strip <code>node p x n ∗</code> from both sides and compare with <code>ih</code>: identical after instantiating <code>ys := ys</code>, <code>p := n</code>, <code>q := q</code>.' }
          ],
          done: 'No goals — the final <code>exact star_mono_right _ (ih ys n q)</code> closes it.' },
        { t: 'p', h: 'One corollary is worth writing down, because it is the form the lemma takes at the end of a traversal: a segment that runs to null <i>is</i> a list.' },
        { t: 'code', tag: 'illustration',
          cap: 'Not in the corpus — compiled against the M10 prelude.',
          src: 'theorem lseg_null_is_listRep (xs : List Nat) (p : Loc) :\n    lseg xs p 0 ⊢ listRep xs p := by\n  intro σ h hl\n  have hstar : (lseg xs p 0 ∗ listRep [] 0) σ h :=\n    ⟨h, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hl, rfl, rfl⟩\n  have hres := lseg_listRep xs [] p 0 σ h hstar\n  rw [List.append_nil] at hres\n  exact hres' },
        { t: 'p', h: 'Two details in that proof. The star is manufactured by hand with <code>Heap.empty</code> on the right, because <code>listRep [] 0</code> is satisfied by the empty heap and nothing else. And <code>rw [List.append_nil]</code> <i>is</i> needed here, unlike the <code>[] ++ ys</code> in the nil cases: <code>List.append</code> recurses on its <b>first</b> argument, so <code>[] ++ ys</code> reduces to <code>ys</code> definitionally but <code>xs ++ []</code> does not reduce to <code>xs</code> at all — that one is a theorem, proved by induction.' },
        { t: 'detail', title: 'Breaking it: what the <code>p ≠ 0</code> conjunct is actually buying', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'Neither append theorem needs the non-null side condition — delete it from both definitions and both proofs get shorter. So why keep it? Because without it the null pointer no longer decides emptiness, and the predicate stops describing linked lists. Here is a concrete heap witnessing that, checked by Lean:' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — compiled against the M10 prelude. With <code>p ≠ 0</code> removed, the two-cell heap {0 ↦ 7, 1 ↦ 0} satisfies “the one-element list [7] starting at the null pointer”.',
              src: 'def listRepBad : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p => aExists fun next => node p x next ∗ listRepBad xs next\n\nexample : listRepBad [7] 0 (fun _ => 0)\n    (Heap.union (Heap.singleton 0 7) (Heap.singleton 1 0)) :=\n  ⟨0,\n   Heap.union (Heap.singleton 0 7) (Heap.singleton 1 0), Heap.empty,\n   disjoint_empty_right _, (union_empty_right _).symm,\n   ⟨Heap.singleton 0 7, Heap.singleton 1 0, singleton_disjoint 7 0 (by decide), rfl, rfl, rfl⟩,\n   ⟨rfl, rfl⟩⟩' },
            { t: 'p', h: 'What that heap does <i>not</i> satisfy is <code>listRepBad [] 0</code> — the nil clause still demands the empty heap — so the two assertions are not literally interchangeable. The thing that is gone is the implication you actually rely on. With the side condition in place, a null start pointer forces the list to be empty, and you can prove it in three lines:' },
            { t: 'code', tag: 'illustration',
              cap: 'Not in the corpus — compiled against the M10 prelude. The seventh field of the bracket is the tail; the sixth splits <code>pure φ</code>, and its first component is <code>0 ≠ 0</code>.',
              src: 'theorem listRep_cons_null (x : Nat) (xs : List Nat) :\n    listRep (x :: xs) 0 ⊢ aFalse := by\n  intro σ h ⟨_, _, _, _, _, ⟨hne, _⟩, _⟩\n  exact hne rfl' },
            { t: 'p', h: 'Delete <code>p ≠ 0</code> and that lemma is false, so a traversal that stops when <code>p = 0</code> is being verified against a predicate which permits it to stop with elements still in the list — and the logic will not object. The side condition is what makes “the pointer is null” and “the list is empty” the <i>same</i> statement, and that equivalence is the contract every list-traversal loop relies on.' }
          ] }
      ],

      pitfall: 'Copying the cons case from <code>lseg_append</code> without dropping the fourth argument. <code>ih</code> here takes three arguments, and <code>ih ys n q q</code> produces an error that does not mention arity at all:<br><code>Application type mismatch: The last q argument has type Loc but is expected to have type Store — in the application ih ys n q q</code><br>because after three arguments the induction hypothesis is an <code>Entails</code>, which unfolds to <code>∀ σ h, …</code> — so the fourth argument is being read as the store. Whenever Lean complains that your <code>Loc</code> should be a <code>Store</code>, you have over-applied something whose result was an entailment.',

      variants: 'Swap the two conjuncts — <code>listRep ys q ∗ lseg xs p q ⊢ listRep (xs ++ ys) p</code> — and the statement is still true, but the proof needs a <code>star_comm</code> at the top and the chain no longer lines up; this is why the order in the statement is not arbitrary. Replace <code>listRep ys q</code> by <code>lseg ys q r</code> and you are back at <code>lseg_append</code>. Take <code>xs = []</code> and the theorem degenerates to <code>pure (fun _ => p = q) ∗ listRep ys q ⊢ listRep ys p</code>, which is the nil case — a useful sanity check that the statement says what you meant. And if you remove the <code>p ≠ 0</code> conjunct from <code>listRep</code> the theorem still holds, but the predicate no longer describes linked lists; the counterexample is in the collapsed block above.',

      solNote: 'The two proofs are the same proof. That is a claim about the definitions, not about the proofs: <code>lseg</code> and <code>listRep</code> differ only in their base case, and neither induction ever inspects a base case of the <i>second</i> argument. If you ever add a third linked-structure predicate, expect a third copy of this proof — and consider whether one parametrised lemma would do.'
    },

    { t: 'h3', s: 'What to carry forward' },

    { t: 'p',
      h: 'Two techniques and one design principle. The techniques: build an assertion by <code>refine</code>-ing one layer at a time and letting Lean tell you the next obligation; and prove things about recursive predicates by <code>entails_trans</code> chains rather than by descending into heaps. The principle: side conditions in two related predicates must be <i>literally the same assertion</i>, or the lemma that relates them will not compose — and the proof will tell you, at the exact step where it fails.' },

    { t: 'p',
      h: 'Forward: M11 introduces <code>-∗</code>, and its first serious use is <code>node p x n -∗ listRep xs p</code> — “a list with a hole where one node used to be”, which is what you are holding while a subroutine works on that node. M13’s loop invariants are all of the form <code>lseg visited p cur ∗ listRep remaining cur</code>, maintained across an iteration by <code>lseg_append</code> and closed at the end by <code>lseg_listRep</code>. Both of the theorems you just proved are load-bearing there.' },

    { t: 'dod',
      h: 'You can define, unfold, fold and recombine ownership of recursive pointer structures, and you can do it with the ∗-algebra rather than by hand.' }
  ]
});
