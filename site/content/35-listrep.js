registerChapter({
  id: 'listrep',
  num: '32',
  phase: 'Phase 7 · Unbounded structures',
  title: 'Lists in the heap',
  blurb: 'One assertion that describes a linked list of any length — and says, in the same breath, what shape memory has and which cells you own.',

  orient: {
    youWill: [
      'Say why no assertion built by hand out of <code>↦</code> and <code>∗</code> can describe a list whose length you do not know.',
      'Define an <code>Assertion</code>-valued function by structural recursion on a <code>List</code>, and read its <code>cons</code> case as an existential over the address of the next node.',
      'Unfold <code>listRep [10, 20, 30] p</code> into the chain it abbreviates, and name what each conjunct contributes.',
      'Say what the <code>∗</code>s guarantee — six different cells for three nodes — and what the <code>pure</code> conjuncts guarantee, by showing that the null pointer is not a one-element list.',
      'State the three fold/unfold identities, prove each by <code>entails_refl _</code>, and say why naming an identity is worth a theorem.',
      'Derive <code>p ≠ p + 1</code> from ownership rather than from arithmetic, and notice that the proof mentions no numbers.',
      'Assemble a concrete three-node list from three <code>node</code> assertions by choosing five heap cuts by hand.',
      'Say why this unit contains no command, no derivation and no triple, and which decision of Unit 18 is responsible.'
    ],
    needs: [
      'Unit 13: <code>emp</code>, <code>↦</code>, and exact ownership.',
      'Unit 14: <code>∗</code>, its six slots, and the absence of weakening and contraction.',
      'Unit 17: <code>pure</code>, <code>fact</code>, and <code>two_cells_distinct</code>.',
      'Unit 12: <code>⊢</code>, <code>entails_refl</code>, <code>aExists</code>.',
      'Unit 20: <code>List</code>, <code>[]</code> and <code>::</code>, met there as an induction warm-up. The bracket literal <code>[a, b, c]</code> is new here.',
      'Units 08–10: <code>Heap.disjoint</code>, <code>Heap.union</code>, <code>disjoint_empty_left</code>, <code>union_empty_left</code>.'
    ],
    payoff: 'Every data structure in separation logic is defined this way, and the reason the logic scales to real programs is on this page: one name stands for an unbounded amount of memory, and handing that name to a caller hands over the memory with it.'
  },

  blocks: [

    /* =========================================================== the wall ==== */

    {t:'p', h:"Take the obstruction literally. <code>l ↦ v</code> names one address. <code>P ∗ Q</code> joins two assertions and divides the heap between them. So an assertion written with <i>n</i> occurrences of <code>↦</code> and <i>n − 1</i> occurrences of <code>∗</code> constrains exactly <i>n</i> cells — you can count them off the text. A linked list of unknown length needs an unknown <i>n</i>, and there is no way to write down an unknown number of stars."},

    {t:'p', h:"The escape is that the text does not have to be written by hand. If the number of stars is determined by something, a <i>function</i> can produce the assertion from that something — and the first question is what that something should be."},

    /* ============================================================ a node ==== */

    {t:'sec', s:'A node is two cells'},

    {t:'p', h:"Fix the layout first, because everything after it depends on the choice. A node occupies two consecutive addresses: the value at <code>p</code>, and the address of the next node at <code>p + 1</code>. Both are stored in heap cells, and a heap cell holds a <code>Val</code>, which is <code>Nat</code> — the same type as <code>Loc</code>. That coincidence, fixed back in Unit 00, is what makes a linked structure expressible at all: an address is a storable value."},

    {t:'code', cap:'Two cells, side by side, owned separately. The <code>∗</code> is doing work already — it is what says the two cells are two, and not one.',
     src:"def node (p : Loc) (value next : Nat) : Assertion :=\n  (p ↦ value) ∗ ((p + 1) ↦ next)"},

    {t:'p', h:"The last node has to say &ldquo;there is nothing after me&rdquo;, and the next field must hold something. The convention taken here is the one every C-like language takes: the address <code>0</code> is null, and no node lives there. That is a modelling decision, not a fact about heaps — <code>Heap.empty</code> maps <code>0</code> to <code>none</code> like every other address, and nothing in Units 05–11 treats <code>0</code> specially."},

    {t:'p', h:"The alternative is to make the next field an <code>Option Loc</code>, with <code>none</code> for the end of the list, so that null is a value of the type rather than a convention. It is unavailable here, and the reason is worth being exact about: a heap cell holds a <code>Val</code>, and <code>Val</code> is <code>Nat</code>. Storing an <code>Option Loc</code> means changing the codomain of <code>Heap</code>, which means reproving every equation of Units 05 and 06. The cost of the convention, by contrast, is one clause in the definition below — the one that says a node's address is never <code>0</code> — and that clause is a proposition you can use, which <code>Option</code> would have given you for free and then hidden inside a constructor."},

    {t:'svg', cap:'Three nodes at addresses 1, 3 and 5, holding 10, 20 and 30. Six cells, all different. The next field of the last node holds <code>0</code>, which is the convention for &ldquo;no next node&rdquo;, and not a seventh cell.',
     src:"<svg viewBox=\"0 0 620 176\" role=\"img\" aria-label=\"Three linked-list nodes occupying six heap cells at addresses one to six; each node holds a value and the address of the next node, and the last next field holds zero\">\n  <defs>\n    <marker id=\"ah35\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"currentColor\"/>\n    </marker>\n  </defs>\n  <g class=\"dg\">\n    <g class=\"dg-t sm\">\n      <text x=\"64\"  y=\"26\" text-anchor=\"middle\" class=\"dg-note\">1</text>\n      <text x=\"124\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">2</text>\n      <text x=\"254\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">3</text>\n      <text x=\"314\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">4</text>\n      <text x=\"444\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">5</text>\n      <text x=\"504\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">6</text>\n    </g>\n    <g class=\"dg-cells\">\n      <rect class=\"a\" x=\"34\"  y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"b\" x=\"94\"  y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"a\" x=\"224\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"b\" x=\"284\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"a\" x=\"414\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"b\" x=\"474\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <text x=\"64\"  y=\"59\" text-anchor=\"middle\" class=\"dg-t\">10</text>\n      <text x=\"124\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">3</text>\n      <text x=\"254\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">20</text>\n      <text x=\"314\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">5</text>\n      <text x=\"444\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">30</text>\n      <text x=\"504\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">0</text>\n    </g>\n    <path d=\"M 124 76 L 124 98 L 250 98 L 250 76\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah35)\"/>\n    <path d=\"M 314 76 L 314 98 L 440 98 L 440 76\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah35)\"/>\n    <text x=\"504\" y=\"92\" text-anchor=\"middle\" class=\"dg-note\">null</text>\n    <path d=\"M 8 53 L 28 53\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah35)\"/>\n    <g class=\"dg-t sm\">\n      <text x=\"94\"  y=\"128\" text-anchor=\"middle\" class=\"dg-note\">node 1 10 3</text>\n      <text x=\"284\" y=\"128\" text-anchor=\"middle\" class=\"dg-note\">node 3 20 5</text>\n      <text x=\"474\" y=\"128\" text-anchor=\"middle\" class=\"dg-note\">node 5 30 0</text>\n    </g>\n    <text x=\"8\" y=\"160\" class=\"dg-lab\">p = 1</text>\n  </g>\n</svg>"},

    /* ================================================== three, by hand ==== */

    {t:'sec', s:'Three nodes, and then any number'},

    {t:'p', h:"With <code>node</code> in hand, the picture above is one line: <code>node 1 10 3 ∗ node 3 20 5 ∗ node 5 30 0</code>. Six cells, divided into three pairs, each pair divided again. If the intermediate addresses were not known you would quantify over them, and the assertion would read <code>∃ q r, node p 10 q ∗ node q 20 r ∗ node r 30 0</code>."},

    {t:'p', h:"That is a complete and honest description of a three-element list. For four elements you write another <code>∗</code> and another existential. The text grows with the length, one node at a time, which is the pattern a recursive definition exists to capture. What it recurses on has to be written down, and lists are written in brackets from here on: <code>[10, 20, 30]</code> is bracket notation for <code>10 :: (20 :: (30 :: []))</code>, the constructors Unit 20 did induction over."},

    {t:'txt', cap:'The shape, schematically. Each line is the previous line with one node peeled off the front, and the recursion is on the list of values.',
     src:"[]           ↝   p = 0\n[x]          ↝   ∃ n,   p ≠ 0  ∗  node p x n  ∗  ( n = 0 )\n[x, y]       ↝   ∃ n,   p ≠ 0  ∗  node p x n  ∗  ( ∃ m, n ≠ 0 ∗ node n y m ∗ m = 0 )\nx :: xs      ↝   ∃ n,   p ≠ 0  ∗  node p x n  ∗  ⟨ the same thing for xs, starting at n ⟩"},

    {t:'p', h:"So the assertion is a function of two things: the address the structure starts at, and the values it holds. Indexing by the values rather than by the length is a decision. A function <code>Nat → Loc → Assertion</code> saying &ldquo;there are <i>n</i> nodes here&rdquo; is shorter and is enough to state that a program does not corrupt memory. It is not enough to state anything about what the program computes: a specification for reversing a list, or for looking one value up, has to mention the values, and a length-indexed predicate has none to mention. Carrying the contents costs nothing at the point of definition and is the difference between a memory-safety property and a correctness property."},

    /* ========================================================= listRep ==== */

    {t:'sec', s:'The definition'},

    {t:'code', cap:'A recursive <code>def</code> whose result type is <code>Assertion</code>. The recursion is structural on the first argument, so Lean accepts it without a termination argument.',
     src:"def listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next"},

    {t:'anat',
     src:"def listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next",
     parts:[
       {m:'List Nat → Loc → Assertion', h:"The result of applying <code>listRep</code> to a list and an address is an assertion — a predicate on a store and a heap. Nothing here is a new kind of object; this is a function into a type the reader has had since Unit 12."},
       {m:'| [],      p =>', h:"The empty list. There are no cells to describe, so the assertion owns nothing and says one thing about the address: it is null."},
       {m:'pure (fun _ => p = 0)', h:"<code>pure φ</code> is <code>aAnd (fact φ) emp</code> — the proposition holds, <i>and the heap is empty</i>. The empty conjunct is what makes the empty list a claim about memory rather than a claim about arithmetic that happens to be dragged along."},
       {m:'| x :: xs, p =>', h:"A list with head <code>x</code> and tail <code>xs</code>, starting at <code>p</code>. The clause is written in terms of <code>xs</code>, so the recursion goes down one constructor and Lean's structural check passes without a word from you."},
       {m:'aExists fun next =>', h:"The address of the second node. It is not determined by <code>xs</code> or by <code>p</code> — the heap decides it — so the assertion cannot name it and has to quantify over it. This existential is the one thing a reader unfolding <code>listRep</code> spends most of their time handling."},
       {m:'pure (fun _ => p ≠ 0)', h:"A node's address is never null. The conjunct is <code>pure</code> and not <code>fact</code> for the reason Unit 23 gave: under <code>∗</code> a <code>fact</code> conjunct owns an arbitrary heap, and an assertion that owns an arbitrary heap is not exact."},
       {m:'node p x next', h:"Two cells at <code>p</code> and <code>p + 1</code>, holding the head value and the address the line above quantified over. This is the only place the head value appears."},
       {m:'listRep xs next', h:"The rest of the list, starting where the next field points. The <code>∗</code> in front of it is what separates the tail's cells from this node's two."}
     ]},

    {t:'p', h:"Read <code>listRep [10, 20, 30] p</code> off the clauses. Three <code>cons</code> steps and one <code>nil</code>: there is an address <code>n₁</code> such that <code>p</code> is not null, the two cells at <code>p</code> hold <code>10</code> and <code>n₁</code>, and separately from them there is an address <code>n₂</code> such that <code>n₁</code> is not null, the two cells at <code>n₁</code> hold <code>20</code> and <code>n₂</code>, and separately from those there is an address <code>n₃</code> such that <code>n₂</code> is not null, the two cells at <code>n₂</code> hold <code>30</code> and <code>n₃</code>, and separately from all six cells, <code>n₃</code> is <code>0</code> and there is nothing left."},

    {t:'code', tag:'illustration', cap:'The same sentence in Lean. The proof is <code>entails_refl _</code>, because the two sides are one term written two ways — Lean reduces the left one to the right one by unfolding the definition three times.',
     src:"example (p : Loc) :\n    listRep [10, 20, 30] p ⊢\n      aExists fun n₁ => pure (fun _ => p ≠ 0) ∗ node p 10 n₁ ∗\n        aExists fun n₂ => pure (fun _ => n₁ ≠ 0) ∗ node n₁ 20 n₂ ∗\n          aExists fun n₃ => pure (fun _ => n₂ ≠ 0) ∗ node n₂ 30 n₃ ∗\n            pure (fun _ => n₃ = 0) :=\n  entails_refl _"},

    /* ================================================= the two readings ==== */

    {t:'sec', s:'What it says twice'},

    {t:'note', kind:'key', title:'The double reading',
     h:"<code>listRep xs p</code> makes two claims in one breath, and they are inseparable because they are the same text. <b>Shape:</b> memory, at these addresses, is arranged as a chain of two-cell nodes ending at null, and the values along it are <code>xs</code> in order. <b>Ownership:</b> the heap the assertion is evaluated at consists of <i>exactly</i> two cells for every entry of <code>xs</code>, and nothing else. Neither reading is a consequence of the other, and the second is the one that makes the first usable."},

    {t:'p', h:"The ownership half is carried entirely by the <code>∗</code>s. Unfold one step: <code>pure (p ≠ 0) ∗ node p x next ∗ listRep xs next</code> divides the heap into three pieces that are pairwise disjoint. The first is empty. The second is the two cells at <code>p</code> and <code>p + 1</code>. The third holds the whole tail. So the head node's addresses do not occur anywhere in the tail, and the same argument applies at every step down the chain: <i>every</i> address of <i>every</i> node is different from every address of every later node. Three nodes are six cells, not five and not four — and a chain that ran back into itself would have to reuse an address, so that is excluded here, before anything has been said about where the chain stops."},

    {t:'p', h:"Change the connective and that disappears. Replace each <code>∗</code> by <code>aAnd</code> and the resulting predicate hands the <i>same</i> heap to the head node and to the tail. The <code>pure</code> conjuncts have to go with it: their <code>emp</code> half would now be a claim about the <i>whole</i> heap, and a <code>cons</code> case demanding both an empty heap and a node sitting in it is satisfied by nothing at all — so what is left of them is the bare <code>fact</code>. It is still a predicate, it still typechecks, and it still describes a shape of sorts. What it stops being is a claim about resources — and the shortest way to see that is to duplicate it."},

    {t:'code', tag:'illustration', cap:'The classical variant, and one line proving that anything satisfying it satisfies it twice. Both copies are handed the same heap, so nothing was divided and nothing was spent.',
     src:"def listRepAnd : List Nat → Loc → Assertion\n  | [],      p => fact (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        aAnd (fact (fun _ => p ≠ 0)) (aAnd (node p x next) (listRepAnd xs next))\n\nexample (xs : List Nat) (p : Loc) :\n    listRepAnd xs p ⊢ aAnd (listRepAnd xs p) (listRepAnd xs p) :=\n  and_intro (entails_refl _) (entails_refl _)"},

    {t:'p', h:"Unit 14 proved that <code>∗</code> admits no such rule in general: <code>no_star_duplication</code> refutes <code>∀ P, P ⊢ P ∗ P</code>. For <code>listRep</code> the failure is concrete rather than generic — two copies of a three-node list want twelve pairwise-disjoint cells and only six exist. The one exception is the list that owns nothing, since <code>2n</code> cells divide into two disjoint copies of themselves only when <code>n</code> is zero."},

    {t:'code', tag:'illustration', cap:'The empty list splits into two empty lists, because <code>Heap.empty</code> is disjoint from itself and their union is <code>Heap.empty</code> again. Every other list refuses.',
     src:"example (p : Loc) : listRep [] p ⊢ listRep [] p ∗ listRep [] p := by\n  intro σ h ⟨hz, he⟩\n  exact ⟨Heap.empty, Heap.empty, disjoint_empty_left _,\n         by rw [he, union_empty_left], ⟨hz, rfl⟩, ⟨hz, rfl⟩⟩"},

    {t:'p', h:"The <code>pure</code> conjuncts carry a different guarantee: they say where the chain ends. Every <code>cons</code> step asserts <code>p ≠ 0</code>, and the <code>nil</code> case asserts that the address it is handed <i>is</i> <code>0</code>. So walking the next fields from the head reaches <code>0</code> after exactly <code>length xs</code> steps, and no node sits at <code>0</code> along the way. That excludes the chain running back into itself a second time, by an argument with no heap in it: if the last next field pointed at a node already passed, the <code>nil</code> case would demand that node's address be <code>0</code> and the <code>cons</code> step that produced it demanded the opposite."},

    {t:'p', h:"The smallest case is the sharpest one. A single node whose next field is <code>0</code>, sitting at address <code>0</code>, looks like a one-element list and is not one — and what refuses it is the <code>pure</code> conjunct, not the cells."},

    {t:'code', tag:'illustration', cap:'A refutation, so it needs a witness: the store is irrelevant and the heap is the two cells at 0 and 1, built as a union of singletons. The last line reads the non-nullness conjunct straight out of the tuple and applies it to <code>rfl</code>.',
     src:"example (a : Val) : ¬ (node 0 a 0 ⊢ listRep [a] 0) := by\n  intro hbad\n  have hnode : node 0 a 0 (fun _ => 0)\n      (Heap.union (Heap.singleton 0 a) (Heap.singleton 1 0)) :=\n    ⟨Heap.singleton 0 a, Heap.singleton 1 0, singleton_disjoint a 0 (by simp), rfl, rfl, rfl⟩\n  obtain ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩ := hbad _ _ hnode\n  exact hp rfl"},

    {t:'detail', title:'Why this is a least fixed point, and what a non-structural recursion would cost', tag:'aside',
     blocks:[
       {t:'p', h:"Written as an equation rather than as a definition, <code>listRep</code> says that a certain operator on predicates has <code>listRep</code> as a fixed point: unfold the left-hand side one step and you get the right-hand side back with <code>xs</code> shorter. Equations of that kind generally have many solutions, and the interesting ones differ over infinite structures. The <i>least</i> solution — the smallest predicate closed under the two clauses — describes only finite chains; the greatest one also admits circular structures that never reach null."},
       {t:'p', h:"That question does not arise here, and it is worth knowing why not. The recursion is on <code>xs : List Nat</code>, and <code>List</code> is an inductive type: every element of it is finite, built by finitely many <code>::</code> steps from <code>[]</code>. So <code>listRep xs p</code> is defined by recursion over an object that was already finite by construction, and the least fixed point is the only fixed point there is. Unit 19 made the same move for <code>Exec</code>: an inductive definition is the least relation closed under its rules, and finiteness comes from the induction principle rather than from a side condition."},
       {t:'p', h:"The alternative — recursing on the <i>heap</i>, or on the chain of addresses, rather than on the list — is where the fixed-point question would become real, and Lean refuses it before it can. A clause whose recursive call is on the same list is not structural, and there is no measure that decreases."},
       {t:'code', tag:'sketch', cap:'Rejected by the termination checker — the complaint Unit 19 got from <code>runBad</code>, for the same reason and about different arguments.',
        src:"def listRepLoop : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRepLoop (x :: xs) next"},
       {t:'state', cap:'What Lean says. The position prefix is dropped, as everywhere in this course, and so are the last five lines — a table of candidate measures and a suggestion to supply one by hand. The two parameters it names are the list and the address, and neither gets smaller.',
        src:"error: fail to show termination for\n  listRepLoop\nwith errors\nfailed to infer structural recursion:\nCannot use parameter #1:\n  failed to eliminate recursive application\n    listRepLoop (x :: xs) next\nCannot use parameter #2:\n  failed to eliminate recursive application\n    listRepLoop (x :: xs) next\n\n\nCould not find a decreasing measure."},
       {t:'p', h:"Reading that message as a statement about separation logic rather than about Lean: a predicate defined by walking the heap would have to say what happens when the walk never stops, and the answer is a choice between two fixed points. A predicate defined by walking a list has already made the choice."}
     ]},

    /* ========================================== the fold/unfold interface ==== */

    {t:'sec', s:'The fold/unfold interface'},

    {t:'p', h:"Unfolding <code>listRep [10, 20, 30] p</code> three steps took <code>entails_refl _</code> and nothing else. What makes that work is the rule Unit 02 stated and Unit 09 turned into a technique: a definition by pattern matching computes exactly when its argument is a constructor application. <code>x :: xs</code> is one, so <code>listRep (x :: xs) p</code> reduces to the body of the <code>cons</code> clause without being asked. Every later proof about lists needs that reduction, and the question is whether to rely on it silently or to name it."},

    {t:'p', h:"Name it. Three theorems: what <code>listRep [] p</code> gives you, what <code>listRep (x :: xs) p</code> gives you, and how to build one. Each is an identity, so each is <code>entails_refl _</code> and costs one line. What the three lines buy is a place to point at. Reduction is silent: a proof that hands an algebraic lemma a folded <code>listRep</code> works because the type checker unfolded it, and no character of that proof says so. Move the non-null conjunct to the far side of the node, reorder the two stars, or let the existential range over the head address instead of the next one, and these three statements stop typechecking and say exactly what changed — while a proof leaning on reduction alone fails somewhere else, with a message about a term nobody wrote."},

    {t:'ex',
     id:'m10-1',
     name:'the three fold/unfold lemmas',
     why:"Two things, and the second is the honest one. First, this is the cheapest demonstration in the course of a distinction that matters: <code>listRep [] p</code> and <code>pure (fun _ => p = 0)</code> are not two propositions that happen to be equivalent, they are one term displayed two ways — which is why the proof is reflexivity and not an argument. Second, none of the three is cited by name anywhere later in this course's Lean. Grep for them and you find nothing, because every later proof about lists gets the same reduction for free from the type checker. What the names buy is diagnosis rather than proof: they are the three statements that break, and say what broke, if the definition is ever changed underneath them.",
     setup:"All three are term-mode. <code>entails_refl</code> takes the assertion explicitly, so it is applied to <code>_</code> and Lean fills it in from the goal. Nothing needs to be unfolded by hand.",
     goal:"theorem listRep_nil (p : Loc) : listRep [] p ⊢ pure (fun _ => p = 0) :=\n  sorry\n\ntheorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next :=\n  sorry\n\ntheorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p :=",
     hints:[
       "Look at what each statement asks for. In the first, the left-hand side is <code>listRep</code> applied to the empty list, and the right-hand side is what the <code>nil</code> clause of the definition returns. In the second and third, the left and right are the <code>cons</code> clause and its body, in one order and then the other.",
       "An entailment whose two sides are the same assertion is an instance of reflexivity. The only question is whether the two sides really are the same assertion, and they are: applying a function defined by pattern matching to a literal constructor reduces to the corresponding clause, and reduction is not something you have to prove.",
       "Unit 12's <code>entails_refl</code> is the theorem you want, in all three. It takes the assertion as an explicit argument.",
       "Write <code>entails_refl _</code> after the <code>:=</code> in each of the three. The underscore is the assertion, and Lean determines it by unifying <code>?P ⊢ ?P</code> with the stated goal — which is exactly where the reduction happens, and where it would fail if the two sides were not definitionally equal."
     ],
     sol:"theorem listRep_nil (p : Loc) : listRep [] p ⊢ pure (fun _ => p = 0) := entails_refl _\n\ntheorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next :=\n  entails_refl _\n\ntheorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p :=\n  entails_refl _",
     solNote:"Three theorems, three identical proofs, and the third is the second backwards. If you find that unsatisfying, that is the right reaction and the reason to write them anyway: the content is in the statements, and they are the only place in the course where the shape of a <code>listRep</code> clause is written out and checked against the definition.",
     expl:"Each goal is <code>A ⊢ B</code> where <code>A</code> and <code>B</code> are the same term after unfolding <code>listRep</code> at a constructor pattern. <code>entails_refl _</code> has type <code>?P ⊢ ?P</code>; unifying it with the goal forces <code>?P</code> to be the left-hand side and then requires the right-hand side to be definitionally equal to it. Lean performs the unfolding during that check, so the proof succeeds without any tactic naming the definition.",
     walk:[
       {tac:'theorem listRep_nil (p : Loc) : listRep [] p ⊢ pure (fun _ => p = 0) :=',
        h:"A term-mode declaration, so what follows <code>:=</code> is a value whose type is the statement. That type is an <code>Entails</code>, which is a <code>∀</code> over a store, a heap and a proof — but nothing here has to look inside it."},
       {tac:'entails_refl _',
        h:"Reflexivity, with its assertion argument left to be inferred. Inference solves it as <code>listRep [] p</code> and then checks that <code>pure (fun _ => p = 0)</code> is the same term. It is: <code>listRep</code> applied to <code>[]</code> selects the first clause, whose body is exactly that."},
       {tac:'theorem listRep_cons_unfold (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next :=',
        h:"The second statement. The left side is the folded name applied to a <code>cons</code>; the right side is the <code>cons</code> clause's body written out — the existential, the <code>pure</code> and the two stars."},
       {tac:'  entails_refl _',
        h:"The same move against a bigger term, and it succeeds for the same reason: applying the definition to <code>x :: xs</code> selects the second clause and produces that body."},
       {tac:'theorem listRep_cons_fold (x : Nat) (xs : List Nat) (p : Loc) :\n    (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      listRep (x :: xs) p :=',
        h:"The mirror: the written-out body on the left, the folded name on the right. The brackets round the left-hand side are needed because a <code>fun</code> body runs as far right as it can, and without them the <code>⊢</code> would be swallowed by the lambda."},
       {tac:'  entails_refl _',
        h:"Reflexivity does not care which way round a definitional equality is presented, which is why the fold and the unfold have the same proof — and different jobs: one is the statement to reach for where a list is taken apart, the other where one is built."}
     ],
     deep:[
       {t:'p', h:"The proof is short enough that nothing shows. Writing the first one in tactic mode with an explicit <code>show</code> makes the reduction visible as a change in the goal display."},
       {t:'trace', title:'listRep_cons_unfold, with the unfolding made visible',
        start:"x : Nat\nxs : List Nat\np : Loc\n⊢ listRep (x :: xs) p ⊢ aExists fun next => (_root_.pure fun x => p ≠ 0) ∗ node p x next ∗ listRep xs next",
        steps:[
          {tac:'show (aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n      aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next',
           state:"x : Nat\nxs : List Nat\np : Loc\n⊢ (aExists fun next => (_root_.pure fun x => p ≠ 0) ∗ node p x next ∗ listRep xs next) ⊢\n    aExists fun next => (_root_.pure fun x => p ≠ 0) ∗ node p x next ∗ listRep xs next",
           h:"<code>show</code> restates a goal as anything definitionally equal to it, and it is accepted here — which is the proof that the unfolding is legitimate. The goal is now visibly of the form <code>A ⊢ A</code>."},
          {tac:'exact entails_refl _',
           state:"No goals.",
           h:"With both sides displayed identically there is nothing left to decide. The shipped proof skips the <code>show</code>, because the same check happens inside <code>exact</code>."}
        ],
        done:'No goals.'},
       {t:'p', h:"Two details of the display in that trace are worth naming once. <code>pure</code> prints as <code>_root_.pure</code> because Lean's core library also has a <code>pure</code> and ours wins by type — Unit 17 met this. And the binder inside <code>pure</code> prints as <code>fun x</code>, reusing the name of the head value that is already in scope; the two are unrelated, and the one inside <code>pure</code> is the store argument that <code>fact</code> discards."}
     ],
     pitfall:"Reaching for <code>rfl</code> instead of <code>entails_refl _</code>. The goal is not an equation: <code>listRep [] p ⊢ pure (fun _ => p = 0)</code> is an <code>Entails</code>, and <code>rfl</code> proves <code>a = a</code>. Lean reports it twice, and the first message is the interesting one: <code>Not a definitional equality: the conclusion should be an equality, but is fact (fun x => p = 0) σ h ∧ emp σ h</code>. <code>rfl</code> has pushed through the two binders and the hypothesis of the entailment, arrived at the conclusion, unfolded <code>pure</code> into its conjunction — and found no <code>=</code> to be reflexive about. The second message is the blunt one: <code>Type mismatch: rfl has type ?m.7 = ?m.7 but is expected to have type listRep [] p ⊢ _root_.pure fun x => p = 0</code>. The two sides <i>are</i> definitionally equal assertions, which is why reflexivity of <code>⊢</code> closes the goal; reflexivity of <code>=</code> would prove a different statement, and there is no equation here to state it about.",
     variants:"Try to state the <code>cons</code> case as an <i>equation</i> — <code>listRep (x :: xs) p = aExists fun next =&gt; …</code> — and there are two reasons not to. The first is half of Unit 12's objection to equality between assertions. That objection had two parts: proving one costs <code>funext</code> and <code>propext</code>, and what you want back out of it is almost always a single direction. The first part does not bite here — this equation is a definitional identity and <code>rfl</code> settles it with no axioms at all — and the second does. The second reason is sharper and Unit 02 owns it. Written as an <code>example</code>, <code>:= rfl</code> proves that equation. Written as a <code>theorem</code>, the Lean in your browser refuses it — <code>Not a definitional equality: the left-hand side listRep (x :: xs) p is not definitionally equal to the right-hand side aExists fun next => (_root_.pure fun x => p ≠ 0) ∗ node p x next ∗ listRep xs next</code> — because a <code>theorem</code> is exported and may not unfold a plain <code>def</code> to prove itself. <code>entails_refl _</code> is not affected, and that is one more reason the interface is three entailments rather than three equations. · Drop <code>listRep_cons_fold</code> and keep only the unfolding: every proof that <i>builds</i> a list then appeals to reduction directly, which is the dependence the three lemmas exist to remove. · State the <code>nil</code> case as <code>listRep [] p ⊣⊢ pure (fun _ => p = 0)</code> and both components are <code>entails_refl _</code>; that is a legitimate alternative packaging, and the corpus keeps the two <code>cons</code> directions separate for the reason above — a proof wants one of them or the other, never both."
    },

    /* ================================================== pure information ==== */

    {t:'sec', s:'Information that falls out'},

    {t:'p', h:"A recursive predicate is worth defining only if facts can be got back out of it, and the cheapest kind is a fact with no heap in it. The head of a non-empty list is not null. That is written into the <code>cons</code> clause, so nobody should have to trust it: it should be a theorem, and the theorem should be extractable by a caller who has a <code>listRep</code> and wants to know the address is safe to work with."},

    {t:'ex',
     id:'x65',
     name:'listRep_cons_ne_zero',
     why:"The first fact pulled out of a recursive predicate, and the pattern for every later one: open the existential, open the star, take the conjunct you want, ignore the rest. It is also where the two embeddings each earn a line. The definition's conjunct is <code>pure</code>, so under the star it takes the empty piece of the heap and <code>listRep</code> stays exact; the conclusion is <code>fact</code>, so what the caller gets back is a proposition with no heap attached to it. The proof is one <code>exact</code> because those two are the same <code>fact</code> term.",
     setup:"Unit 14's six-slot <code>intro</code> pattern, with an existential in front of it and one slot destructured further — the slot holding the <code>pure</code> conjunct, which is itself a conjunction.",
     goal:"theorem listRep_cons_ne_zero (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢ fact (fun _ => p ≠ 0) := by",
     hints:[
       "The goal is an entailment, so it is a function of three arguments: a store, a heap, and a proof that <code>listRep (x :: xs) p</code> holds there. What has to be produced is a proof of <code>fact (fun _ => p ≠ 0)</code> at the same store and heap — which, unfolding <code>fact</code>, is a proof of <code>p ≠ 0</code>.",
       "The premise is a <code>cons</code> case, so it is an existential over the next address whose body is a three-way separating conjunction. The leftmost conjunct of that body <i>is</i> the fact you are asked for, packaged with a claim that its heap is empty. Take the premise apart and hand back the piece.",
       "One <code>intro</code> with a pattern, then <code>exact</code>. The pattern needs a name for the existential witness, then Unit 14's six slots, and the fifth of those has to be split in two because <code>pure</code> is a conjunction.",
       "Start with <code>intro σ h ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩</code>. That leaves <code>hp : fact (fun x => p ≠ 0) σ h₁</code> and the goal <code>fact (fun x => p ≠ 0) σ h</code> — different heaps, and one <code>exact</code> away, for a reason the walk spells out."
     ],
     sol:"theorem listRep_cons_ne_zero (x : Nat) (xs : List Nat) (p : Loc) :\n    listRep (x :: xs) p ⊢ fact (fun _ => p ≠ 0) := by\n  intro σ h ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩\n  exact hp",
     solNote:"Two lines, and the second one is doing something that looks illegal until you unfold <code>fact</code>.",
     expl:"The premise is opened in one <code>intro</code>: seven names, of which four are underscores. What survives is <code>hp</code>, the non-nullness conjunct, sitting at the empty sub-heap <code>h₁</code>. The goal wants the same conjunct at the whole heap <code>h</code>. Those are different-looking propositions and the same one, because <code>fact φ</code> is <code>fun σ _ => φ σ</code> — the heap argument is discarded, so <code>fact φ σ h₁</code> and <code>fact φ σ h</code> reduce to the identical proposition <code>φ σ</code>.",
     walk:[
       {tac:'intro σ h ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩',
        h:"Three <code>intro</code>s in one line, the third against a pattern. The pattern's first name is the witness of <code>aExists</code>; the next six are the star's slots — the two sub-heaps, disjointness, the union equation, the left assertion and the right one. The fifth slot holds <code>pure (fun _ => p ≠ 0) σ h₁</code>, a conjunction, so <code>⟨hp, _⟩</code> takes it apart and keeps the left half. The four underscores are the facts this proof does not need: the two heaps do not have to be compared, and the tail is irrelevant."},
       {tac:'exact hp',
        h:"Closes the goal. <code>hp</code> is stated at <code>h₁</code> and the goal at <code>h</code>, and the two types are definitionally equal because <code>fact</code> ignores its heap argument. This is the first place in the course where <i>not</i> owning anything is what makes a term reusable at a different heap."}
     ],
     deep:[
       {t:'trace', title:'The whole proof, both states',
        start:"x : Nat\nxs : List Nat\np : Loc\n⊢ listRep (x :: xs) p ⊢ fact fun x => p ≠ 0",
        steps:[
          {tac:'intro σ h ⟨n, h₁, h₂, _, _, ⟨hp, _⟩, _⟩',
           state:"x : Nat\nxs : List Nat\np : Loc\nσ : Store\nh : Heap\nn : Nat\nh₁ h₂ : Heap\nleft✝¹ : h₁.disjoint h₂\nleft✝ : h = h₁.union h₂\nhp : fact (fun x => p ≠ 0) σ h₁\nright✝¹ : emp σ h₁\nright✝ : (node p x n ∗ listRep xs n) σ h₂\n⊢ fact (fun x => p ≠ 0) σ h",
           h:"Every underscore in the pattern has become an inaccessible name — <code>left✝</code> for a left component, <code>right✝</code> for a right one, superscripts counting backwards. The premise has been fully unfolded on the way in: nothing named <code>listRep (x :: xs)</code> survives, because <code>intro</code> saw through the definition to find the binders."},
          {tac:'exact hp',
           state:"No goals.",
           h:"<code>hp</code> is at <code>h₁</code>, the goal at <code>h</code>, and the check passes."}
        ],
        done:'No goals.'},
       {t:'p', h:"The context is worth one more look for what it says about the definition. <code>right✝¹ : emp σ h₁</code> is the empty half of <code>pure</code>, and it is the reason <code>h₁</code> was never going to matter. <code>left✝ : h = h₁.union h₂</code> says the whole heap is that empty piece together with everything else — so the star in front of a <code>pure</code> conjunct cuts nothing off, and the tuple's first two slots could have been <code>Heap.empty</code> and <code>h</code>. That is the observation the construction exercise later on runs on."}
     ],
     pitfall:"Stopping the pattern one level early. <code>intro σ h ⟨n, h₁, h₂, _, _, hp, _⟩</code> is accepted — the flattening does not complain — and <code>hp</code> then names the whole <code>pure</code> conjunction rather than its left half. The complaint arrives at the next line: <code>Type mismatch: hp has type _root_.pure (fun x => p ≠ 0) σ h₁ but is expected to have type fact (fun x => p ≠ 0) σ h</code>. The fix is <code>⟨hp, _⟩</code> in that slot, not a change to <code>exact</code>.",
     variants:"Name the underscores — <code>intro σ h ⟨n, h₁, h₂, hd, hu, ⟨hp, hemp⟩, hrest⟩</code> — and the proof is unchanged and compiles; underscores here are hygiene, not necessity. · Ask for the conclusion as <code>pure</code> rather than <code>fact</code> and the theorem becomes <i>false</i> rather than harder, and it is false at exactly one point: the <code>emp</code> half. Hand the entailment the store <code>fun _ => 0</code> and the two-cell heap <code>Heap.union (Heap.singleton 1 a) (Heap.singleton 2 0)</code>, which satisfies <code>listRep [a] 1</code> with witness <code>0</code>; the <code>pure</code> that comes back claims that heap <i>is</i> <code>Heap.empty</code>, and evaluating both sides at address <code>1</code> gives <code>some a</code> against <code>none</code>. Fourteen lines, eight of them the heap and the witness. · State it for <code>listRep xs p</code> with <code>xs</code> arbitrary and it is false at <code>xs = []</code>, <code>p = 0</code>, where the <code>nil</code> clause asserts exactly the opposite; the refutation is three lines, because <code>listRep [] 0 (fun _ => 0) Heap.empty</code> is <code>⟨rfl, rfl⟩</code>. The hypothesis that the list is a <code>cons</code> is the only reason the pattern has an existential in it at all. · Reach one level deeper for the head <i>node</i> rather than the head fact — <code>⟨n, h₁, h₂, _, _, ⟨_, _⟩, ⟨h₃, h₄, _, _, hn, _⟩⟩</code>, giving <code>hn : node p x n σ h₃</code> — and it does not travel, however accommodating you make the conclusion. Weaken the goal all the way to <code>listRep (x :: xs) p ⊢ aExists (fun n => node p x n)</code>, so that the witness and the values are no longer in dispute, and <code>exact ⟨n, hn⟩</code> is still refused: <code>Application type mismatch: The argument hn has type node p x n σ h₃ but is expected to have type (fun n => node p x n) n σ h</code>. <code>h₃</code> is the node's two cells, <code>h</code> is the whole heap, and nothing in the context identifies them. Only an assertion that ignores its heap argument travels between heaps for free, and <code>fact</code> is the one that does — which is why it, and not <code>pure</code>, is what the conclusion asks for."
    },

    /* ============================================ distinctness from owning ==== */

    {t:'sec', s:'Where the disequality comes from'},

    {t:'p', h:"A node occupies <code>p</code> and <code>p + 1</code>, and those had better be two addresses rather than one. There is an obvious proof: <code>p ≠ p + 1</code> is a fact about natural numbers, and a reader with arithmetic available would settle it and move on."},

    {t:'p', h:"That proof is not the one to write, and Unit 17 said why when it proved <code>two_cells_distinct</code>: if two assertions each own a cell and they sit on opposite sides of a <code>∗</code>, then the cells are at different addresses, because the two sub-heaps are disjoint and a heap cannot be disjoint from itself at an allocated address. The premise is ownership. Arithmetic never enters, and the conclusion holds for whatever the addresses happen to be."},

    {t:'ex',
     id:'m10-2',
     name:'node_cells_distinct',
     why:"One line, and it is the promise Unit 17 made being kept. It also settles a question the definition of <code>node</code> raises and does not answer: nothing in <code>(p ↦ value) ∗ ((p + 1) ↦ next)</code> says the two addresses differ, and it does not have to, because <code>∗</code> says it. The same argument, applied down the chain, is what makes a three-node list six cells.",
     setup:"<code>two_cells_distinct</code> is Unit 17's theorem: <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)</code>, with all four arguments explicit. <code>node</code> is a plain <code>def</code>, so its body is available to the type checker without being unfolded by hand.",
     goal:"theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=",
     hints:[
       "Unfold <code>node</code> in your head. The statement is <code>(p ↦ x) ∗ ((p + 1) ↦ next) ⊢ fact (fun _ => p ≠ p + 1)</code> — an instance of something the course already has.",
       "Two cells owned separately are at different addresses. That is a theorem about <code>∗</code> and <code>↦</code>, proved in Unit 17, and it is not proved again here.",
       "<code>two_cells_distinct</code>, applied. It takes two addresses and two values, in that order, all explicit.",
       "Write <code>two_cells_distinct p (p + 1) x next</code> after the <code>:=</code>. Its type is then <code>(p ↦ x) ∗ ((p + 1) ↦ next) ⊢ fact (fun _ => p ≠ p + 1)</code>, and the goal is that statement with <code>node</code> folded over the left-hand side."
     ],
     sol:"theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=\n  two_cells_distinct p (p + 1) x next",
     solNote:"No tactic, no unfolding, and no arithmetic. If a reader wants the arithmetic proof they can have it, and it will prove a different theorem — one that says nothing about memory.",
     expl:"<code>node p x next</code> is by definition <code>(p ↦ x) ∗ ((p + 1) ↦ next)</code>, so the goal is definitionally an instance of <code>two_cells_distinct</code> with <code>l₁ := p</code>, <code>l₂ := p + 1</code>, <code>v₁ := x</code>, <code>v₂ := next</code>. Supplying those four arguments produces a term of exactly the right type, and the check that <code>node p x next</code> matches the star costs the type checker one unfolding.",
     walk:[
       {tac:'theorem node_cells_distinct (p : Loc) (x next : Nat) :\n    node p x next ⊢ fact (fun _ => p ≠ p + 1) :=',
        h:"The statement to be inhabited. Note which side <code>p + 1</code> is on: <code>two_cells_distinct</code> concludes <code>l₁ ≠ l₂</code> in the order its arguments were given, so the order chosen here decides whether the result is <code>p ≠ p + 1</code> or its symmetric twin."},
       {tac:'two_cells_distinct p (p + 1) x next',
        h:"Four explicit arguments, and no proof obligation left behind. The disequality is produced by the disjointness hypothesis buried in the premise, which the reader never sees because Unit 17 already discharged it."}
     ],
     deep:[
       {t:'trace', title:'The same proof in tactic mode, with the unfolding shown',
        start:"p : Loc\nx next : Nat\n⊢ node p x next ⊢ fact fun x => p ≠ p + 1",
        steps:[
          {tac:'show (p ↦ x) ∗ ((p + 1) ↦ next) ⊢ fact (fun _ => p ≠ p + 1)',
           state:"p : Loc\nx next : Nat\n⊢ p ↦ x ∗ p + 1 ↦ next ⊢ fact fun x => p ≠ p + 1",
           h:"The goal now displays the star. Lean has dropped the brackets you typed, because <code>↦</code> binds at 60 and <code>∗</code> at 55, so <code>p ↦ x ∗ p + 1 ↦ next</code> parses the way it is meant to; <code>+</code> binds tighter still, which is why <code>p + 1 ↦ next</code> is one cell and not a sum of two things."},
          {tac:'exact two_cells_distinct p (p + 1) x next',
           state:"No goals.",
           h:"The shipped proof omits the <code>show</code>: the same unfolding happens when the term's type is checked against the goal."}
        ],
        done:'No goals.'},
       {t:'p', h:"Nothing in that proof mentions <code>Nat</code>. Replace <code>Loc</code> by an abstract type of addresses with no arithmetic on it, give a node's two fields two unrelated addresses instead of <code>p</code> and <code>p + 1</code>, and the line still typechecks — because what is being used is that the two cells are owned on opposite sides of a star, not that the numbers differ. That is a claim about the whole development: Unit 10's partial commutative monoid, not <code>Nat</code>, is what the disjointness arguments run on."}
     ],
     pitfall:"Swapping the two addresses. <code>two_cells_distinct (p + 1) p next x</code> is a perfectly good theorem, and Lean prints what it proves: <code>Type mismatch: two_cells_distinct (p + 1) p next x has type p + 1 ↦ next ∗ p ↦ x ⊢ fact fun x =&gt; p + 1 ≠ p but is expected to have type node p x next ⊢ fact fun x =&gt; p ≠ p + 1</code>. <code>p + 1 ≠ p</code> and <code>p ≠ p + 1</code> are different propositions related by <code>Ne.symm</code>, exactly as Unit 03 said when it introduced <code>Ne</code>. Swapping only the addresses and leaving the values alone gives the same shape of message with the two cells crossed as well, so the display tells you both mistakes at once.",
     variants:"Prove it by arithmetic instead: <code>fun _ _ _ =&gt; by simp [fact]</code> ignores the premise entirely and compiles. What is lost is that the theorem stops being evidence about memory — the identical proof goes through with <code>node p x next</code> replaced by <code>aTrue</code>, so it says nothing about what is owned. · Change the layout so that both fields sit at <code>p</code> — <code>(p ↦ value) ∗ (p ↦ next)</code> — and the interesting thing happens: <code>two_cells_distinct p p x next</code> still proves the corresponding statement, now reading <code>p ≠ p</code>, and it compiles. The theorem is vacuously true because <i>nothing satisfies the premise</i>. A broken layout does not announce itself as a failed proof; it announces itself as an assertion no heap satisfies, which is the failure mode Unit 07 named and the reason an exercise like <code>x16</code> exists at all. · Ask for <code>p ≠ p + 2</code> and <code>two_cells_distinct p (p + 2) x next</code> proves the <i>conclusion</i> you wanted and nothing else: <code>Type mismatch: two_cells_distinct p (p + 2) x next has type p ↦ x ∗ p + 2 ↦ next ⊢ fact fun x => p ≠ p + 2 but is expected to have type node p x next ⊢ fact fun x => p ≠ p + 2</code>. The two <code>fact</code>s agree; the premises do not, because a node owns <code>p</code> and <code>p + 1</code> and nothing owns <code>p + 2</code>. The disequalities you can get out of a <code>∗</code> are exactly those between addresses it actually mentions."
    },

    /* ============================================== building one by hand ==== */

    {t:'sec', s:'Building one'},

    {t:'p', h:"Every proof so far has consumed a <code>listRep</code>. The other direction is the one a program needs: you hold three nodes, they are chained, and you want to hand a caller a single assertion saying so. That is a proof whose every step chooses a heap cut, and there are five of them."},

    {t:'p', h:"The rhythm is fixed by the shape of the <code>cons</code> clause. To prove <code>listRep (x :: xs) p</code> at a heap you must (i) supply the witness for the existential — the address the next field holds; (ii) cut the heap for the <code>pure</code> conjunct, which owns nothing, so the cut is <code>Heap.empty</code> on the left and everything on the right; (iii) cut again to give the head node its two cells and leave the rest; (iv) recurse. Three nodes means that sequence three times, and then the <code>nil</code> case, which needs the empty heap and the address <code>0</code>."},

    {t:'ex',
     id:'m10-3',
     name:'concrete_list',
     hard:true,
     why:"The only construction proof in this unit, and the shape of every one that follows: witness, split off the empty heap for the <code>pure</code>, hand the node its cells, recurse. Reading a list apart is one <code>intro</code>; building one is five cuts chosen by hand, and knowing which is which is what makes the next unit's algebraic proofs feel like a relief rather than a trick.",
     setup:"The premise is a three-way star, so the flattened pattern has eleven names: five for the outer star (with its right-hand assertion opened rather than named) and six for the inner one. <code>disjoint_empty_left</code>, <code>union_empty_left</code>, <code>disjoint_empty_right</code> and <code>union_empty_right</code> are Units 08 and 09.",
     goal:"theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p := by",
     hints:[
       "The premise says the heap divides into three pieces holding three nodes, chained: the first node's next field is <code>q</code>, the second's is <code>r</code>, the third's is <code>0</code>. The goal says the same heap satisfies <code>listRep [a, b, c] p</code>, which unfolds to three existentials, three non-nullness claims and three nodes, with an empty heap at the end. The three disequality hypotheses are there because the goal asserts them and the premise does not.",
       "Take the premise apart once, then build the goal from the outside in. Each <code>cons</code> step needs four decisions: what address the existential is witnessed by, how the heap splits for the <code>pure</code> conjunct, how the remainder splits between the node and the tail, and then the same again one level down.",
       "<code>intro</code>, then <code>obtain</code> to flatten the premise, then <code>subst</code> on the two heap equations so that the heap in the goal is written out in terms of the pieces you have, then a <code>refine</code> per layer with a <code>?_</code> for the rest.",
       "Open with <code>intro σ h hstar</code> and <code>obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd', hu', hn₂, hn₃⟩ := hstar</code>. That leaves eleven new names in the context and the goal <code>listRep [a, b, c] p σ h</code>; <code>subst hu'</code> and <code>subst hu</code> then replace <code>h</code> by <code>h₁.union (h₃.union h₄)</code> everywhere, and the first cut can be read straight off the result."
     ],
     sol:"theorem concrete_list (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p := by\n  intro σ h hstar\n  obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd', hu', hn₂, hn₃⟩ := hstar\n  subst hu'\n  subst hu\n  refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩\n  refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩\n  refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩\n  refine ⟨h₃, h₄, hd', rfl, hn₂, ?_⟩\n  refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩\n  exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩",
     solNote:"Five <code>refine</code>s and an <code>exact</code>, alternating between the two halves of one rhythm: witness-and-strip-the-<code>pure</code>, then hand-the-node-its-heap. If you climbed all four hints and are still stuck, open this and read it against the trace below — the difficulty here is bookkeeping, and bookkeeping is learned by watching it once.",
     expl:"After the <code>obtain</code> and the two <code>subst</code>s the heap is spelled out as <code>h₁.union (h₃.union h₄)</code> and never changes again; from there each <code>refine</code> fills a tuple and leaves one hole. The odd-numbered ones open a <code>cons</code>: witness the next address, split the heap as empty-plus-everything so the <code>pure</code> conjunct gets a heap it can own, prove the non-nullness from a hypothesis, and leave the remainder. The even-numbered ones split that remainder into the head node and the tail, using the disjointness the premise already supplied. The last line closes the <code>nil</code> case, where the tail is empty and the address is <code>0</code>.",
     walk:[
       {tac:'intro σ h hstar',
        h:"Turns the entailment into a fixed store, a fixed heap, and a hypothesis. Goal: <code>listRep [a, b, c] p σ h</code>."},
       {tac:"obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd', hu', hn₂, hn₃⟩ := hstar",
        h:"Eleven names for a nested pair of stars: five for the outer one (two heaps, disjointness, the union equation, the first node) and six for the inner one, flattened into the same bracket. The goal is untouched; all the change is in the context."},
       {tac:"subst hu'",
        h:"<code>subst hu'</code> replaces <code>h₂</code> by <code>h₃.union h₄</code> wherever it occurs, and deletes both. Nothing is proved; the point is that the heap in <code>hd</code> and in the goal is now written in terms of the four pieces rather than in terms of a name."},
       {tac:'subst hu',
        h:"The same for <code>h</code>. The goal becomes <code>listRep [a, b, c] p σ (h₁.union (h₃.union h₄))</code>, which is the form the cuts have to be given in, and the context stops changing for the rest of the proof."},
       {tac:'refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), disjoint_empty_left _,',
        h:"The first <code>cons</code>. <code>q</code> witnesses the existential, because the first node's next field holds <code>q</code> — that is a choice, and the wrong choice is caught two lines later. The heap is cut as <code>Heap.empty</code> beside the whole thing, which is the cut the <code>pure</code> conjunct forces: it owns nothing, so its side of the star must be empty."},
       {tac:'          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩',
        h:"The same <code>refine</code>, continued. The union equation wants <code>whole = Heap.union Heap.empty whole</code>, so <code>union_empty_left</code> is used backwards. The <code>⟨hp, rfl⟩</code> is the <code>pure</code> conjunct as a pair: the disequality from the hypothesis, and <code>Heap.empty = Heap.empty</code>. The hole is everything after the <code>pure</code>."},
       {tac:'refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩',
        h:"The second cut, and the one that does the real dividing: the head node takes <code>h₁</code> and the tail takes the rest. <code>hd</code> is the disjointness the premise handed over, and the union equation is now <code>rfl</code> — which is what the two <code>subst</code>s bought. <code>hn₁</code> is the node itself, unchanged from the premise."},
       {tac:'refine ⟨r, Heap.empty, Heap.union h₃ h₄, disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩',
        h:"The second <code>cons</code>, character for character the first with <code>r</code>, <code>h₃.union h₄</code> and <code>hq</code> substituted. The goal it acts on is <code>listRep [b, c] q σ (h₃.union h₄)</code>."},
       {tac:"refine ⟨h₃, h₄, hd', rfl, hn₂, ?_⟩",
        h:"The second node takes <code>h₃</code>, the tail takes <code>h₄</code>. Same shape as before, with the primed disjointness."},
       {tac:'refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩',
        h:"The third and last <code>cons</code>. The witness is <code>0</code>, because the third node's next field holds <code>0</code> — this is where the list is declared to end, and the remaining goal is a <code>node</code> starred with <code>listRep [] 0</code>."},
       {tac:'exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩',
        h:"The <code>nil</code> case, and the only cut in the proof that puts the empty heap on the <i>right</i>: the node keeps <code>h₄</code> and the empty list gets nothing. Seven slots for a six-slot star, because the last one is <code>listRep [] 0</code>, itself a conjunction, and the anonymous constructor flattens it — <code>0 = 0</code> and <code>Heap.empty = Heap.empty</code>, both <code>rfl</code>."}
     ],
     deep:[
       {t:'p', h:"After the two <code>subst</code>s the context is fixed for the rest of the proof, so it is worth printing once and then not again."},
       {t:'state', cap:'The state after <code>subst hu</code>, in full. From here to the last line only the goal changes; the fourteen hypothesis lines are the same at every step below.',
        src:"p : Loc\na b c : Nat\nq r : Loc\nhp : p ≠ 0\nhq : q ≠ 0\nhr : r ≠ 0\nσ : Store\nh₁ : Heap\nhn₁ : node p a q σ h₁\nh₃ h₄ : Heap\nhd' : h₃.disjoint h₄\nhn₂ : node q b r σ h₃\nhn₃ : node r c 0 σ h₄\nhd : h₁.disjoint (h₃.union h₄)\n⊢ listRep [a, b, c] p σ (h₁.union (h₃.union h₄))"},
       {t:'trace', title:'The five cuts, goal line by goal line — the fourteen context lines above are unchanged at every step and are omitted; each state below is the goal line as Lean prints it',
        start:"⊢ listRep [a, b, c] p σ (h₁.union (h₃.union h₄))",
        steps:[
          {tac:'refine ⟨q, Heap.empty, Heap.union h₁ (Heap.union h₃ h₄), …⟩',
           state:"⊢ (node p a q ∗ listRep [b, c] q) σ (h₁.union (h₃.union h₄))",
           h:"The existential and the <code>pure</code> are gone and the heap is unchanged, which is the visible sign that the first cut divided nothing."},
          {tac:'refine ⟨h₁, Heap.union h₃ h₄, hd, rfl, hn₁, ?_⟩',
           state:"⊢ listRep [b, c] q σ (h₃.union h₄)",
           h:"Now the heap has shrunk: <code>h₁</code> went to the node and what is left is the tail's. The goal is the original one with the list one shorter and the address moved to <code>q</code> — the recursion, visible."},
          {tac:'refine ⟨r, Heap.empty, Heap.union h₃ h₄, …⟩',
           state:"⊢ (node q b r ∗ listRep [c] r) σ (h₃.union h₄)",
           h:"The same first move at the second node. Same shape, smaller list."},
          {tac:"refine ⟨h₃, h₄, hd', rfl, hn₂, ?_⟩",
           state:"⊢ listRep [c] r σ h₄",
           h:"And the same second move. One node's worth of heap has come off again."},
          {tac:'refine ⟨0, Heap.empty, h₄, …⟩',
           state:"⊢ (node r c 0 ∗ listRep [] 0) σ h₄",
           h:"The last <code>cons</code>. <code>listRep [] 0</code> is <code>pure (fun _ => 0 = 0)</code>, so the remaining obligation is the third node plus an empty heap — which is what the final <code>exact</code> supplies."}
        ],
        done:'No goals.'},
       {t:'p', h:"Two things are worth reading off that column of goals. The heap shrinks only on the even steps, because only the even steps divide anything; the odd steps trade an existential and a <code>pure</code> for nothing. And the goal at step two is the goal at step zero with <code>[a, b, c]</code> replaced by <code>[b, c]</code> and <code>p</code> by <code>q</code> — the proof is one step of an induction, done three times by hand. Unit 33 does it once, by induction, and never writes a heap again."},
       {t:'detail', title:'The proof without the two substs', tag:'aside',
        blocks:[
          {t:'p', h:"The <code>subst</code>s are convenience rather than necessity, and it is worth seeing what they cost and what they buy. Skip them, keep <code>h</code>, <code>h₂</code>, <code>hu</code> and <code>hu'</code>, and every cut can be given in terms of the original names — the equation slots then take <code>hu</code> and <code>hu'</code> where the shipped proof takes <code>rfl</code>."},
          {t:'code', tag:'illustration', cap:'The same theorem, two lines shorter and one degree less readable. Compiled.',
           src:"example (p : Loc) (a b c : Nat) (q r : Loc)\n    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :\n    node p a q ∗ node q b r ∗ node r c 0 ⊢ listRep [a, b, c] p := by\n  intro σ h hstar\n  obtain ⟨h₁, h₂, hd, hu, hn₁, h₃, h₄, hd', hu', hn₂, hn₃⟩ := hstar\n  refine ⟨q, Heap.empty, h, disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩\n  refine ⟨h₁, h₂, hd, hu, hn₁, ?_⟩\n  refine ⟨r, Heap.empty, h₂, disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hq, rfl⟩, ?_⟩\n  refine ⟨h₃, h₄, hd', hu', hn₂, ?_⟩\n  refine ⟨0, Heap.empty, h₄, disjoint_empty_left _, (union_empty_left _).symm, ⟨hr, rfl⟩, ?_⟩\n  exact ⟨h₄, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₃, rfl, rfl⟩"},
          {t:'p', h:"What the <code>subst</code>s buy is the goal display: with them, the heap in every goal is written out as a union of the pieces you are holding, so the next cut can be read off the screen. Without them the goal says <code>h</code>, and which pieces <code>h</code> is made of has to be carried in your head. That is the argument for doing it, and it is an argument about the goal state rather than about the proof term."}
        ]}
     ],
     pitfall:"Cutting the first star the wrong way round. The <code>pure</code> conjunct is on the <i>left</i> of the star, so its heap is the <i>first</i> component of the tuple, and it must be empty. Writing <code>⟨q, Heap.union h₁ (Heap.union h₃ h₄), Heap.empty, …⟩</code> puts the whole heap where the <code>pure</code> lives, and three errors arrive together, one for every slot of that <code>refine</code> that mentions a heap. The first is the disjointness — <code>Application type mismatch: The argument disjoint_empty_left ?m.116 has type Heap.empty.disjoint ?m.116 but is expected to have type (h₁.union (h₃.union h₄)).disjoint Heap.empty</code> — and it reads like a complaint about argument order, which is the wrong diagnosis. The one to read is the second: <code>Application type mismatch: The argument rfl has type ?m.129 = ?m.129 but is expected to have type emp σ (h₁.union (h₃.union h₄))</code>. Take that literally — you have promised that the whole heap is empty.",
     variants:"Witness the first existential with <code>r</code> instead of <code>q</code> and the error arrives one line later, at the node, heading a cascade of three: <code>Application type mismatch: The argument hn₁ has type node p a q σ h₁ but is expected to have type node p a r σ h₁</code>. Only that one is a mistake; the other two are the same substitution echoing down the chain, because a tail that starts at <code>r</code> then wants <code>r ≠ 0</code> where <code>hq</code> was handed over and <code>node r b _</code> where <code>hn₂</code> was. The witness is checked against the node you hand over, not against the heap, so a wrong address is caught precisely and late. · Drop the <code>.symm</code> from each <code>(union_empty_left _).symm</code>, or put a bare <code>rfl</code> in all three of those slots, and the proof still compiles — <code>Heap.union Heap.empty h</code> reduces to <code>h</code>, as Unit 15 found, so all three spellings typecheck. The mirror is not so forgiving: replace the final line's <code>(union_empty_right _).symm</code> by <code>rfl</code> and you get <code>Application type mismatch: The argument rfl has type ?m.212 = ?m.212 but is expected to have type h₄ = h₄.union Heap.empty</code>. The left-hand cuts are free and the right-hand one is not, and this proof uses three of the first kind and one of the second. · Drop <code>hq</code> from the hypotheses and exactly one obligation is left open, at the second <code>cons</code>: <code>⊢ fact (fun x =&gt; q ≠ 0) σ Heap.empty</code>. Nothing in the premise supplies it — <code>node q b r</code> says <code>q</code> and <code>q + 1</code> hold values, and address <code>0</code> is allowed to hold a value like any other. All three disequalities are genuinely needed, one per node, and the premise asserts none of them."
    },

    /* ============================================ why there is no program ==== */

    {t:'sec', s:'No program on this page'},

    {t:'p', h:"There is no command in this unit, no derivation and no triple. That is not because the material would not fit; it is because the language of Unit 18 cannot walk one of these structures, and the reason is one constructor's type."},

    {t:'code', tag:'sketch', cap:'What a traversal needs, and what the syntax offers. <code>Cmd.load</code> takes a <code>Loc</code> — a literal address, fixed when the program is written — and there is no way to say &ldquo;load from the address currently held in <code>cur</code>, plus one&rdquo;.',
     src:"def walkStep (cur : Var) : Cmd :=\n  .load cur (.plus (.var cur) (.const 1))"},

    {t:'state', cap:'Lean reports it through the leading-dot notation, which resolves a constructor against the expected type. The expected type here is <code>Loc</code>, so it tries <code>Loc.plus</code> and then, unfolding the abbreviation, <code>Nat.plus</code>; neither exists, and it says so twice. The message is a statement about which type the slot wants.',
     src:"error(lean.unknownIdentifier): Unknown constant `Loc.plus`\n\nNote: Inferred this name from the expected resulting type of `.plus`:\n  Loc\nerror(lean.unknownIdentifier): Unknown constant `Nat.plus`\n\nNote: Inferred this name from the expected resulting type of `.plus`:\n  Loc"},

    {t:'p', h:"Unit 18 chose that on purpose and priced it there: an address that is an expression is a store-dependent address, and every rule, every frame and every locality proof would have to carry one. The cost lands here. A command can read and write any address that was written into the program text, so a three-node list at addresses fixed in advance is within reach; what no command can do is take the value it has read out of a next field and use it as an address. Following a pointer is the one operation the syntax withholds, and it is the operation every list algorithm is made of. Unit 38 gives the one-line change to <code>Cmd</code> that removes the limitation, and the argument that everything proved in between survives it, because no theorem in the development ever inspects how an address was arrived at."},

    {t:'p', h:"What this page produces instead is the thing a program logic consumes. <code>listRep xs p</code> is an assertion like <code>l ↦ v</code>: it can sit in a precondition, in a postcondition, or as the frame <code>R</code> of Unit 27's rule. Framing it hands an entire unbounded data structure across a command in one symbol, and the frame rule's proof does not care that the symbol stands for two cells per entry of <code>xs</code> rather than one cell in total. That is the whole of what recursive predicates buy, and it is why every data structure in this subject is defined the way this one is."},

    /* ========================================================== closing ==== */

    {t:'dod', h:"You can say why an assertion written by hand cannot describe a list of unknown length; define an <code>Assertion</code>-valued function by structural recursion on a <code>List</code> and read its <code>cons</code> case aloud; unfold a concrete <code>listRep</code> into the chain it abbreviates; say what the <code>∗</code>s guarantee and what the <code>pure</code> conjuncts guarantee, and produce the heap that shows the null pointer is not a one-element list; state and prove the three fold/unfold identities and say why they are worth naming; derive a node's two addresses are distinct from ownership rather than from arithmetic; and assemble a three-node list by choosing five cuts, knowing before you start which of them divide anything."},

    {t:'p', h:"A predicate for a <i>complete</i> list. A traversal splits a list into the part already visited and the part remaining, and neither of those is a complete list."}

  ]
});
