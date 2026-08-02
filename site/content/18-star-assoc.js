registerChapter({
  id: 'star-assoc',
  num: '16',
  ledgerForward: ['star_swap_middle'],
  ledgerAllow: ['star_assoc'],
  phase:'Phase 2 · The logic of ownership',
  title: 'Associativity',
  blurb: 'One theorem, both directions: the law that turns a tree of stars into a list of owned resources, and the only proof on which all the work is disjointness bookkeeping.',

  orient: {
    youWill: [
      'Draw the re-bracketing of a three-way split and say which heaps move (none) and which names appear and disappear (one each).',
      'Take apart a star whose left conjunct is itself a star, in one <code>intro</code> pattern with a six-slot tuple inside slot five.',
      'Delete an intermediate heap with <code>subst</code> before building anything, and say why that leaves the goal untouched.',
      'Say which pairwise disjointness facts you are handed, which ones the goal wants, and why those are two different lists.',
      'Extract two facts with <code>disjoint_union_left.mp</code> and build a third with <code>disjoint_union_right.mpr</code>, and read <code>left</code> and <code>right</code> as naming a side of <code>Heap.disjoint</code> rather than a side of the goal.',
      'Discharge the heap equation with <code>union_assoc</code>, which carries no hypothesis, and see that nothing else on the page is about unions at all.',
      'Prove the mirror direction and predict, before writing it, which two lemma names exchange places.',
      'Say which of the five laws of the completed monoid is the one that does not generalise to an arbitrary partial commutative monoid, and point at the two places in the proof that are the reason.'
    ],
    needs: [
      'Unit 14: the definition of <code>∗</code>, the six-slot <code>⟨…⟩</code> and the six-name <code>intro</code> pattern.',
      'Unit 11: <code>splits_assoc</code> — this theorem with the assertions removed, proved line for line.',
      'Unit 10: <code>union_assoc</code>, and the two bridges <code>disjoint_union_left</code> and <code>disjoint_union_right</code>. Unit 08: <code>subst</code>.',
      'Unit 15: the four laws proved there, and the fact that exactly one was left over.'
    ],
    payoff: 'From here on a star of four assertions is a list and not a tree, and you may re-bracket it silently. Unit 17 builds <code>star_swap_middle</code> out of this theorem and <code>star_comm</code> with no <code>intro</code> in it, and that composition style is what carries the inductive steps of Unit 33\'s two list theorems without a heap in sight.'
  },

  blocks: [

    /* ==================================================== the missing law === */

    {t:'p', h:'That law is associativity, and Unit 11 did the work under a different name. <code>splits_assoc</code> is this theorem with every trace of assertions removed: three heaps, two ways of bracketing them, and an existential witness for the piece that has to be built.'},

    {t:'cmp',
     left: {t:'Unit 11, about heaps', src:'theorem splits_assoc {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by'},
     right:{t:'Unit 16, about assertions', src:'theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by'}},

    {t:'p', h:'The left statement names its five heaps and quantifies the witness explicitly. The right one names none of them: the heaps arrive from the <code>intro</code> pattern and the witness is the second slot of the tuple you build, because that is where the definition of <code>∗</code> put its existential. Same five heaps, same witness, different packaging. The packaging is what this page has to teach you to handle; the argument inside it is Unit 11\'s, and all of it is about disjointness.'},

    {t:'p', h:'What the law buys is already in the notation. <code>infixr:55</code> makes <code>P ∗ Q ∗ R</code> parse as <code>P ∗ (Q ∗ R)</code>, and Lean prints it back that way, without brackets — which is only honest if the brackets do not matter. Unit 14 made that bet before it could be paid. This unit pays it: afterwards a precondition is a <i>list</i> of things you own, and you may regroup it without saying so.'},

    /* ====================================================== the picture === */

    {t:'sec', s:'What moves when you re-bracket'},

    {t:'p', h:'Before any Lean, draw it. The heap <code>h</code> is cut into three pieces. The left bracketing glues the first two together first and calls the result <code>hPQ</code>; the right bracketing glues the last two together first and calls the result <code>hQR</code>.'},

    {t:'txt', cap:'The same three pieces of the same heap, grouped two ways. The pieces do not move; the intermediate name does.',
     src:'        (P ∗ Q) ∗ R                        P ∗ (Q ∗ R)\n\n     ┌─────┬─────┬─────┐                ┌─────┬─────┬─────┐\n     │ hP  │ hQ  │ hR  │                │ hP  │ hQ  │ hR  │\n     └─────┴─────┴─────┘                └─────┴─────┴─────┘\n     └─── hPQ ───┘                            └─── hQR ───┘\n\n     hPQ = hP.union hQ                  hQR = hQ.union hR\n       h = hPQ.union hR                   h = hP.union hQR'},

    {t:'p', h:'Nothing moves. <code>hP</code>, <code>hQ</code> and <code>hR</code> are the same three heaps on both sides, and <code>h</code> is the same heap. One name disappears and one name appears. That is the whole geometric content, and it is why exactly one union lemma is spent in the proof, and why that lemma is <code>union_assoc</code>.'},

    {t:'p', h:'The bookkeeping is not symmetric with the picture. There are three pairwise disjointness facts available about three pieces — <code>hP</code> against <code>hQ</code>, <code>hP</code> against <code>hR</code>, <code>hQ</code> against <code>hR</code> — and the two bracketings bundle them differently. The left one hands you <code>hP</code>-against-<code>hQ</code> loose and the other two glued into a single fact about <code>hP.union hQ</code>. The right one wants <code>hQ</code>-against-<code>hR</code> loose and the other two glued into a single fact about <code>hQ.union hR</code>. Neither bundle is the other, and neither is a projection of the other. Taking the first apart and building the second is the proof.'},

    /* ===================================================== the statement === */

    {t:'sec', s:'The statement, twice'},

    {t:'code', tag:'sketch', cap:'Statements only — each is followed in the corpus by its proof, and a bare <code>:= by</code> reports <code>unsolved goals</code>.',
     src:'theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by'},

    {t:'p', h:'Two theorems, because <code>⊢</code> is a one-way implication and neither direction follows from the other. Commutativity got away with one theorem: its converse is itself with <code>P</code> and <code>Q</code> exchanged. Associativity has no such trick — exchanging the names in <code>star_assoc_left</code> gives you <code>star_assoc_left</code> again with different letters, never the other direction. The pair is packaged as a single <code>⊣⊢</code> in <code>x37</code>, and there is no theorem in this course called <code>star_assoc</code>: you cite one of the two by name and you get the direction right, or the type mismatch tells you which one you wanted.'},

    /* ============================================== the nested intro pattern === */

    {t:'sec', s:'Taking apart a star whose conjunct is a star'},

    {t:'p', h:'Unit 14\'s six-name pattern still applies to the outer star of <code>(P ∗ Q) ∗ R</code>: two heaps, a disjointness fact, an equation, and the two ownership facts. What is different is the fifth slot, which holds <code>(P ∗ Q) σ hPQ</code> — itself a star.'},

    {t:'code', tag:'sketch', cap:'One tactic line rather than a proof, so it does not compile on its own: the outer star opened with Unit 14\'s pattern, and the inner one left folded. The trace below is what it leaves.',
     src:'  intro σ h ⟨hPQ, hR, hd₁, hu₁, hpq, hr⟩'},

    {t:'trace', title:'What the outer pattern leaves',
     start:'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R',
     steps:[
       {tac:'intro σ h ⟨hPQ, hR, hd₁, hu₁, hpq, hr⟩',
        state:'P Q R : Assertion\nσ : Store\nh hPQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhu₁ : h = hPQ.union hR\nhpq : (P ∗ Q) σ hPQ\nhr : R σ hR\n⊢ (P ∗ Q ∗ R) σ h',
        h:'Three binders come out of the entailment and the six-name pattern takes the star apart. <code>hpq</code> is a star, folded, at the heap <code>hPQ</code> — and <code>hPQ</code> is a bare variable, about which nothing is known except <code>hd₁</code> and <code>hu₁</code>. The goal prints its right-nested star without brackets: <code>P ∗ Q ∗ R</code> is <code>P ∗ (Q ∗ R)</code>.'}
     ]},

    {t:'p', h:'<code>hpq</code> has to be opened before anything can be done with it, and there are two spellings. <code>obtain ⟨hP, hQ, hd₂, hu₂, hp, hq⟩ := hpq</code> is one extra line. Or the pattern goes in where the name would have been, and the whole thing happens in the <code>intro</code>. The corpus takes the second.'},

    {t:'code', tag:'verified', cap:'One pattern, eleven names, a six-slot tuple inside slot five.',
     src:'  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩'},

    {t:'p', h:'Eleven names for eleven things: the store <code>σ</code>; the heap <code>h</code> the entailment is evaluated at; the outer cut <code>hPQ</code>, <code>hR</code> with its disjointness <code>hd₁</code> and its equation <code>hu₁</code>; the inner cut <code>hP</code>, <code>hQ</code> with <code>hd₂</code> and <code>hu₂</code>; and the three ownership facts <code>hp</code>, <code>hq</code>, <code>hr</code>. Nesting is not decoration here — flattening the tuple all the way to eleven names does not compile, and the error names a type you never wrote. That is <code>m4-4</code>\'s first trap.'},

    {t:'p', h:'That pattern is the only piece of Lean this unit adds. Every tactic and every lemma in the proof below is one you have already used, which is the honest report: what makes this the hardest proof about <code>∗</code> in the course is not its syntax.'},

    /* ========================================================= subst === */

    {t:'sec', s:'Deleting the middle heap first'},

    {t:'p', h:'<code>hPQ</code> is a variable for which you now have a formula: <code>hu₂ : hPQ = hP.union hQ</code>. Nothing in the goal mentions it — the goal is <code>(P ∗ Q ∗ R) σ h</code>, whose only heap is <code>h</code>. Two hypotheses mention it, <code>hd₁</code> and <code>hu₁</code>. So the variable is carrying no information that the formula does not, and it can go.'},

    {t:'code', tag:'verified', cap:'The second line of the proof.', src:'  subst hu₂'},

    {t:'p', h:'<code>hPQ</code> and <code>hu₂</code> both vanish from the context, and the two hypotheses that mentioned <code>hPQ</code> are restated in terms of <code>hP</code> and <code>hQ</code>: <code>hd₁</code> becomes <code>(hP.union hQ).disjoint hR</code> and <code>hu₁</code> becomes <code>h = (hP.union hQ).union hR</code>. The goal is character for character what it was, because <code>hPQ</code> never occurred in it. Eliminating a variable can only cost you something if what you are proving mentions it; this one does not, so the move is free.'},

    {t:'p', h:'Doing it first is what makes the next line possible at all. <code>disjoint_union_left</code> is a statement about <code>Heap.disjoint (Heap.union h₁ h₂) h₃</code>, so to use it on <code>hd₁</code> Lean has to see a union in the first argument of <code>Heap.disjoint</code>. Before the <code>subst</code> it sees the variable <code>hPQ</code>, and all it can report is the pattern it failed to match. <code>m4-4</code>\'s <b>pitfall</b> has that message.'},

    {t:'detail', title:'The whole context, before and after `subst`', open:false, blocks:[
      {t:'p', h:'Twelve lines and ten, which is why they are folded rather than in the running argument. The first is what the nested <code>intro</code> pattern leaves.'},
      {t:'state', cap:'After <code>intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩</code>.',
       src:'P Q R : Assertion\nσ : Store\nh hPQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhu₁ : h = hPQ.union hR\nhP hQ : Heap\nhd₂ : hP.disjoint hQ\nhu₂ : hPQ = hP.union hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\n⊢ (P ∗ Q ∗ R) σ h'},
      {t:'p', h:'And this is the same context one tactic later. Two entries are gone, two are rewritten, the order has changed because <code>subst</code> reinserts the rewritten hypotheses at the end, and the goal is untouched.'},
      {t:'state', cap:'After <code>subst hu₂</code>.',
       src:'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\n⊢ (P ∗ Q ∗ R) σ h'},
      {t:'p', h:'The alternative is to rewrite instead of substituting. <code>rw [hu₂] at hd₁ hu₁</code> produces the same two hypotheses and compiles; the difference is that <code>hPQ</code> and <code>hu₂</code> stay in the context afterwards, unused, and every goal state for the rest of the proof is two lines longer. Nothing else in the proof changes.'},
      {t:'code', tag:'illustration', cap:'The same theorem with <code>rw … at</code> in place of <code>subst</code>. Compiled.',
       src:'example (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩\n  rw [hu₂] at hd₁ hu₁\n  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁\n  refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩\n  · rw [hu₁, union_assoc]\n  · exact ⟨hQ, hR, hQR, rfl, hq, hr⟩'}
    ]},

    /* =================================================== the disjointness === */

    {t:'sec', s:'The disjointness you have, and the disjointness you need'},

    {t:'p', h:'Two facts are in the context and two are wanted, and no two of the four are the same statement.'},

    {t:'tbl', cap:'Every remaining difficulty in the proof is in this table. The heap equation is one lemma; this is the rest.',
     head:['', 'the fact'],
     rows:[
       ['in hand, loose', '<code>hd₂ : hP.disjoint hQ</code>'],
       ['in hand, glued', '<code>hd₁ : (hP.union hQ).disjoint hR</code>'],
       ['wanted by the outer star', '<code>hP.disjoint (hQ.union hR)</code>'],
       ['wanted by the inner star', '<code>hQ.disjoint hR</code>']
     ]},

    {t:'p', h:'Unit 10 proved the two lemmas that convert between glued and loose, and both are stated as <code>↔</code>, so each works in both directions. Their names say <i>which argument of <code>Heap.disjoint</code> the union sits in</i>, and nothing else. <code>disjoint_union_left</code> is about <code>Heap.disjoint (Heap.union h₁ h₂) h₃</code>; <code>disjoint_union_right</code> is about <code>Heap.disjoint h₁ (Heap.union h₂ h₃)</code>. Neither name refers to which side of the entailment you are on, or to which half of the picture you are building. The mirror proof uses the same two lemmas with their roles exchanged, and it is that naming rule and nothing else that decides which one goes where.'},

    {t:'p', h:'So: <code>hd₁</code> has its union on the left, and you want it taken apart, so it is <code>disjoint_union_left</code> in the <code>.mp</code> direction.'},

    {t:'code', tag:'verified', cap:'The third line. It splits one glued fact into the two loose ones underneath it.',
     src:'  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁'},

    {t:'p', h:'That produces <code>hPR : hP.disjoint hR</code> and <code>hQR : hQ.disjoint hR</code>. The second is the inner star\'s requirement, exactly. The first is half of the outer star\'s requirement; the other half is <code>hd₂</code>, which you have had since the <code>intro</code>. The outer requirement has its union on the right, and you are building it rather than taking it apart, so it is <code>disjoint_union_right</code> in the <code>.mpr</code> direction, applied to a pair of those two facts. Which of the two goes first in the pair is decided by the statement, not by the picture, and getting it backwards is the error <code>m4-4</code>\'s <b>pitfall</b> quotes.'},

    /* ====================================================== the equation === */

    {t:'sec', s:'The equation slot costs one lemma and no hypothesis'},

    {t:'p', h:'The fourth slot of the tuple you are building is <code>h = hP.union (hQ.union hR)</code>. You have <code>hu₁ : h = (hP.union hQ).union hR</code>. Rewriting with <code>hu₁</code> replaces <code>h</code> and leaves an equation between two heaps with the same three pieces in the same order and different brackets.'},

    {t:'code', tag:'illustration', cap:'That equation, on its own, with the proof it takes.',
     src:'example (hP hQ hR : Heap) :\n    Heap.union (Heap.union hP hQ) hR = Heap.union hP (Heap.union hQ hR) :=\n  union_assoc hP hQ hR'},

    {t:'p', h:'<code>union_assoc</code> takes three heaps and no hypothesis. Unit 10 proved it that way deliberately — the equation holds whether or not the heaps overlap, because a left-biased union has a definite answer at every address either way, and the two bracketings compute the same answer. So this slot generates nothing to discharge: no disjointness side condition hiding in it, no obligation left behind. Every difficulty on this page is in the four-row table above, and that is the honest summary of the unit: associativity of <code>∗</code> is disjointness bookkeeping with one rewrite attached.'},

    {t:'p', h:'The inner star\'s equation is cheaper still. You choose the witness for the second slot, and the picture chose it for you: <code>Heap.union hQ hR</code>. Its own equation is then <code>Heap.union hQ hR = Heap.union hQ hR</code>, and <code>rfl</code> fills it.'},

    /* ===================================================== what is left === */

    {t:'sec', s:'What is left'},

    {t:'p', h:'Three lines are on the page: the <code>intro</code>, the <code>subst</code>, the <code>obtain</code>. What remains is one tuple with six slots, and the picture has already chosen the two heaps that go in the first two.'},

    {t:'tbl', cap:'The six slots of <code>(P ∗ (Q ∗ R)) σ h</code> once the two witnesses are fixed. Only slot 5 is already in your hands under its own name.',
     head:['slot', 'what must go there'],
     rows:[
       ['1 · first heap', '<code>hP</code>'],
       ['2 · second heap', '<code>Heap.union hQ hR</code> — the piece the picture builds'],
       ['3 · disjointness', '<code>hP.disjoint (hQ.union hR)</code>'],
       ['4 · the equation', '<code>h = hP.union (hQ.union hR)</code>'],
       ['5 · the left conjunct', '<code>P σ hP</code>'],
       ['6 · the right conjunct', '<code>(Q ∗ R) σ (hQ.union hR)</code> — itself a six-slot tuple']
     ]},

    {t:'p', h:'Slot 3 is one application of a bridge lemma, short enough to write where it stands. Slots 4 and 6 are not, so they go in as <code>?_</code> and are proved afterwards — which is what <code>refine</code> is for, and Unit 10 introduced it on <code>disjoint_union_left</code> for the same reason. Then the mirror, where the picture is read right to left and two lemma names exchange places.'},

    /* ====================================================== exercise m4-4 === */

    {t:'ex',
     id: 'm4-4',
     name: 'star_assoc_left / star_assoc_right',
     hard: true,

     why: 'This is the hardest proof about <code>∗</code> alone in the course, and no later one asks you to take two nested stars apart and hand the pieces back regrouped. Later proofs do still name heaps; what they stop doing is re-bracketing by hand. Unit 17 builds <code>star_swap_middle</code> out of these two theorems and <code>star_comm</code> without writing a single <code>intro</code>, and the inductive step of each of Unit 33\'s two list theorems is a chain of <code>entails_trans</code> with <code>star_assoc_left</code> in it twice and no heap named anywhere. Both directions are cited by name later — <code>star_assoc_right</code> opens <code>star_swap_middle</code> and <code>star_assoc_left</code> closes it — and after this page <code>star_assoc_left</code> is used seven more times in the corpus and <code>star_assoc_right</code> twice.',

     setup: 'You have <code>subst</code> (Unit 08), <code>disjoint_union_left</code> and <code>disjoint_union_right</code> as <code>↔</code>s (Unit 10), <code>union_assoc</code> (Unit 10), and <code>refine</code> with <code>?_</code> holes (Unit 10). No lemma about <code>∗</code> is needed, and none of Unit 15\'s laws is used. Write both directions; the second is not the first with the letters permuted.',

     goal: 'theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n  sorry\n\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by',

     hints: [
       'Unfolded, <code>star_assoc_left</code> says: for every store and every heap <code>h</code>, if <code>h</code> splits into two pieces with <code>P ∗ Q</code> on the first and <code>R</code> on the second, and that first piece splits again into pieces carrying <code>P</code> and <code>Q</code>, then <code>h</code> splits into two pieces carrying <code>P</code> and <code>Q ∗ R</code>. Five heaps are involved and three of them are the leaves. <code>star_assoc_right</code> says the same sentence with the two splittings interchanged: the second piece is the one that splits again, and the piece you must build is the first.',
       'Nothing moves. The three leaf heaps you are handed are the three you hand back; the only thing that changes is which two of them get glued together first, and glueing is <code>Heap.union</code>, which is associative unconditionally. What is not unconditional is disjointness: you are handed one pairwise fact loose and two of them glued into a single statement about a union, and the goal wants a different one loose and the other two glued the other way. Take the bundle apart, then build the other bundle.',
       'One <code>intro</code> whose pattern has a six-slot tuple nested inside it. Then <code>subst</code> on the inner equation. Then <code>disjoint_union_left</code> or <code>disjoint_union_right</code> in the <code>.mp</code> direction to take the glued fact apart, and the other one in the <code>.mpr</code> direction to build the new one — the names refer to the side of <code>Heap.disjoint</code> the union is on. Then <code>refine</code> with holes for the disjointness-free slots, <code>union_assoc</code> for the equation, and a six-slot <code>⟨…⟩</code> for the conjunct that is itself a star.',
       'For the forward direction start <code>intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩</code> and then <code>subst hu₂</code>. That leaves a context with <code>hd₂ : hP.disjoint hQ</code>, <code>hd₁ : (hP.union hQ).disjoint hR</code>, <code>hu₁ : h = (hP.union hQ).union hR</code> and the three ownership facts, against the goal <code>(P ∗ Q ∗ R) σ h</code>. Next line: <code>obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁</code>. Then the tuple, with <code>Heap.union hQ hR</code> as the second witness, <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code> as the third slot, and holes for the equation and the inner star. For the mirror, the nested tuple moves to the last slot of the pattern and the two lemma names swap.'
     ],

     sol: 'theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩\n  subst hu₂\n  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁\n  refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩\n  · rw [hu₁, union_assoc]\n  · exact ⟨hQ, hR, hQR, rfl, hq, hr⟩\n\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by\n  intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩\n  subst hu₂\n  obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁\n  refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩\n  rw [hu₁, union_assoc]',

     solNote: 'The forward proof needs two holes and the mirror needs one: in the mirror the conjunct that is a star sits in slot five, where the witnesses are already fixed, so its tuple can be written inline. If you climbed all four hints and are still stuck, open this without regret — the arrangement here is the kind of thing that is obvious once seen and invisible before.',

     expl: 'Both proofs are four moves: open both stars in one pattern, delete the intermediate heap, convert the glued disjointness fact into the one the goal wants, and hand back the three leaf heaps regrouped. The only heap lemma is <code>union_assoc</code>, and it carries no hypothesis, so all of the reasoning is about disjointness and none of it is about unions.',

     walk: [
       {tac:'theorem star_assoc_left …', h:'Three assertion variables and one entailment. The heaps are not named in the statement; they arrive from the pattern.'},
       {tac:'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩', h:'Strips the three binders of the entailment and takes both stars apart at once. Slot five of the outer six is <code>(P ∗ Q) σ hPQ</code>, so a six-slot pattern goes there instead of a name. Eleven names, one goal: <code>(P ∗ Q ∗ R) σ h</code>.'},
       {tac:'subst hu₂', h:'Eliminates the variable <code>hPQ</code> in favour of <code>hP.union hQ</code>. <code>hd₁</code> and <code>hu₁</code> are re-typed; the goal is untouched, because <code>hPQ</code> never occurred in it.'},
       {tac:'obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁', h:'Turns the one glued fact <code>(hP.union hQ).disjoint hR</code> into the two loose facts under it. <code>hQR</code> is what the inner star of the goal wants; <code>hPR</code> is half of what the outer star wants.'},
       {tac:'refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩', h:'Commits to the cut: <code>hP</code> and the heap the picture builds. The third slot glues <code>hd₂</code> and <code>hPR</code> into <code>hP.disjoint (hQ.union hR)</code> — the <code>.mpr</code> direction, because this fact is being <i>made</i>. Slot five is <code>hp</code> unchanged. Two holes remain.'},
       {tac:'· rw [hu₁, union_assoc]', h:'The first hole is <code>h = hP.union (hQ.union hR)</code>. <code>hu₁</code> replaces <code>h</code> by <code>(hP.union hQ).union hR</code>; <code>union_assoc</code> then rewrites that to the right-nested form and <code>rw</code>\'s trailing <code>rfl</code> closes it.'},
       {tac:'· exact ⟨hQ, hR, hQR, rfl, hq, hr⟩', h:'The second hole is <code>(Q ∗ R) σ (hQ.union hR)</code>. Its cut is <code>hQ</code> and <code>hR</code>, so its equation is <code>Heap.union hQ hR = Heap.union hQ hR</code> and <code>rfl</code> fills it. The remaining four slots are hypotheses under their own names.'},
       {tac:'theorem star_assoc_right …', h:'The mirror. Same three assertions, entailment reversed.'},
       {tac:'intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩', h:'The nested tuple moves from slot five to slot six, because it is now the <i>right</i> conjunct that is a star. Eleven names again, and <code>hu₂ : hQR = hQ.union hR</code>.'},
       {tac:'subst hu₂', h:'Identical move, different variable: <code>hQR</code> goes, and <code>hd₁</code>, <code>hu₁</code> are restated over <code>hQ.union hR</code>.'},
       {tac:'obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁', h:'First swap. The glued fact now has its union on the <i>right</i> of <code>Heap.disjoint</code>, so the other lemma takes it apart, yielding <code>hP.disjoint hQ</code> and <code>hP.disjoint hR</code>.'},
       {tac:'refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩', h:'Second swap: the fact being built has its union on the left, so <code>disjoint_union_left.mpr</code> makes it, out of <code>hPR</code> and <code>hd₂</code>. The star-valued conjunct is slot five and its witnesses are already fixed, so it goes in inline and only one hole is left.'},
       {tac:'rw [hu₁, union_assoc]', h:'The single hole is <code>h = (hP.union hQ).union hR</code>. The line is character for character the forward direction\'s, but it does something different: after <code>hu₁</code> the goal is <code>hP.union (hQ.union hR) = (hP.union hQ).union hR</code>, and <code>union_assoc</code> now fires on the <i>right</i>-hand side, because that is where the left-nested union has ended up.'}
     ],

     deep: [
       {t:'trace', title:'star_assoc_left, tactic by tactic',
        start:'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R',
        steps:[
          {tac:'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩',
           state:'P Q R : Assertion\nσ : Store\nh hPQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhu₁ : h = hPQ.union hR\nhP hQ : Heap\nhd₂ : hP.disjoint hQ\nhu₂ : hPQ = hP.union hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\n⊢ (P ∗ Q ∗ R) σ h',
           h:'Everything the premise has to give, in one line. Two equations, about different heaps: <code>hu₁</code> about <code>h</code>, <code>hu₂</code> about <code>hPQ</code>.'},
          {tac:'subst hu₂',
           state:'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\n⊢ (P ∗ Q ∗ R) σ h',
           h:'<code>hPQ</code> and <code>hu₂</code> are gone; <code>hd₁</code> and <code>hu₁</code> reappear at the end of the context, rewritten. The goal did not change.'},
          {tac:'obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁',
           state:'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (P ∗ Q ∗ R) σ h',
           h:'All three pairwise disjointness facts are now in the context loose: <code>hd₂</code>, <code>hPR</code>, <code>hQR</code>. <code>hd₁</code> stays and is not used again.'},
          {tac:'refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩',
           state:'case refine_1\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ h = hP.union (hQ.union hR)\n\ncase refine_2\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (Q ∗ R) σ (hQ.union hR)',
           h:'Two goals with identical contexts and different conclusions — printed in full because the pair is the picture: the equation and the new bracket, and nothing else left to do.'},
          {tac:'· rw [hu₁, union_assoc]',
           state:'case refine_2\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (Q ∗ R) σ (hQ.union hR)',
           h:'The first hole closes on <code>rw</code>\'s trailing <code>rfl</code> and only the second goal is left.'},
          {tac:'· exact ⟨hQ, hR, hQR, rfl, hq, hr⟩',
           h:'The inner star, built directly. Four of its six slots are names already in scope.'}
        ],
        done:'No goals.'},

       {t:'detail', title:'The equation goal, halfway through its rewrite', open:false, blocks:[
         {t:'p', h:'<code>rw [hu₁, union_assoc]</code> is two rewrites and a silent <code>rfl</code>. Here is <code>case refine_1</code> after the first of them alone. The heap <code>h</code> has gone from the conclusion and what is left is <code>union_assoc</code> with its three arguments written out — which is why the second entry closes the goal.'},
         {t:'state', cap:'From <code>· rw [hu₁]</code> followed by <code>trace_state</code>, inside the focus dot.',
          src:'case refine_1\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (hP.union hQ).union hR = hP.union (hQ.union hR)'}
       ]},

       {t:'steps', title:'Each obligation, and where it is in the picture', items:[
         {k:'slot 2 · the witness', h:'<code>Heap.union hQ hR</code> is the bracket drawn on the right-hand side of the diagram. It is the only thing in the proof that is <i>constructed</i> rather than found, and choosing it is choosing where to cut.'},
         {k:'slot 3 · the outer disjointness', h:'<code>hP.disjoint (hQ.union hR)</code> — the left cell of the picture against the new bracket. Two loose facts glued: <code>hd₂</code> for <code>hQ</code>, <code>hPR</code> for <code>hR</code>.'},
         {k:'refine_1 · the equation', h:'<code>h = hP.union (hQ.union hR)</code> — the claim that the right-hand picture really is the same heap <code>h</code>. It is the left-hand picture composed with <code>union_assoc</code>, and neither half of that carries a hypothesis.'},
         {k:'refine_2 · the new bracket', h:'<code>(Q ∗ R) σ (hQ.union hR)</code> — the right-hand bracket, asserted to satisfy <code>Q ∗ R</code>. Its own cut is the two cells it was built from, so its equation is <code>rfl</code> and its disjointness is <code>hQR</code>.'}
       ]},

       {t:'cmp', cap:'The <code>obtain</code> line in each direction. One lemma name swaps, and the pair of names it binds swaps with it.',
        left: {t:'star_assoc_left', src:'  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁'},
        right:{t:'star_assoc_right', src:'  obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁'}},

       {t:'p', h:'And in the tuple: <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code> becomes <code>disjoint_union_left.mpr ⟨hPR, hd₂⟩</code>. The <code>.mp</code> lemma and the <code>.mpr</code> lemma exchange names, and the pair handed to the <code>.mpr</code> exchanges order — because in one direction the union being built is the second argument of <code>Heap.disjoint</code> and in the other it is the first, and the two conjuncts of the bridge are listed in the order the union lists its pieces.'},

       {t:'detail', title:'star_assoc_right, tactic by tactic', open:false, blocks:[
         {t:'p', h:'Folded because it is the same four moves against contexts of the same length, and the value is in three places only: the <code>intro</code> pattern\'s nesting has moved to the last slot, the <code>refine</code> leaves <i>one</i> goal rather than two, and the final <code>rw</code> — character for character the forward direction\'s — meets a mirrored equation.'},
         {t:'trace', title:'The mirror',
          start:'P Q R : Assertion\n⊢ P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R',
          steps:[
            {tac:'intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩',
             state:'P Q R : Assertion\nσ : Store\nh hP hQR : Heap\nhd₁ : hP.disjoint hQR\nhu₁ : h = hP.union hQR\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhu₂ : hQR = hQ.union hR\nhq : Q σ hQ\nhr : R σ hR\n⊢ ((P ∗ Q) ∗ R) σ h',
             h:'The unopened heap is now <code>hQR</code>, and it is the <i>second</i> of the outer cut, so <code>hd₁</code> reads <code>hP.disjoint hQR</code> — union on the right of <code>Heap.disjoint</code> once <code>hu₂</code> is spent. Compare the forward direction, where it read <code>hPQ.disjoint hR</code>. That one difference decides both lemma names below.'},
            {tac:'subst hu₂',
             state:'P Q R : Assertion\nσ : Store\nh hP : Heap\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : hP.disjoint (hQ.union hR)\nhu₁ : h = hP.union (hQ.union hR)\n⊢ ((P ∗ Q) ∗ R) σ h',
             h:'<code>hQR</code> goes; <code>hd₁</code> and <code>hu₁</code> come back rewritten and last. The goal is untouched for the same reason as before — <code>hQR</code> never occurred in it.'},
            {tac:'obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁',
             state:'P Q R : Assertion\nσ : Store\nh hP : Heap\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : hP.disjoint (hQ.union hR)\nhu₁ : h = hP.union (hQ.union hR)\nhPQ : hP.disjoint hQ\nhPR : hP.disjoint hR\n⊢ ((P ∗ Q) ∗ R) σ h',
             h:'Both new facts are about <code>hP</code>, because <code>hP</code> is the argument that was <i>not</i> a union; in the forward direction both were about <code>hR</code> for the same reason. <code>hPQ</code> is what the inner star of the goal wants and <code>hPR</code> is half of what the outer one wants — the same division of labour as the forward direction, where <code>hQR</code> and <code>hPR</code> played those two parts.'},
            {tac:'refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩',
             state:'P Q R : Assertion\nσ : Store\nh hP : Heap\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : hP.disjoint (hQ.union hR)\nhu₁ : h = hP.union (hQ.union hR)\nhPQ : hP.disjoint hQ\nhPR : hP.disjoint hR\n⊢ h = (hP.union hQ).union hR',
             h:'One goal rather than two, and it prints with no <code>case</code> line above it. The star-valued conjunct went in inline at slot five, so only the equation was left as a hole — which is why the corpus proof has no focus dots in it. The pair <code>⟨hPR, hd₂⟩</code> is in that order because <code>disjoint_union_left</code> lists its two conjuncts in the order the union lists its pieces, <code>hP</code> then <code>hQ</code>; the forward direction\'s <code>⟨hd₂, hPR⟩</code> is the same rule applied to <code>disjoint_union_right</code>, whose union is <code>hQ.union hR</code>.'},
            {tac:'rw [hu₁, union_assoc]',
             h:'Closes it. The state below is what stands between the two rewrites.'}
          ],
          done:'No goals.'},
         {t:'state', cap:'From <code>rw [hu₁]</code> followed by <code>trace_state</code>, with <code>rw [union_assoc]</code> on the line after.',
          src:'P Q R : Assertion\nσ : Store\nh hP : Heap\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : hP.disjoint (hQ.union hR)\nhu₁ : h = hP.union (hQ.union hR)\nhPQ : hP.disjoint hQ\nhPR : hP.disjoint hR\n⊢ hP.union (hQ.union hR) = (hP.union hQ).union hR'},
         {t:'p', h:'Set that beside the forward direction\'s halfway state, <code>⊢ (hP.union hQ).union hR = hP.union (hQ.union hR)</code>. The two are each other reflected, and the identical <code>rw [union_assoc]</code> closes both — there it rewrites the left-hand side into the right, here the right-hand side into the left. <code>rw</code> rewrites the first match it finds anywhere in the goal, and in each case there is exactly one left-nested union to find.'}
       ]},

       {t:'code', tag:'illustration', cap:'Commutativity does not imply associativity, and this is the counterexample. Squares-sum on <code>Nat</code> is commutative outright and fails to associate at <code>1, 2, 3</code>: 34 against 170.',
        src:'def sqSum (a b : Nat) : Nat := a * a + b * b\n\ntheorem sqSum_comm (a b : Nat) : sqSum a b = sqSum b a := by\n  simp [sqSum, Nat.add_comm]\n\ntheorem sqSum_not_assoc : ¬ (∀ a b c : Nat, sqSum (sqSum a b) c = sqSum a (sqSum b c)) := by\n  intro hall\n  have h := hall 1 2 3\n  simp [sqSum] at h'},

       {t:'code', tag:'illustration', cap:'What would happen if <code>union_assoc</code> carried hypotheses the way <code>union_comm</code> does: nothing. All three pairwise facts are in scope by the time the equation slot is reached.',
        src:'theorem union_assoc_hyp {h₁ h₂ h₃ : Heap}\n    (_ : Heap.disjoint h₁ h₂) (_ : Heap.disjoint h₁ h₃) (_ : Heap.disjoint h₂ h₃) :\n    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) :=\n  union_assoc h₁ h₂ h₃\n\nexample (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩\n  subst hu₂\n  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁\n  refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩\n  · rw [hu₁, union_assoc_hyp hd₂ hPR hQR]\n  · exact ⟨hQ, hR, hQR, rfl, hq, hr⟩'},

       {t:'code', tag:'illustration', cap:'Associativity for the connective with the disjointness conjunct deleted. Unit 14\'s <code>starNoDisj</code>, five slots instead of six, and the same proof three lines shorter.',
        src:'theorem starNoDisj_assoc_left (P Q R : Assertion) :\n    starNoDisj (starNoDisj P Q) R ⊢ starNoDisj P (starNoDisj Q R) := by\n  intro σ h ⟨hPQ, hR, hu₁, ⟨hP, hQ, hu₂, hp, hq⟩, hr⟩\n  subst hu₂\n  exact ⟨hP, Heap.union hQ hR, by rw [hu₁, union_assoc], hp, ⟨hQ, hR, rfl, hq, hr⟩⟩'}
     ],

     pitfall: 'Four, in the order you will meet them; the last is the only one that waits for the mirror. <b>(1)</b> Flattening the pattern all the way. <code>intro σ h ⟨hPQ, hR, hd₁, hu₁, hP, hQ, hd₂, hu₂, hp, hq, hr⟩</code> gives eleven names and fails with <code>Invalid `⟨...⟩` notation: The expected type `R σ hR` is not an inductive type</code> — flattening consumes conjuncts rightwards, so the names run past the inner star and land on <code>R σ hR</code>, which is not a pair. The nesting has to be written. <b>(2)</b> Doing the <code>obtain</code> before the <code>subst</code>. <code>disjoint_union_left.mp hd₁</code> against <code>hd₁ : hPQ.disjoint hR</code> reports <code>The argument hd₁ has type hPQ.disjoint hR but is expected to have type (Heap.union ?m.114 ?m.115).disjoint ?m.116</code>, and then two hypotheses full of metavariables that poison the rest of the proof. The lemma needs to <i>see</i> a union, and it can only see one after <code>hPQ</code> has been eliminated. <b>(3)</b> Handing the wrong loose fact to the bridge: <code>disjoint_union_right.mpr ⟨hd₂, hQR⟩</code> gives <code>The argument hQR has type hQ.disjoint hR but is expected to have type hP.disjoint hR</code>. Both conjuncts of <code>disjoint_union_right</code> are about the <i>same first heap</i>, which is <code>hP</code>; <code>hQR</code> is about <code>hQ</code>. <b>(4)</b> Writing the mirror with the forward direction\'s argument order. <code>disjoint_union_left.mpr ⟨hd₂, hPR⟩</code> reports <code>The argument hd₂ has type hQ.disjoint hR but is expected to have type hP.disjoint hR</code> — and the diagnosis is (3) reflected: <code>disjoint_union_left</code>\'s two conjuncts share their <i>second</i> heap, which is <code>hR</code>, so they are listed <code>hP</code>-first and <code>hQ</code>-second. The lemma name swaps and so does the pair; changing one and not the other is the mistake, and it is the only place in either proof where the same two hypotheses are correct in one order and wrong in the other.',

     variants: 'Delete the disjointness conjunct from <code>∗</code> altogether — Unit 14\'s <code>starNoDisj</code> — and associativity <b>survives</b>, in three lines instead of six, because <code>union_assoc</code> never needed a hypothesis and everything that was deleted was hypothesis-handling. That proof is in the fold above. Commutativity does not survive: Unit 15 refuted it for <code>starNoDisj</code> with two singletons at one address, where the left-biased union keeps whichever value is on the left. So the two laws fail for genuinely different reasons, and disjointness is load-bearing for exactly one of them. · Trying to get one direction from the other and <code>star_comm</code> does not work, and the reason is not Lean\'s: commutativity permutes the leaves of a tree and never changes its shape, so no amount of it turns <code>(P ∗ Q) ∗ R</code> into a right-nested star. <code>sqSum</code>, in the fold above, is a commutative operation on <code>Nat</code> that is not associative, which settles the general claim. · Give <code>union_assoc</code> the disjointness hypotheses <code>union_comm</code> carries — all three pairwise ones — and the proof survives untouched except for the arguments: <code>rw [hu₁, union_assoc_hyp hd₂ hPR hQR]</code> compiles, because at the moment the equation slot is reached all three facts are in the context under their own names. That is the sharpest way to see what this page is about. The hypotheses would cost nothing here and everything elsewhere, which is why Unit 10 proved the lemma without them.'
    },

    /* ================================================== subst, afterwards === */

    {t:'detail', title:'When `subst` refuses', open:false, blocks:[
      {t:'p', h:'<code>subst</code> eliminates a <i>variable</i>. It needs an equation with a free local variable standing alone on one side and anything at all on the other — <code>x = t</code> or <code>t = x</code> — and it works in both orientations, which is why <code>hu₂ : hPQ = hP.union hQ</code> and its reverse would both be accepted.'},
      {t:'p', h:'Give it an equation between two compound terms and it says so, naming the equation it was handed:'},
      {t:'state', cap:'From <code>have hbad : Heap.union hP hQ = Heap.union hP hQ := rfl</code> followed by <code>subst hbad</code>.',
       src:'Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)\n  hP.union hQ = hP.union hQ'},
      {t:'p', h:'Give it something that is not an equation at all — <code>subst hd₁</code>, say — and the message changes shape, because now there is nothing to look at:'},
      {t:'state', src:'Tactic `subst` failed: did not find equation for eliminating \'hd₁\''},
      {t:'p', h:'The first has a repair: <code>rw … at</code> rewrites the hypotheses that mention the term and leaves the context otherwise as it was. It is strictly weaker and strictly safer — it never removes anything, so it never fails for the reason above, and it never shortens a context either. The second has none. <code>hd₁</code> is not an equation, and no variable was ever going to come out of it.'}
    ]},

    /* ================================================== the monoid, done === */

    {t:'sec', s:'The monoid, complete'},

    {t:'p', h:'Five facts, and they are now all proved. <code>emp</code> is a unit on the left and on the right, <code>∗</code> is commutative, <code>∗</code> is associative, and <code>∗</code> respects <code>⊣⊢</code> in both arguments. Assertions under <code>∗</code> and <code>emp</code> are a commutative monoid, and the proof of each law is the corresponding law of heaps with a fixed amount of packaging round it.'},

    {t:'tbl', cap:'Every law of <code>∗</code> and what its proof spends. Three of the four rows spend a law of <code>Heap.union</code> together with a fact about <code>Heap.disjoint</code>; the fourth spends nothing, because monotonicity never touches the cut.',
     head:['law of <code>∗</code>', 'what it spends'],
     rows:[
       ['<code>star_emp_left</code>, <code>star_emp_right</code>', '<code>union_empty_left</code>, <code>union_empty_right</code>, and the two <code>disjoint_empty_*</code> facts to build with'],
       ['<code>star_comm</code>', '<code>union_comm</code> — which carries a disjointness hypothesis — and <code>disjoint_symm</code>'],
       ['<code>star_assoc_left</code>, <code>star_assoc_right</code>', '<code>union_assoc</code>, which carries none, and <code>disjoint_union_left</code>/<code>disjoint_union_right</code>'],
       ['<code>star_mono</code>, and <code>star_congr</code> after it', 'nothing: the cut is passed through untouched']
     ]},

    {t:'note', kind:'key', title:'∗ is not a connective about heaps', h:'Look at what these proofs actually used about heaps: an associative operation, a unit for it, a commutativity law qualified by a validity relation, the symmetry of that relation, and the fact that the unit is valid against everything. Those are the fields of Unit 10\'s <code>PCM</code> — a partial commutative monoid — and <code>Heap</code> was only ever one model of it. Substitute permissions, tokens, protocol states or fractional ownership for heaps and commutativity and the unit law hold with the same proofs. That is a claim, not a slogan: Unit 38 defines the separating conjunction of an arbitrary <code>PCM</code> and proves both of them from the fields alone, and you can set the proofs side by side.'},

    {t:'p', h:'Associativity is the exception, and this page is where you can see why. <code>star_assoc_left</code> reaches outside the monoid laws exactly twice, at <code>disjoint_union_left</code> and <code>disjoint_union_right</code>, and neither of those is a field of <code>PCM</code>. The structure says that validity is symmetric and that the unit is valid against everything; it says nothing about how validity behaves when you compose. So associativity is the one law of the four whose generalisation needs an axiom the structure does not have, and the two places the proof cites a bridge — the <code>obtain</code>, and the third slot of the <code>refine</code> — are where that shows. Unit 11 recorded the same gap about <code>splits_assoc</code>; this is the connective-level statement of it.'},

    /* ======================================================= exercise x37 === */

    {t:'ex',
     id: 'x37',
     name: 'star_assoc_iff',
     why: 'Unit 15 packaged the two unit laws and commutativity as <code>⊣⊢</code>s; associativity was not yet proved and so could not be packaged with them. <code>star_congr</code> rewrites inside a star only when it is handed a <code>⊣⊢</code>, so until this line exists associativity is two lemmas you have to pick between rather than a rewrite rule. The other three <code>_iff</code>s were built in <code>x36</code>; this closes the set. Like them, it is never cited again in the corpus — what it buys is the option, and the fact that the algebra is packaged the same way throughout.',

     setup: 'Both directions are proved. <code>⊣⊢</code> is Unit 12\'s <code>AssertionEquiv</code>, which is a conjunction of two entailments, so its proof is a two-slot <code>⟨…⟩</code>. The order of the two components follows the order of the statement.',

     goal: 'theorem star_assoc_iff (P Q R : Assertion) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=',

     hints: [
       'The goal <code>(P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R)</code> unfolds to <code>((P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)) ∧ (P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R)</code> — the two theorems of <code>m4-4</code>, in that order, joined by <code>∧</code>.',
       'Nothing has to be proved. Both components exist under their own names; the work is supplying them in the right order and with their arguments.',
       'A two-slot <code>⟨…⟩</code>, in term mode, with no <code>by</code> anywhere. Both <code>star_assoc_left</code> and <code>star_assoc_right</code> take <code>P</code>, <code>Q</code> and <code>R</code> explicitly.',
       'Write <code>⟨star_assoc_left P Q R, star_assoc_right P Q R⟩</code> after the <code>:=</code>. The first slot must be the direction that matches the left-to-right reading of <code>⊣⊢</code>, which is the same reading <code>x28</code> established for <code>equiv_symm</code>.'
     ],

     sol: 'theorem star_assoc_iff (P Q R : Assertion) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=\n  ⟨star_assoc_left P Q R, star_assoc_right P Q R⟩',

     solNote: 'One line, and no tactic in it. It exists because a <code>⊣⊢</code> can be handed to <code>star_congr</code> and a loose pair of entailments cannot.',

     expl: 'An <code>AssertionEquiv</code> is a conjunction, so its proof is a pair, so the whole exercise is choosing which theorem goes in which slot. The two names differ by direction and the elaborator checks the direction for you.',

     walk: [
       {tac:'theorem star_assoc_iff (P Q R : Assertion) : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) :=', h:'A term-mode declaration: no <code>by</code>, so what follows the <code>:=</code> is a value of the type on the left. That type is a conjunction of two entailments, folded twice — once by <code>AssertionEquiv</code> and once by the <code>⊣⊢</code> notation — and <code>⟨…⟩</code> sees through both.'},
       {tac:'⟨star_assoc_left P Q R, star_assoc_right P Q R⟩', h:'Two slots. The first is the forward entailment, applied to the three assertions so that it is a proof rather than a function; the second is the backward one. Applying them is not optional: <code>star_assoc_left</code> on its own is <code>∀ (P Q R : Assertion), …</code>, and a <code>∀</code> is not an entailment.'}
     ],

     deep: [
       {t:'trace', title:'The same theorem in tactic mode, so the two components are visible as goals',
        start:'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊣⊢ P ∗ Q ∗ R',
        steps:[
          {tac:'constructor',
           state:'case left\nP Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R\n\ncase right\nP Q R : Assertion\n⊢ P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R',
           h:'<code>constructor</code> splits the conjunction and names the halves <code>left</code> and <code>right</code>. Reading them tells you which theorem each slot wants, which is the whole difficulty of the exercise.'},
          {tac:'· exact star_assoc_left P Q R', state:'case right\nP Q R : Assertion\n⊢ P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R', h:'First goal closed by name.'},
          {tac:'· exact star_assoc_right P Q R', h:'Second likewise. The term-mode spelling is these three lines with the scaffolding removed.'}
        ],
        done:'No goals.'}
     ],

     pitfall: 'Forgetting the arguments. <code>⟨star_assoc_left, star_assoc_right⟩</code> reports <code>The argument star_assoc_left has type ∀ (P Q R : Assertion), (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R but is expected to have type (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R</code>. The theorem\'s three binders are explicit, so a bare name is a function and not a proof; <code>star_emp_left_iff</code> in <code>x36</code> had the same shape and the same requirement.',

     variants: 'Swap the two components and the error names the mismatch directly: <code>The argument star_assoc_right P Q R has type P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R but is expected to have type (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R</code>. <code>x36</code>\'s <code>star_comm_iff</code> refuses a swap too — <code>⟨star_comm Q P, star_comm P Q⟩</code> gives <code>The argument star_comm Q P has type Q ∗ P ⊢ P ∗ Q but is expected to have type P ∗ Q ⊢ Q ∗ P</code> — but there both slots carry the same theorem name and differ only in the order of its arguments, so the direction is legible only to a reader who also remembers which way <code>star_comm</code> points. Here the slots carry different names and the direction is legible on its own. · State it the other way round — <code>P ∗ (Q ∗ R) ⊣⊢ (P ∗ Q) ∗ R</code> — and the two components exchange places. That statement is equally true, and it is not in the corpus because it does not have to be: Unit 12\'s <code>equiv_symm</code> turns this one into it.'
    },

    /* ========================================================== closing === */

    {t:'dod', h:'You can state and prove both directions of associativity for <code>∗</code>, open a star whose conjunct is a star in one <code>intro</code> pattern, eliminate an intermediate heap before building anything, and move a disjointness fact between its glued and loose forms in whichever direction the goal asks for. You can say which single lemma in the proof is about unions, and that it carries no hypothesis. And you can say what the algebra of assertions is — a commutative monoid — and which one of its laws is the one that does not come free with an arbitrary partial commutative monoid.'},

    {t:'p', h:'The algebra is nearly complete and you can move resources around freely. Two things are missing before it can be used. First: how do you attach an ordinary proposition — one about the store, of the kind <code>fact</code> embeds — to a separating conjunction, when a proposition owns no memory and <code>∗</code> insists that its two sides own disjoint pieces? Second, and further off: there is still nothing in this course to reason <i>about</i>. No program has been written down.'}

  ]
});
