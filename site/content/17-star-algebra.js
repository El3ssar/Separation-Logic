registerChapter({
  id: 'star-algebra',
  num: '15',
  ledgerForward: ['star_swap_middle'],
  phase: 'Phase 2 · The logic of ownership',
  title: 'LAB — the laws of ∗',
  blurb: 'Six laws in one sitting: emp is a unit on both sides, ∗ is commutative and monotone, and it distributes over ∨ and ∃ — after which exactly one law is left unproved.',

  orient: {
    youWill: [
      'Prove <code>emp ∗ P ⊢ P</code> and its converse, and say why they are two theorems rather than one.',
      'Choose the cut when you are the one building the star, and know that for the unit laws the choice is forced.',
      'Read an equation slot and decide whether the lemma that fills it wants <code>.symm</code> — and see the one law where dropping it is silently fine and the mirror law where it is not.',
      'Prove commutativity, and point at both slots in which the star\'s own disjointness hypothesis is spent.',
      'Prove monotonicity, derive its two one-sided forms as term proofs, and improve one side of a star without touching the other.',
      'Prove that <code>∗</code> distributes over <code>∨</code> and commutes with <code>∃</code>, and say why the <code>∃</code> case is the first line of both list theorems in Unit 33.',
      'Package a pair of entailments as a <code>⊣⊢</code>, and rewrite <i>inside</i> a star with <code>star_congr</code>.',
      'Say why <code>∗</code> commutes with <code>∃</code> in both directions and with <code>∀</code> in only one.'
    ],
    needs: [
      'Unit 14: the definition of <code>∗</code>, the flat six-slot <code>⟨…⟩</code> that builds one, and the six-name <code>intro</code> pattern that takes one apart.',
      'Unit 09: <code>union_empty_left</code>, <code>union_empty_right</code>. Unit 08: <code>disjoint_symm</code>, <code>disjoint_empty_left</code>, <code>disjoint_empty_right</code>. Unit 10: <code>union_comm</code> and the disjointness hypothesis it carries.',
      'Unit 12: <code>⊢</code>, <code>⊣⊢</code>, <code>entails_refl</code>, <code>entails_trans</code>, <code>aOr</code>, <code>aExists</code>, <code>aTrue</code>. Unit 13: <code>emp</code> as an equation on the heap, and <code>pointsTo_not_emp</code>.'
    ],
    payoff: 'From Unit 17 onwards a proof about assertions is a chain of these six laws composed with <code>entails_trans</code>, and no heap is mentioned in it. Unit 17 derives three permutation theorems from nothing but this page and associativity; Unit 29 spends <code>star_comm</code> three times and <code>star_emp_left</code> twice in the course of verifying two programs; Unit 33 opens the inductive step of both list theorems with <code>star_exists_left</code>.'
  },

  blocks: [

    /* ================================================================= brief === */

    {t:'p', h:'Yes to both. <code>emp</code> is a unit for <code>∗</code> on each side, and <code>∗</code> is commutative, and neither takes more than four lines. Six laws are proved on this page, in one sitting, because individually none of them is interesting and collectively they are the language the rest of the course is written in. From Unit 17 on, an entailment between assertions is often a chain of these composed with <code>entails_trans</code> and nothing else — no <code>intro</code>, no heap named anywhere in it.'},

    {t:'p', h:'Every proof here has the same two halves. Take the star apart with the six-name <code>intro</code> pattern, which hands you two heaps and four facts about them; then build a new star with a six-slot <code>⟨…⟩</code>, choosing which two heaps to use. Both moves are Unit 14\'s and neither needs a lemma. What changes from law to law is one slot: the equation <code>h = Heap.union h₁ h₂</code>, and which fact from Module 2 discharges it.'},

    {t:'tbl', cap:'The six laws and the Module 2 fact each one spends. Two of them spend nothing at all: the connective has properties with no heap content whatever.',
     head:['law', 'what the equation slot costs'],
     rows:[
       ['<code>emp ∗ P ⊢ P</code>', '<code>union_empty_left</code>'],
       ['<code>P ∗ emp ⊢ P</code>', '<code>union_empty_right</code>'],
       ['<code>P ⊢ emp ∗ P</code> and its mirror', '<code>disjoint_empty_left</code>/<code>_right</code>, and the same two union lemmas <i>reversed</i>'],
       ['<code>P ∗ Q ⊢ Q ∗ P</code>', '<code>disjoint_symm</code>, and <code>union_comm</code> — the one lemma on the list that carries a hypothesis'],
       ['monotonicity', 'nothing: the cut is passed through untouched'],
       ['distribution over <code>∨</code> and <code>∃</code>', 'nothing, for the same reason']
     ]},

    /* ======================================================= worked example === */

    {t:'sec', s:'The worked example: emp ∗ P ⊢ P'},

    {t:'p', h:'On paper this is a sentence: if the heap splits into an empty piece and a piece satisfying <code>P</code>, then the whole heap is that second piece, so <code>P</code> holds of it. The Lean proof is that sentence with the word <i>so</i> replaced by three rewrites, and the interesting question is which three, in which order.'},

    {t:'code', tag:'verified', cap:'The left unit law: the statement, then three tactics.',
     src:'theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩\n  rw [hu, he, union_empty_left]\n  exact hp'},

    {t:'p', h:'The <code>_</code> in the third slot of the pattern is the disjointness fact, which this proof never uses: the two pieces could overlap for all the argument cares, because the empty heap contributes nothing either way. Lean keeps it in the context under an inaccessible name, <code>left✝</code>, so you can see it and cannot name it.'},

    {t:'trace', title:'star_emp_left, with the three rewrites separated',
     start:'P : Assertion\n⊢ emp ∗ P ⊢ P',
     steps:[
       {tac:'intro σ h ⟨h₁, h₂, _, hu, he, hp⟩',
        state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ h',
        h:'Three binders and a six-name pattern, exactly as in Unit 14. The goal is now about <code>h</code>, and the only fact you have about <code>P</code> is about <code>h₂</code>. Everything that follows is the work of turning one into the other.'},
       {tac:'rw [hu]',
        state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ (h₁.union h₂)',
        h:'The ownership equation replaces <code>h</code> by the union. This has to happen first: until it does, <code>h₁</code> does not occur in the goal, and there is nothing for the next rewrite to find.'},
       {tac:'rw [he]',
        state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ (Heap.empty.union h₂)',
        h:'<code>he : emp σ h₁</code> is <code>h₁ = Heap.empty</code> with a name wrapped round it, and <code>rw</code> reaches through the wrapper without being asked. That is Unit 13\'s decision paying off: an exact ownership claim is an equation, and equations rewrite.'},
       {tac:'rw [union_empty_left]',
        state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ h₂',
        h:'Unit 09\'s left unit law, applied under the assertion. The goal is now literally the type of <code>hp</code>.'},
       {tac:'exact hp', state:'No goals.', h:'The heap the assertion is asked about and the heap you have a proof for are the same term.'}
     ],
     done:'The corpus writes the three rewrites as one line, <code>rw [hu, he, union_empty_left]</code>. Splitting them is how you see that they are three separate facts and that their order is forced.'},

    {t:'p', h:'Reverse the first two and the proof stops. <code>rw [he]</code> on the goal <code>P σ h</code> is looking for the term <code>h₁</code>, and <code>h₁</code> is not there yet.'},

    {t:'state', cap:'What Lean says when the rewrites are given in the other order. The context is printed underneath the message, and it is the same context as before — nothing has happened.',
     src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  h₁\nin the target expression\n  P σ h'},

    {t:'detail', title:'The same proof with subst instead of rw', tag:'aside', open:false, blocks:[
      {t:'p', h:'Both <code>hu</code> and <code>he</code> are equations with a variable on one side, so <code>subst</code> will eliminate that variable outright rather than rewriting one occurrence of it. It works, and it costs a line.'},
      {t:'code', tag:'illustration', cap:'The same theorem, one line longer. <code>subst hu</code> deletes <code>h</code>; <code>subst he</code> deletes <code>h₁</code>; the union lemma still has to be applied by name.',
       src:'example (P : Assertion) : emp ∗ P ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩\n  subst hu\n  subst he\n  rw [union_empty_left]\n  exact hp'},
      {t:'p', h:'Nothing chooses between them here. <code>subst</code> is the better move when the variable it eliminates occurs in several hypotheses you are going to use later — which is what happens in Unit 16 — and <code>rw</code> is the better move when it does not, because it leaves the context alone.'}
    ]},

    {t:'h4', s:'The converse, where you choose the cut'},

    {t:'p', h:'<code>P ⊢ emp ∗ P</code> is a different kind of statement, and the difference is Unit 14\'s asymmetry. Consuming a star hands you a cut. Producing one makes you name it, and here you have nothing to name it with except the single heap <code>h</code> the entailment gives you.'},

    {t:'p', h:'The choice is forced, and you can read it off the slots backwards. The only proof of anything about <code>P</code> in your hands is <code>hp : P σ h</code>, so the right half must be <code>h</code>. The left half must satisfy <code>emp</code>, which is an equation saying it is <code>Heap.empty</code>, so the left half must be <code>Heap.empty</code>. Both halves are now fixed, and the two remaining slots are Module 2 facts about them.'},

    {t:'code', tag:'verified', cap:'The left intro form. Everything after the two heaps is a lemma applied to <code>h</code>, with one <code>rfl</code> for the <code>emp</code> conjunct.',
     src:'theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by\n  intro σ h hp\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩'},

    {t:'p', h:'The <code>rfl</code> is the <code>emp</code> conjunct: the goal in that slot is <code>emp σ Heap.empty</code>, which unfolds to <code>Heap.empty = Heap.empty</code>. It is the smallest possible demonstration that <code>emp</code> is an equation and not a predicate you have to reason about.'},

    {t:'h4', s:'Which way round the equation goes'},

    {t:'p', h:'The fourth slot of a star is <code>h = Heap.union h₁ h₂</code>: the heap in hand on the <b>left</b>, the union on the right. Unit 09\'s lemma is <code>union_empty_left h : Heap.union Heap.empty h = h</code> — the union on the left. Those are the same fact and not the same type: <code>a = b</code> and <code>b = a</code> are two different statements, and a slot wants a term of <i>its</i> type. So the lemma arrives with <code>.symm</code> on it.'},

    {t:'p', h:'This particular law will not punish you for leaving it off, and the reason is a fact about <code>Heap.union</code> rather than about <code>emp</code>. Union matches on its left argument, so <code>Heap.union Heap.empty h</code> reduces to <code>h</code> on the spot and the fourth slot of the left law accepts the lemma either way round — and accepts a bare <code>rfl</code>. <code>Heap.union h Heap.empty</code> is stuck on a variable and reduces to nothing, so the mirror law accepts exactly one of the three. The discipline therefore has to be learned on the mirror, which is where <code>m4-2</code> puts it.'},

    {t:'p', h:'The discipline itself is one sentence. When an equation slot rejects your lemma, read the two types the error prints rather than the lemma\'s name: if they are the same equation with the sides exchanged, the repair is <code>.symm</code> and nothing else. The corpus writes <code>.symm</code> in both intro forms even though the left one does not need it, so that the two proofs are mirror images and neither is a special case to remember.'},

    /* ================================================================ m4-1 === */

    {t:'p', h:'The first two exercises are the two laws above and their mirrors. <code>star_emp_left</code> and <code>star_emp_left_intro</code> are on the page; what you are writing is the other half of each pair, and neither half is a copy of the one you were given.'},

    {t:'ex',
     id: 'm4-1',
     name: 'star_emp_left / star_emp_right',
     why: 'These are the two halves of "<code>emp</code> is a unit", and they are the first theorems in the course whose proof consumes a star. The consumption move — three binders and a six-name pattern — opens every proof on this page that consumes a star, and nine more theorems in the course, the last of them in Unit 34. <code>star_emp_left</code> itself is cited three times in later Lean, twice in Unit 29 and once in Unit 27, always to delete the <code>emp</code> a small-footprint rule leaves behind; <code>star_emp_right</code> is cited nowhere, and is here because a unit law with only one side is not a unit law. The mirror law is not a copy: it spends <code>union_empty_right</code>, which unlike its partner is not a reduction, so the two proofs are the same shape over different ground.',
     setup: '<code>star_emp_left</code> is worked in full above; transcribe it and then write its mirror. <code>union_empty_left</code> and <code>union_empty_right</code> are Unit 09\'s, and both are stated with the union on the left of the equation.',
     goal: 'theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by\n  sorry\n\ntheorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by',
     hints: [
       'The goal <code>emp ∗ P ⊢ P</code> unfolds to: for every store <code>σ</code> and heap <code>h</code>, if there are heaps <code>h₁ h₂</code> that do not overlap, whose union is <code>h</code>, with <code>emp</code> at <code>h₁</code> and <code>P</code> at <code>h₂</code>, then <code>P</code> holds at <code>h</code>. For the mirror law the last two are swapped: <code>P</code> at <code>h₁</code> and <code>emp</code> at <code>h₂</code>.',
       'You know <code>P</code> holds at one of the two pieces. You need it at the whole heap. So rewrite the whole heap into the union of the pieces, then rewrite the empty piece into <code>Heap.empty</code>, then apply the unit law for unions on the correct side. Three equations, and the order they are applied in is not free.',
       'One <code>intro</code> with a six-name pattern, one <code>rw</code> with three lemmas in it, one <code>exact</code>. The three lemmas are the two ownership hypotheses the pattern gave you and, last, <code>union_empty_left</code> or <code>union_empty_right</code>.',
       'Start <code>intro σ h ⟨h₁, h₂, _, hu, he, hp⟩</code> for the left law — the underscore is the disjointness fact, which neither proof uses. That leaves <code>⊢ P σ h</code> with <code>hu : h = h₁.union h₂</code> in the context. For the mirror law the fifth and sixth names swap: <code>⟨h₁, h₂, _, hu, hp, he⟩</code>.'
     ],
     sol: 'theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩\n  rw [hu, he, union_empty_left]\n  exact hp\n\ntheorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, hp, he⟩\n  rw [hu, he, union_empty_right]\n  exact hp',
     solNote: 'The two proofs differ in two places: the order of the last two names in the pattern, and the last lemma in the <code>rw</code>. Everything else is character for character the same.',
     expl: 'The premise gives you a decomposition of <code>h</code> in which one piece is empty. Rewriting with the decomposition puts both pieces into the goal; rewriting with the <code>emp</code> hypothesis turns one of them into <code>Heap.empty</code>; the union lemma then deletes it. What is left is the piece the surviving conjunct was always about.',
     walk: [
       {tac:'intro σ h ⟨h₁, h₂, _, hu, he, hp⟩', h:'Consumes the three binders of <code>⊢</code> and then splits the premise into its six components: the two pieces <code>h₁</code> and <code>h₂</code>, their disjointness — sent to the underscore and parked in the context as <code>left✝</code> — the decomposition <code>hu : h = h₁.union h₂</code>, and one ownership fact for each piece. The goal drops from an entailment to <code>P σ h</code>.'},
       {tac:'rw [hu, …]', h:'Replaces <code>h</code> in the goal by <code>h₁.union h₂</code>. Nothing else in the proof can happen before this, because until it does the goal mentions neither piece.'},
       {tac:'rw […, he, …]', h:'<code>he</code> is definitionally <code>h₁ = Heap.empty</code>, so this turns the goal into <code>P σ (Heap.empty.union h₂)</code>. The rewrite reaches through the folded name <code>emp</code> without an <code>unfold</code>.'},
       {tac:'rw […, union_empty_left]', h:'Deletes the empty half, leaving <code>P σ h₂</code>. In the mirror law the empty half is on the right and this is <code>union_empty_right</code>, leaving <code>P σ h₁</code>.'},
       {tac:'exact hp', h:'Closes the goal, because after the three rewrites it is the type of <code>hp</code> on the nose.'}
     ],
     deep: [
       {t:'trace', title:'star_emp_right, the half you write',
        start:'P : Assertion\n⊢ P ∗ emp ⊢ P',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, _, hu, hp, he⟩',
           state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhe : emp σ h₂\n⊢ P σ h',
           h:'Compare with the left law\'s context: <code>hp</code> and <code>he</code> have exchanged heaps. Everything above them is identical, which is the point of naming the pattern in the definition\'s order.'},
          {tac:'rw [hu, he]',
           state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhe : emp σ h₂\n⊢ P σ (h₁.union Heap.empty)',
           h:'The empty heap is now on the right of the union, which is why <code>union_empty_left</code> will not fire here.'},
          {tac:'rw [union_empty_right]',
           state:'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhe : emp σ h₂\n⊢ P σ h₁',
           h:'And the goal is <code>hp</code>\'s type.'}
        ],
        done:'exact hp'}
     ],
     pitfall: 'Giving the three rewrites in the order they are stated in the goal rather than the order they can fire in. <code>rw [he]</code> before <code>rw [hu]</code> reports <code>Did not find an occurrence of the pattern h₁ in the target expression P σ h</code> — a correct message that reads like a complaint about <code>he</code> when the problem is that <code>hu</code> has not run. The second trap is finishing the mirror law with <code>union_empty_left</code> out of habit: <code>Did not find an occurrence of the pattern Heap.empty.union ?h in the target expression P σ (h₁.union Heap.empty)</code>, which prints the shape the lemma is looking for and the shape the goal actually has, one under the other — empty on the left against empty on the right.',
     variants: 'Delete the disjointness conjunct and both laws survive: Unit 14\'s <code>starNoDisj</code> is exactly that connective, and <code>starNoDisj emp P ⊢ P</code> closes on <code>intro σ h ⟨h₁, h₂, hu, he, hp⟩</code> followed by the identical <code>rw</code> and <code>exact</code>. Only the name count changes, because neither proof ever touches that slot — which is why it is an underscore here. Delete the union equation instead and both die at once: without <code>hu</code> the goal is about a heap the hypotheses never mention. And the classical analogue, <code>aAnd emp P ⊢ P</code>, is <code>fun _ _ h => h.2</code> — Unit 12\'s right projection, needing none of this, because classical conjunction hands both conjuncts the same heap. The two statements look alike and only one of them says anything about memory.'},

    /* ================================================================ m4-2 === */

    {t:'p', h:'The converses run the other way, and the cut has to come from somewhere.'},

    {t:'ex',
     id: 'm4-2',
     name: 'star_emp_left_intro / star_emp_right_intro',
     why: 'This is the first time you build a star without being handed the two heaps, and the right place to learn to choose a cut, because here the choice is forced and you can check your reasoning against the answer. It also installs the <code>.symm</code> discipline on the equation slot, which is the single most frequent small failure in the rest of the module. Together with <code>m4-1</code> these give <code>emp ∗ P ⊣⊢ P</code>, which is what <code>x36</code> packages. <code>star_emp_left_intro</code> is cited exactly once in the whole corpus, at the end of this unit, where it turns Unit 14\'s two concrete refutations of weakening into the general theorem.',
     setup: '<code>star_emp_left_intro</code> is worked above; transcribe it and then write its mirror, which is where the equation slot bites. Available: <code>disjoint_empty_left</code>, <code>disjoint_empty_right</code> from Unit 08, and <code>union_empty_left</code>, <code>union_empty_right</code> from Unit 09.',
     goal: 'theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by\n  sorry\n\ntheorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by',
     hints: [
       'The goal <code>P ⊢ emp ∗ P</code> unfolds to: for every store <code>σ</code> and heap <code>h</code>, given <code>P σ h</code>, there exist heaps <code>h₁ h₂</code> with <code>h₁.disjoint h₂</code>, <code>h = h₁.union h₂</code>, <code>emp σ h₁</code> and <code>P σ h₂</code>. So you are handed one heap and asked to produce two, plus four facts about them. For the mirror law the last two conjuncts are swapped: <code>P σ h₁</code> and <code>emp σ h₂</code>.',
       'Work the choice out backwards. The only fact you hold about <code>P</code> is at <code>h</code>, so one half must be <code>h</code>; the other half has to satisfy <code>emp</code>, which pins it to <code>Heap.empty</code>. Then the disjointness and the union equation are facts about <code>h</code> and the empty heap, and Module 2 proved both.',
       'One <code>intro</code> for the three binders — nothing to destructure, so three plain names — then one <code>exact</code> with a six-slot <code>⟨…⟩</code>. The four proof slots are, in order: a <code>disjoint_empty_*</code> lemma, a <code>union_empty_*</code> lemma, <code>rfl</code>, and your hypothesis — with the <code>rfl</code> and the hypothesis in whichever order the statement puts <code>emp</code> and <code>P</code>.',
       'For the left law: <code>exact ⟨Heap.empty, h, disjoint_empty_left h, …⟩</code>. The fourth slot wants <code>h = Heap.union Heap.empty h</code> and the lemma states the reverse, so it needs <code>.symm</code> — mandatory in the mirror law, and harmless here.'
     ],
     sol: 'theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by\n  intro σ h hp\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩\n\ntheorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by\n  intro σ h hp\n  exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩',
     solNote: 'If you climbed all four hints and are still stuck on which slot wants what, open the definition of <code>∗</code> beside this and count. Six slots, and they are in the order the definition writes them.',
     expl: 'A star is an existential, so proving one means producing witnesses. The witnesses are determined here by working backwards from the two conjuncts: <code>P</code> forces one half to be the whole heap and <code>emp</code> forces the other to be empty. Once they are fixed, the remaining three slots are a Unit 08 lemma, a Unit 09 lemma reversed, and a <code>rfl</code>.',
     walk: [
       {tac:'intro σ h hp', h:'Three binders again, but the premise is <code>P σ h</code> and there is nothing to destructure. The goal becomes <code>(emp ∗ P) σ h</code> — a six-slot existential displayed folded, with one heap in the context and two to be produced.'},
       {tac:'⟨Heap.empty, h, …⟩', h:'Supplies the two witnesses, so the goal stops being an existential: the four remaining slots are the body with <code>Heap.empty</code> for <code>h₁</code> and <code>h</code> for <code>h₂</code>. This is the only creative slot in the proof, and the reasoning that produced it happened before any Lean was typed.'},
       {tac:'…, disjoint_empty_left h, …', h:'Discharges <code>Heap.disjoint Heap.empty h</code>. Unit 08 proved that the empty heap is disjoint from everything, on both sides.'},
       {tac:'…, (union_empty_left h).symm, …', h:'Discharges <code>h = Heap.union Heap.empty h</code>. The lemma is stated the other way round, so <code>.symm</code> turns it. This is the slot that will reject a lemma in the mirror law.'},
       {tac:'…, rfl, …', h:'Discharges <code>emp σ Heap.empty</code>, which unfolds to <code>Heap.empty = Heap.empty</code>.'},
       {tac:'…, hp⟩', h:'Discharges <code>P σ h</code>, which is the premise, unchanged and at the same heap.'}
     ],
     deep: [
       {t:'trace', title:'star_emp_right_intro, with the equation slot left open',
        start:'P : Assertion\n⊢ P ⊢ P ∗ emp',
        steps:[
          {tac:'intro σ h hp',
           state:'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ (P ∗ emp) σ h',
           h:'One heap, one premise, and a goal that is an existential in disguise. Nothing in the context can be taken apart.'},
          {tac:'refine ⟨h, Heap.empty, disjoint_empty_right h, ?_, hp, rfl⟩',
           state:'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ h = h.union Heap.empty',
           h:'Filling five of the six slots and leaving the equation open shows the slot\'s type on its own. <code>union_empty_right h</code> proves the reverse of it, and that is exactly the gap <code>.symm</code> closes. The corpus proof writes the whole tuple in one <code>exact</code>; this is how to see the slot when it will not accept what you gave it.'}
        ],
        done:'exact (union_empty_right h).symm'},
       {t:'cmp',
        left:{t:'The left law tolerates the mistake', kind:'good', tag:'illustration',
          h:'The fourth slot filled with a bare <code>rfl</code>, and nothing proved there at all: both sides of <code>h = Heap.union Heap.empty h</code> are already the same term once the union has reduced. This compiles.',
          src:'example (P : Assertion) : P ⊢ emp ∗ P := by\n  intro σ h hp\n  exact ⟨Heap.empty, h, disjoint_empty_left h, rfl, rfl, hp⟩'},
        right:{t:'The mirror law does not', kind:'bad', tag:'sketch',
          h:'With the empty heap on the right there is no reduction, so the slot\'s type and the lemma\'s type stay apart. Drop the <code>.symm</code> in <code>star_emp_right_intro</code> and the slot rejects the lemma.',
          src:'example (P : Assertion) : P ⊢ P ∗ emp := by\n  intro σ h hp\n  exact ⟨h, Heap.empty, disjoint_empty_right h, union_empty_right h, hp, rfl⟩'}},

       {t:'state', cap:'What the right-hand column reports. Lean names the term, the type it has, and the type the slot wanted; the two differ by an exchange of sides and by nothing else.',
        src:'error: Application type mismatch: The argument\n  union_empty_right h\nhas type\n  h.union Heap.empty = h\nbut is expected to have type\n  h = h.union Heap.empty\nin the application\n  And.intro (union_empty_right h)'}
     ],
     pitfall: 'Choosing the cut the other way round, and writing the mirror proof under the left law\'s statement: <code>⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, rfl, hp⟩</code> for <code>P ⊢ emp ∗ P</code>. The third and fourth slots type-check without complaint, because <code>Heap.disjoint h Heap.empty</code> and <code>h = Heap.union h Heap.empty</code> are perfectly true statements; the first slot that cannot be filled is the <code>emp</code> conjunct, which with these witnesses asks for <code>emp σ h</code> instead of <code>emp σ Heap.empty</code>. <code>Application type mismatch: The argument rfl has type ?m.22 = ?m.22 but is expected to have type emp σ h</code>. The message names <code>rfl</code>, in slot five; the mistake is in slot one. When a tuple fails in a proof slot, check the witnesses before you read the proof it is complaining about.',
     variants: 'Delete the disjointness conjunct — Unit 14\'s <code>starNoDisj</code> — and both proofs survive one slot and one lemma shorter, <code>⟨Heap.empty, h, (union_empty_left h).symm, rfl, hp⟩</code>, because nothing was ever in doubt there: the empty heap is disjoint from everything. Strengthen <code>emp</code> instead, to <code>0 ↦ 0</code>, and the law is false, at the first slot rather than the fourth: take <code>P</code> to be <code>emp</code> and the heap to be <code>Heap.empty</code>, and no cut of the empty heap has a left half holding a cell. What a unit law needs of its unit is exactly this — that the conjunct pin its half to a heap you can always produce.'},

    /* =========================================================== commutative === */

    {t:'sec', s:'Commutativity, and the one hypothesis on the page'},

    {t:'p', h:'Every fact used so far has been unconditional. <code>union_comm</code> is not: Unit 10 proved <code>Heap.union h₁ h₂ = Heap.union h₂ h₁</code> only under <code>Heap.disjoint h₁ h₂</code>, and it exhibited the two overlapping heaps where the two orders disagree — one address, two values, and Unit 09\'s left bias deciding which one survives. So the question <i>is <code>∗</code> commutative?</i> is really the question <i>does a star carry enough to satisfy <code>union_comm</code>?</i> — and it does, in its third slot, which exists for exactly this.'},

    {t:'code', tag:'verified', cap:'Commutativity. Two lines, and one of them is the pattern.',
     src:'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩'},

    {t:'p', h:'The single hypothesis <code>hd</code> is spent twice, in adjacent slots. <code>disjoint_symm hd</code> fills the new star\'s disjointness conjunct, because the halves have changed places and <code>Heap.disjoint</code> is stated in an order. <code>union_comm hd</code> fills the equation, and that is the entire mathematical content of the theorem: the heaps do not move, only the names of the halves do.'},

    {t:'p', h:'The fourth slot holds a tactic block. Unit 09 already put a <code>by</code> inside a term this way; what is new is only that the tactic block has two rewrites in it and that their order is again forced. The goal in that slot is <code>h = h₂.union h₁</code>. <code>rw [hu]</code> makes it <code>h₁.union h₂ = h₂.union h₁</code>; <code>union_comm hd</code> rewrites the left side to the right side, and <code>rw</code>\'s silent trailing <code>rfl</code> closes it.'},

    {t:'ex',
     id: 'm4-3',
     name: 'star_comm',
     why: 'One line of content, and it is the line where the partial commutative monoid of Module 2 becomes a law of the logic. Everything about the proof that is not <code>union_comm hd</code> is bookkeeping you have already done twice. It is cited five times in later Lean — once in Unit 17, three times in Unit 29 and once in Unit 34 — which makes it the most-used law on this page after monotonicity. Unit 17 permutes a three-way chain of stars using nothing but this law, associativity and monotonicity.',
     setup: 'You have <code>disjoint_symm</code> from Unit 08 and <code>union_comm</code> from Unit 10; the latter takes a disjointness proof as its argument.',
     goal: 'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by',
     hints: [
       'Unfolded, the goal says: if <code>h</code> splits into <code>h₁</code> and <code>h₂</code> with <code>P</code> on the left and <code>Q</code> on the right, then <code>h</code> splits into two pieces with <code>Q</code> on the left and <code>P</code> on the right. The two pieces you produce are the two you were given, exchanged.',
       'Take the star apart, then build a new one with the halves swapped. Four of the six slots are then hypotheses you already have, in a different order. The two that are not are the disjointness — which is stated in an order and so must be turned round — and the union equation, which is a statement about <code>h₂.union h₁</code> where you know something about <code>h₁.union h₂</code>.',
       'One <code>intro</code> with the six-name pattern, then one <code>exact</code> with a six-slot tuple. The two slots that need work want <code>disjoint_symm</code> and <code>union_comm</code>, and both take <code>hd</code>.',
       'After <code>intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩</code>, write <code>refine ⟨h₂, h₁, disjoint_symm hd, ?_, hq, hp⟩</code>. That fills five slots and leaves one goal, <code>h = h₂.union h₁</code>; close it by rewriting first with <code>hu</code> and then with <code>union_comm hd</code>. The corpus folds the same thing into a single <code>exact</code> by putting a <code>by</code> block in that slot.'
     ],
     sol: 'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩',
     solNote: 'One entailment, not an equivalence — but its converse is itself with <code>P</code> and <code>Q</code> exchanged, which is what makes <code>star_comm_iff</code> a two-character exercise in <code>x36</code>.',
     expl: 'A star asserts the existence of a cut. Exchanging the two halves of a cut gives a cut again, provided the two operations that mention order — <code>Heap.disjoint</code> and <code>Heap.union</code> — both survive the exchange. Unit 08 proved the first and Unit 10 proved the second, and the second needed the very hypothesis the star carries.',
     walk: [
       {tac:'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩', h:'Reduces the goal to <code>(Q ∗ P) σ h</code> and puts the premise\'s six components in the context. All six get real names this time: unlike in <code>m4-1</code> the disjointness fact is load-bearing, and an underscore would make it unreachable.'},
       {tac:'⟨h₂, h₁, …⟩', h:'Supplies the two witnesses in the other order, which discharges the goal\'s two existentials and instantiates the four conjuncts underneath them at <code>h₂</code> and <code>h₁</code>. No heap is constructed and none is modified; only the labels <i>left half</i> and <i>right half</i> move.'},
       {tac:'…, disjoint_symm hd, …', h:'Turns <code>h₁.disjoint h₂</code> into <code>h₂.disjoint h₁</code>. Without it the slot reports <code>The argument hd has type h₁.disjoint h₂ but is expected to have type h₂.disjoint h₁</code>.'},
       {tac:'…, by rw [hu, union_comm hd], …', h:'The goal here is <code>h = h₂.union h₁</code>. The first rewrite replaces <code>h</code> by <code>h₁.union h₂</code>; the second replaces that by <code>h₂.union h₁</code>; the trailing <code>rfl</code> that every <code>rw</code> attempts then closes the goal.'},
       {tac:'…, hq, hp⟩', h:'The two ownership facts, exchanged to match the exchanged halves.'}
     ],
     deep: [
       {t:'trace', title:'The equation slot on its own',
        start:'P Q : Assertion\n⊢ P ∗ Q ⊢ Q ∗ P',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩',
           state:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (Q ∗ P) σ h',
           h:'The goal displays folded, as a name applied to two arguments; underneath it is the six-slot existential.'},
          {tac:'refine ⟨h₂, h₁, disjoint_symm hd, ?_, hq, hp⟩',
           state:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ h = h₂.union h₁',
           h:'Five slots filled, one left open. This is the whole theorem, and it is an equation between heaps with no assertion anywhere in it.'},
          {tac:'rw [hu]',
           state:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ h₁.union h₂ = h₂.union h₁',
           h:'Now it is <code>union_comm</code>\'s statement, letter for letter, and <code>hd</code> is sitting in the context waiting to be its argument.'},
          {tac:'rw [union_comm hd]', state:'No goals.', h:'Rewrites the left side into the right side; the trailing <code>rfl</code> finishes.'}
        ],
        done:'The corpus writes the two rewrites as one tactic block inside the tuple.'},
       {t:'p', h:'Without <code>hd</code> the theorem is false, and Unit 14\'s deleted-disjointness connective is where you can watch it fail. <code>starNoDisj</code> is <code>∗</code> with the disjointness conjunct removed; two singletons at one address then satisfy it in one order and not the other, because a left-biased union keeps the left value.'},
       {t:'code', tag:'illustration', cap:'Commutativity refuted for the connective without disjointness. The premise is Unit 14\'s one-cell exhibit given a name; the refutation reads both sides at address 0 and finds <code>some 4</code> against <code>some 7</code>.',
        src:'theorem oneCellIsBoth :\n    Heap.singleton 0 4 = Heap.union (Heap.singleton 0 4) (Heap.singleton 0 7) := by\n  funext l\n  by_cases hl : l = 0\n  · rw [hl, union_of_some (Heap.singleton 0 7) (singleton_same 0 4), singleton_same]\n  · rw [union_of_none (Heap.singleton 0 7) (singleton_other 0 l 4 hl),\n        singleton_other 0 l 7 hl, singleton_other 0 l 4 hl]\n\nexample : ¬ (starNoDisj (0 ↦ 4) (0 ↦ 7) ⊢ starNoDisj (0 ↦ 7) (0 ↦ 4)) := by\n  intro hbad\n  obtain ⟨k₁, k₂, hu, h7, _⟩ :=\n    hbad (fun _ => 0) (Heap.singleton 0 4)\n      ⟨Heap.singleton 0 4, Heap.singleton 0 7, oneCellIsBoth, rfl, rfl⟩\n  subst h7\n  have := congrFun hu 0\n  rw [singleton_same, union_of_some k₂ (singleton_same 0 7)] at this\n  exact absurd this (by simp)'}
     ],
     pitfall: 'Filling the disjointness slot with <code>hd</code> rather than <code>disjoint_symm hd</code>. The message — <code>The argument hd has type h₁.disjoint h₂ but is expected to have type h₂.disjoint h₁</code> — is clear, but it arrives at the third slot and readers who wrote <code>⟨h₂, h₁, …⟩</code> a moment earlier tend to read it as a complaint about the witnesses. The other trap is reaching for <code>union_comm hd</code> before <code>hu</code>: <code>Did not find an occurrence of the pattern h₁.union h₂ in the target expression h = h₂.union h₁</code>, because the goal still mentions <code>h</code>.',
     variants: 'Drop <code>hd</code> from <code>union_comm</code>\'s statement and it stops being provable at all, which is Unit 10\'s result and not a fact about this page. Drop the disjointness conjunct from <code>∗</code> and this theorem is what breaks first — see the compiled refutation above, where the same one-cell heap satisfies the star in one order and not the other. Associativity, by contrast, survives that deletion untouched, because <code>union_assoc</code> carries no hypothesis; the two laws fail for genuinely different reasons, and Unit 16 says so.'},

    /* ============================================================== monotone === */

    {t:'sec', s:'Monotonicity: improving one side'},

    {t:'p', h:'Here is a question the laws so far cannot answer. You have proved <code>P ∗ Q</code> and you know <code>P ⊢ P\'</code>. Can you conclude <code>P\' ∗ Q</code> without knowing anything about <code>Q</code> at all? For classical conjunction the answer is yes, and the proof is Unit 12\'s projections and pairing. For a connective that divides memory it is not obvious: replacing one conjunct might demand a different cut, and the cut is shared.'},

    {t:'defn', term:'Monotonicity of a connective', h:'A binary connective <code>∘</code> is monotone when <code>P ⊢ P\'</code> and <code>Q ⊢ Q\'</code> together give <code>P ∘ Q ⊢ P\' ∘ Q\'</code>. It is the statement that the connective respects the order that <code>⊢</code> puts on assertions, and it is what lets you improve part of a formula in place instead of restating the whole of it.', cap:'The property, stated for an arbitrary connective, because the proof below uses nothing specific to <code>∗</code>.'},

    {t:'code', tag:'verified', cap:'Monotonicity and its two one-sided forms. The specialisations are term proofs: no <code>intro</code>, no tactic block, no heap.',
     src:'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\' := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩\n\ntheorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=\n  star_mono h (entails_refl Q)\n\ntheorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=\n  star_mono (entails_refl P) h'},

    {t:'p', h:'The answer to the question is that the cut does not have to change. The proof reuses <code>h₁</code>, <code>h₂</code>, <code>hd</code> and <code>hu</code> verbatim and only touches the last two slots, where each entailment is applied to a store, a heap and a proof — Unit 12\'s three arguments. It is the only law in the module whose proof names no lemma about heaps.'},

    {t:'p', h:'The two one-sided forms are the ones you actually reach for, and they are derived rather than proved: to leave one side alone, hand <code>star_mono</code> the identity entailment for it. <code>entails_refl Q</code> is that identity, and Unit 12 remarked that it is the identity function.'},

    {t:'ex',
     id: 'm4-5',
     name: 'star_mono and its two specialisations',
     hard: false,
     why: 'Monotonicity is what turns the laws on this page from a list into a calculus: with it you can rewrite one conjunct of a star and leave the rest of the formula untouched, which is what the verification proofs of Units 29 and 33 spend most of their lines doing. The two one-sided forms are cited nine times in later Lean — three of <code>star_mono_left</code> and six of <code>star_mono_right</code>, across Units 17, 29, 33 and 34 — while <code>star_mono</code> itself is never cited directly again, which is what deriving the specialisations is for. The first of those citations is Unit 17\'s <code>star_swap_middle</code>, which you cannot read yet because it also needs associativity. Deriving them rather than reproving them is also the pattern: three theorems, one proof.',
     setup: 'Nothing from Module 2 is needed. <code>entails_refl</code> is Unit 12\'s, and an entailment <code>h : P ⊢ P\'</code> is applied as <code>h σ h₁ hp</code>.',
     goal: 'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\' := by\n  sorry\n\ntheorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=\n  sorry\n\ntheorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=',
     hints: [
       'The premise gives you a cut of <code>h</code> with <code>P</code> on the left half and <code>Q</code> on the right. The goal asks for a cut of <code>h</code> with <code>P\'</code> on the left half and <code>Q\'</code> on the right. The two specialisations are the same statement with one side held still: <code>star_mono_left</code> wants <code>P ∗ Q ⊢ P\' ∗ Q</code> out of <code>P ⊢ P\'</code> alone, and <code>star_mono_right</code> is its mirror. No particular heap is named in any of the three, so ask first whether the cut has to change.',
       'It does not. Use the cut you were given, unchanged, and apply each entailment to the half it belongs to. For the two specialisations, an entailment that changes nothing is exactly what <code>entails_refl</code> is.',
       'One <code>intro</code> with the six-name pattern and one <code>exact</code> with a six-slot tuple whose first four entries are the names the pattern introduced. The specialisations are single applications of <code>star_mono</code>, written as terms after <code>:=</code> with no <code>by</code>.',
       'Start <code>exact ⟨h₁, h₂, hd, hu, ?, ?⟩</code>; the fifth slot wants <code>P\' σ h₁</code> and you have <code>hpq : P ⊢ P\'</code> and <code>hp : P σ h₁</code>, so it is <code>hpq σ h₁ hp</code>. Then <code>star_mono_left Q h</code> is <code>star_mono h (entails_refl Q)</code>.'
     ],
     sol: 'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\' := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩\n\ntheorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=\n  star_mono h (entails_refl Q)\n\ntheorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=\n  star_mono (entails_refl P) h',
     expl: 'An entailment does not change the heap it talks about; it changes what is claimed about that heap. So a proof that improves both conjuncts of a star can leave the decomposition exactly where it was, and the only slots that move are the two carrying the conjuncts. The one-sided forms follow by supplying the identity entailment on the side you do not want to touch.',
     walk: [
       {tac:'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩', h:'The usual opening: the goal drops to <code>(P\' ∗ Q\') σ h</code> and the six components land in the context. What matters is what the goal and the premise now share — the same <code>h</code>, and so the same admissible cut of it — which is why no lemma about <code>Heap.union</code> appears anywhere below.'},
       {tac:'⟨h₁, h₂, hd, hu, …⟩', h:'Four slots filled with the names as they came out of the pattern. The cut is reused verbatim, which is the theorem\'s entire mathematical content.'},
       {tac:'…, hpq σ h₁ hp, …', h:'Applies the left entailment at the left half. Unit 12 defined <code>⊢</code> as a function of a store, a heap and a proof, so this is three arguments and nothing more.'},
       {tac:'…, hrs σ h₂ hq⟩', h:'The same on the right, at the right half.'},
       {tac:'star_mono h (entails_refl Q)', h:'<code>star_mono_left</code>. Supplying <code>entails_refl Q</code> on the right says "and change nothing there"; the resulting type is <code>P ∗ Q ⊢ P\' ∗ Q</code>, with <code>Q</code> the same on both sides.'},
       {tac:'star_mono (entails_refl P) h', h:'<code>star_mono_right</code>, the mirror. The two are not proved; they are the general theorem with one argument fixed.'}
     ],
     deep: [
       {t:'trace', title:'Where the two entailments are spent',
        start:'P P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\n⊢ P ∗ Q ⊢ P\' ∗ Q\'',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩',
           state:'P P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (P\' ∗ Q\') σ h',
           h:'Two entailments in the context and four structural facts. The goal wants a star at the same <code>h</code>, so <code>hd</code> and <code>hu</code> can be handed straight back.'},
          {tac:'exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩', state:'No goals.',
           h:'Six slots: two heaps, two facts about them, and two applications. No rewriting anywhere, which is why this proof would read the same for any connective defined by a cut.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'illustration', cap:'What the one-sided forms are for: weakening a points-to to <code>aTrue</code> on the left of a star, with the right side untouched and unnamed. <code>trivial</code> is the proof of <code>True</code>, and <code>aTrue</code> is <code>True</code> at every store and heap, so the entailment handed to <code>star_mono_left</code> ignores all three of its arguments.',
        src:'example (l : Loc) (v : Val) (Q : Assertion) : (l ↦ v) ∗ Q ⊢ aTrue ∗ Q :=\n  star_mono_left Q (fun _ _ _ => trivial)'}
     ],
     pitfall: 'Applying an entailment to the wrong heap: <code>hpq σ h hp</code> instead of <code>hpq σ h₁ hp</code>. Lean reports <code>The argument hp has type P σ h₁ but is expected to have type P σ h</code> — the error is on <code>hp</code>, and the wrong thing is the argument before it. The rule of thumb is that the heap you pass an entailment is the heap its <i>premise</i> is about, not the heap the goal is about.',
     variants: 'Reverse one of the two hypotheses — take <code>hpq : P\' ⊢ P</code> — and the theorem is not harder but false, and it fails at the fifth slot, which needs <code>P\' σ h₁</code> and is offered a proof running the wrong way. The witness is one line of Module 3: put <code>P := aTrue</code> and <code>P\' := aFalse</code>, so that <code>P\' ⊢ P</code> holds vacuously, and take <code>Q = Q\' = aTrue</code>. Then <code>aTrue ∗ aTrue</code> holds at <code>Heap.empty</code> — cut it into <code>Heap.empty</code> and <code>Heap.empty</code> — while <code>aFalse ∗ aTrue</code> holds nowhere, since its left conjunct is <code>False</code>. Drop <code>hrs</code> and keep the conclusion <code>P ∗ Q ⊢ P\' ∗ Q\'</code> and the same thing happens one slot later, with the same witness on the other side. Weaken the conclusion to <code>P ∗ Q ⊢ P\' ∗ Q</code> and <code>hrs</code> stops being needed at all, which is the specialisation. And monotonicity has no converse: from <code>P ∗ Q ⊢ P\' ∗ Q\'</code> you cannot recover <code>P ⊢ P\'</code>, because <code>Q := aFalse</code> makes both stars unsatisfiable and the entailment between them holds for every <code>P</code> and <code>P\'</code> whatever.'},

    /* =========================================================== distribute === */

    {t:'sec', s:'Distribution over ∨ and ∃'},

    {t:'p', h:'The last two laws are about a star whose left conjunct is a disjunction or an existential. Both proofs are the same shape: take the star apart, take the disjunction or existential apart, and rebuild the star <b>with the same cut</b> inside each case. Nothing about heaps is used, because nothing about heaps changes.'},

    {t:'code', tag:'verified', cap:'Distribution over <code>∨</code>, and the <code>∃</code> case. In both, the six components handed out by the pattern are handed straight back.',
     src:'theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩\n  rcases hpq with hp | hq\n  · exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩\n  · exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by\n  intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩\n  exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩'},

    {t:'p', h:'<code>star_exists_left</code> is where Unit 12\'s <code>Sort u</code> stops being free generality and does something: <code>α</code> is the type the existential ranges over, and it is unconstrained, so the same theorem covers a witness that is a heap, a value, an address, or a proof. The witness travels from the premise to the conclusion and the cut is untouched — which is the whole of it. The reverse direction holds too, by the same three lines with the tuple rearranged, and Unit 17 sets it; that is not automatic, and the <code>∀</code> case below is where the same move fails.'},

    {t:'p', h:'The <code>∃</code> case is the one to remember. Unit 33 defines a list segment by recursion, so the assertion for a non-empty segment is an existential over the next address, and every proof about it opens by pulling that existential out through a star. Both of that unit\'s two main theorems open their inductive step with it.'},

    {t:'ex',
     id: 'm4-6',
     name: 'star_or_left / star_exists_left',
     why: 'These are the first laws that take something apart <i>inside</i> a star and rebuild it, and they establish the habit that makes the rest possible: the cut you were handed is the cut you give back. <code>star_exists_left</code> opens the inductive step of both list theorems in Unit 33 — literally the first line of one and the second line of the other — and is the reason those proofs are readable at all. It is cited twice there and nowhere else, which is a small number for a theorem that carries a whole unit\'s proofs. <code>star_or_left</code> is the case-split half of the same skill; no later proof in the corpus uses it, and it earns its place by being the drill that makes the existential version readable.',
     setup: 'Unit 12\'s <code>aOr</code> and <code>aExists</code>. <code>rcases</code> splits a disjunction into two goals; an existential can be destructured directly inside the <code>intro</code> pattern.',
     goal: 'theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by\n  sorry\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by',
     hints: [
       'For the first: the premise is a star whose left conjunct is a disjunction, so after destructuring you hold a cut plus a proof of <code>P</code> or a proof of <code>Q</code>, at the left half. The goal is a disjunction of two stars. For the second: the left conjunct is an existential, so you hold a witness <code>x</code> and a proof of <code>P x</code> at the left half, and the goal is an existential whose body is a star.',
       'In both cases the decomposition of <code>h</code> is the same before and after; only the assertion at the left half changes. So the argument is: destructure, choose the branch or supply the witness, rebuild with the identical two heaps.',
       '<code>rcases … with … | …</code> for the disjunction, then <code>Or.inl</code> and <code>Or.inr</code> to choose the branch of the goal. For the existential, put a nested pattern in the fifth slot of the <code>intro</code> pattern and put the witness first in the tuple you build.',
       'For the first theorem, <code>intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩</code> leaves <code>hpq : aOr P Q σ h₁</code> and the goal <code>aOr (P ∗ R) (Q ∗ R) σ h</code>; split <code>hpq</code> and each branch is one <code>exact</code>. For the second, <code>intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩</code> takes the star and the existential apart in one move, leaving the goal <code>aExists (fun x => P x ∗ Q) σ h</code>, and the proof is a seven-slot tuple beginning with <code>x</code>.'
     ],
     sol: 'theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩\n  rcases hpq with hp | hq\n  · exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩\n  · exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by\n  intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩\n  exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩',
     solNote: 'The two branches of <code>star_or_left</code> differ in three characters: <code>inl</code> against <code>inr</code>, and <code>hp</code> against <code>hq</code>.',
     expl: 'A star and a disjunction commute because the cut is chosen before the branch is: whichever side of the disjunction holds, it holds at the same left half, so the same two heaps rebuild the star in either branch. A star and an existential commute for the same reason with the branch replaced by a witness, and the witness moves to the front of the tuple.',
     walk: [
       {tac:'intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩', h:'Leaves the goal <code>aOr (P ∗ R) (Q ∗ R) σ h</code> — a disjunction at the whole heap — and puts a disjunction at the <i>left half</i> into the context as <code>hpq : aOr P Q σ h₁</code>. The two disjunctions are at different heaps, and that gap is the theorem.'},
       {tac:'rcases hpq with hp | hq', h:'Replaces the one disjunctive hypothesis by two goals, one per disjunct, with <code>hpq</code> gone and <code>hp : P σ h₁</code> or <code>hq : Q σ h₁</code> in its place at the end of the context. The goal itself is untouched in both, which is what makes the two branches copies of each other.'},
       {tac:'· exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩', h:'Chooses the left disjunct of the goal, then builds the star with the cut untouched. <code>Or.inl</code> is Unit 01\'s.'},
       {tac:'· exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩', h:'The mirror. The tuple is the same except that the fifth entry is now the proof of <code>Q</code>.'},
       {tac:'intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩', h:'The second theorem\'s opening. The nested pattern in the fifth slot opens the existential in the same breath as the star, so instead of one hypothesis <code>aExists P σ h₁</code> the context gains two: <code>x : α</code> and <code>hp : P x σ h₁</code>. The goal is the existential <code>aExists (fun x => P x ∗ Q) σ h</code>, whose bound variable is a different <code>x</code> from the one now in the context.'},
       {tac:'exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩', h:'Seven slots: the witness for the outer existential, then the six of the star. The witness goes first because the goal\'s outermost binder is the existential.'}
     ],
     deep: [
       {t:'trace', title:'star_or_left, one branch',
        start:'P Q R : Assertion\n⊢ aOr P Q ∗ R ⊢ aOr (P ∗ R) (Q ∗ R)',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩',
           state:'P Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhpq : aOr P Q σ h₁\nhr : R σ h₂\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
           h:'The disjunction is at <code>h₁</code>, not at <code>h</code>. That is what makes the rebuild possible with the same cut.'},
          {tac:'rcases hpq with hp | hq',
           state:'case inl\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhr : R σ h₂\nhp : P σ h₁\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
           h:'The first of two goals. <code>hpq</code> is gone and <code>hp : P σ h₁</code> has taken its place at the end of the context; the goal is untouched.'},
          {tac:'exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩', state:'case inr\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhr : R σ h₂\nhq : Q σ h₁\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
           h:'Closing the first branch leaves the second, and printed in full it differs from the first in exactly one line: <code>hq : Q σ h₁</code> where <code>hp : P σ h₁</code> stood. Same cut, same goal, other disjunct.'}
        ],
        done:'The second branch is the first with inl and hp replaced by inr and hq.'},
       {t:'trace', title:'star_exists_left, where the witness goes',
        start:'α : Sort u\nP : α → Assertion\nQ : Assertion\n⊢ aExists P ∗ Q ⊢ aExists fun x => P x ∗ Q',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩',
           state:'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nx : α\nhp : P x σ h₁\nhq : Q σ h₂\n⊢ aExists (fun x => P x ∗ Q) σ h',
           h:'<code>α : Sort u</code> at the top of the context is the universe-polymorphic binder from Unit 12\'s <code>aExists</code>; <code>x : α</code> is the witness the premise carried, now named. The bound <code>x</code> in the goal is a different variable and Lean is content.'},
          {tac:'exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩', state:'No goals.',
           h:'One tuple, seven entries, none of them constructed: the witness and the six components came out of the premise unchanged.'}
        ],
        done:'No goals.'}
     ],
     pitfall: 'In <code>star_exists_left</code>, giving the tuple in the star\'s order and putting the witness where the existential in the premise had it: <code>⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩</code>. The goal\'s outermost binder is the existential over <code>α</code>, so the first entry must be the witness, and Lean says so in a message that is the first sighting of what <code>Sort u</code> buys: <code>The argument h₁ has type Heap of sort `Type` but is expected to have type α of sort `Sort u`</code>. In <code>star_or_left</code>, the corresponding slip is forgetting the <code>rcases</code> and offering <code>hpq</code> where a proof of <code>P</code> is wanted: <code>The argument hpq has type aOr P Q σ h₁ but is expected to have type P σ h₁</code>.',
     variants: 'Move the disjunction to the right conjunct — <code>R ∗ (aOr P Q) ⊢ aOr (R ∗ P) (R ∗ Q)</code> — and nothing changes but the names: the same <code>rcases</code>, the same two tuples, with the hypothesis that gets split now sitting at <code>h₂</code> instead of <code>h₁</code>. Replace <code>aOr</code> by <code>aAnd</code> and this direction is still provable, in one <code>exact</code> with two tuples, because the same cut serves both conjuncts; but the direction you would actually want, pulling a conjunction <i>out</i> of a star, is false, and the retrospective below gives the counterexample. Replace <code>aExists</code> by the universal quantifier and the same asymmetry appears, for the same reason.'},

    {t:'detail', title:'∀ and ∃ are not the same case, and the reason is the order of the quantifier and the cut', tag:'aside', open:false, blocks:[
      {t:'p', h:'A universal quantifier over assertions lifts pointwise the way <code>aExists</code> did, and one of its two directions goes through by almost the same proof. The other does not, and the gap between them is what this fold is for.'},
      {t:'code', tag:'verified', cap:'The universal lift, and the direction that works.',
       src:'def aForall {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∀ x, P x σ h\n\ntheorem star_forall_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aForall P ∗ Q ⊢ aForall (fun x => P x ∗ Q) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩ x\n  exact ⟨h₁, h₂, hd, hu, hp x, hq⟩'},
      {t:'p', h:'That <code>intro</code> takes four things: the store, the heap, the six-name pattern, and then <code>x</code>, because the goal left after the premise is itself a <code>∀</code>. The proof works because there is <i>one</i> cut, fixed before <code>x</code> is chosen, and it serves every <code>x</code> at once.'},
      {t:'state', cap:'The goal after that <code>intro</code>. One cut in the context, one arbitrary <code>x</code>, and a star to build.',
       src:'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : aForall P σ h₁\nhq : Q σ h₂\nx : α\n⊢ (P x ∗ Q) σ h'},
      {t:'p', h:'Now run it backwards. The premise <code>aForall (fun x => P x ∗ Q) σ h</code> says: for every <code>x</code> there is a cut making <code>P x</code> and <code>Q</code> true on its two halves. The cut is <i>inside</i> the quantifier, so it may depend on <code>x</code>. The conclusion needs a single cut that works for all of them, and nothing supplies one.'},
      {t:'state', cap:'The goal at the start of the failing direction. There is nothing in the context to destructure until an <code>x</code> is supplied, and supplying one produces a cut that is only good for that <code>x</code>.',
       src:'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh : Heap\nhall : aForall (fun x => P x ∗ Q) σ h\n⊢ (aForall P ∗ Q) σ h'},
      {t:'p', h:'That is an argument, not a proof of falsity, and the difference matters — refuting the direction costs a witness. The corpus supplies one: a family of two assertions indexed by <code>Bool</code>, claiming a different address for each index.'},
      {t:'code', tag:'verified', cap:'The counterexample. <code>Pcx false</code> owns address 0 and <code>Pcx true</code> owns address 1; the heap holds both.',
       src:'def Pcx : Bool → Assertion\n  | false => (0 ↦ 4)\n  | true  => (1 ↦ 7)\n\ntheorem star_forall_right_fails :\n    ¬ (aForall (fun x => Pcx x ∗ aTrue) ⊢ aForall Pcx ∗ aTrue) := by\n  intro hcontra\n  have hlhs : aForall (fun x => Pcx x ∗ aTrue) (fun _ => 0)\n      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) := by\n    intro x\n    cases x with\n    | false =>\n        exact ⟨Heap.singleton 0 4, Heap.singleton 1 7,\n          singleton_disjoint 4 7 (by simp), rfl, rfl, trivial⟩\n    | true =>\n        refine ⟨Heap.singleton 1 7, Heap.singleton 0 4,\n          singleton_disjoint 7 4 (by simp), ?_, rfl, trivial⟩\n        exact union_comm (singleton_disjoint 4 7 (by simp))\n  obtain ⟨h₁, h₂, _, _, hall, _⟩ := hcontra _ _ hlhs\n  have e0 : h₁ = Heap.singleton 0 4 := hall false\n  have e1 : h₁ = Heap.singleton 1 7 := hall true\n  have : Heap.singleton 0 4 0 = Heap.singleton 1 7 0 := by rw [← e0, ← e1]\n  rw [singleton_same, singleton_other 1 0 7 (by simp)] at this\n  exact absurd this (by simp)'},
      {t:'p', h:'<code>Bool</code> is Lean\'s two-element type, with constructors <code>false</code> and <code>true</code>, and <code>cases x with | false => … | true => …</code> splits on which one <code>x</code> is. It is the only construct here that has not been used already, and it appears nowhere else in this unit.'},
      {t:'p', h:'The two halves of the proof are worth separating. <code>hlhs</code> proves the premise, and it does so with <b>two different cuts</b> — for <code>false</code> the owned cell is on the left, for <code>true</code> it is on the right, and the second needs <code>union_comm</code> to put the same heap back together the other way round. That is precisely the freedom the left-hand side has. The rest of the proof then shows the conclusion has no such freedom: whatever single <code>h₁</code> the conclusion offers must equal <code>Heap.singleton 0 4</code> and equal <code>Heap.singleton 1 7</code>, and reading both at address 0 gives <code>some 4 = some 7</code>.'},
      {t:'p', h:'So: <code>∗</code> commutes with <code>∃</code> in both directions and with <code>∀</code> in one. The discriminator is whether the cut is chosen once or once per index.'}
    ]},

    /* =============================================================== package === */

    {t:'sec', s:'Packaging, and rewriting inside a star'},

    {t:'p', h:'Four of the laws above come in pairs pointing opposite ways, and Unit 12 gave the notation for that: <code>P ⊣⊢ Q</code> is a pair of entailments, and nothing more. Turning <code>m4-1</code> and <code>m4-2</code> into <code>emp ∗ P ⊣⊢ P</code> is a matter of writing the pair down.'},

    {t:'p', h:'Monotonicity says a star respects <code>⊢</code>; applying it to both halves of a <code>⊣⊢</code> says a star respects <code>⊣⊢</code>, which is congruence: you may replace either conjunct by an equivalent one, in place, without touching the rest. That is the difference between a list of laws and an algebra you can compute in.'},

    {t:'ex',
     id: 'x36',
     name: 'star_emp_left_iff / star_emp_right_iff / star_comm_iff / star_congr',
     why: 'Every theorem on this page is an entailment, and the four here are the equivalences hiding in them. The last, <code>star_congr</code>, is the one that changes how the laws read: with it a chain of stars can be simplified conjunct by conjunct, the way you would rewrite inside a sum. Being honest about the accounting: none of these four is cited by name anywhere later in the course — the corpus reaches for the entailments directly, as it does for Unit 12\'s <code>equiv_*</code>. What they buy is the reader\'s model. A law you can only apply to a whole formula is plumbing; a law you can apply inside one is algebra, and the four lines here are the difference.',
     setup: 'All four are one-line terms. <code>⊣⊢</code> is a pair, so <code>⟨…, …⟩</code> builds one and <code>.1</code> and <code>.2</code> take one apart; Unit 12\'s <code>equiv_refl</code> is available but not needed here.',
     goal: 'theorem star_emp_left_iff (P : Assertion) : emp ∗ P ⊣⊢ P :=\n  sorry\n\ntheorem star_emp_right_iff (P : Assertion) : P ∗ emp ⊣⊢ P :=\n  sorry\n\ntheorem star_comm_iff (P Q : Assertion) : P ∗ Q ⊣⊢ Q ∗ P :=\n  sorry\n\ntheorem star_congr {P P\' Q Q\' : Assertion} (hp : P ⊣⊢ P\') (hq : Q ⊣⊢ Q\') :\n    P ∗ Q ⊣⊢ P\' ∗ Q\' :=',
     hints: [
       '<code>P ⊣⊢ Q</code> unfolds to <code>P ⊢ Q ∧ Q ⊢ P</code>. Each of the first three is therefore a pair of theorems you have already proved; the fourth is a pair of applications of one theorem you have already proved.',
       'For commutativity the two directions are the same theorem at different arguments. For congruence, the first component improves left-to-right and the second improves right-to-left, so the two halves of each hypothesis are used in opposite directions.',
       '<code>⟨…, …⟩</code> for each, with <code>star_emp_left</code>, <code>star_emp_left_intro</code>, <code>star_comm</code> and <code>star_mono</code> as the entries. The projections <code>.1</code> and <code>.2</code> take the two directions out of a hypothesis that is itself a <code>⊣⊢</code>.',
       '<code>star_emp_left_iff P</code> is <code>⟨star_emp_left P, star_emp_left_intro P⟩</code>. For <code>star_comm_iff P Q</code> the second entry is <code>star_comm Q P</code>, not <code>star_comm P Q</code>. For <code>star_congr</code> the second entry is <code>star_mono hp.2 hq.2</code>.'
     ],
     sol: 'theorem star_emp_left_iff (P : Assertion) : emp ∗ P ⊣⊢ P :=\n  ⟨star_emp_left P, star_emp_left_intro P⟩\n\ntheorem star_emp_right_iff (P : Assertion) : P ∗ emp ⊣⊢ P :=\n  ⟨star_emp_right P, star_emp_right_intro P⟩\n\ntheorem star_comm_iff (P Q : Assertion) : P ∗ Q ⊣⊢ Q ∗ P :=\n  ⟨star_comm P Q, star_comm Q P⟩\n\ntheorem star_congr {P P\' Q Q\' : Assertion} (hp : P ⊣⊢ P\') (hq : Q ⊣⊢ Q\') :\n    P ∗ Q ⊣⊢ P\' ∗ Q\' :=\n  ⟨star_mono hp.1 hq.1, star_mono hp.2 hq.2⟩',
     expl: 'An equivalence between assertions is a pair of entailments, so packaging one is writing a pair. The only place where thought is required is the second component, which always runs the other way: for commutativity that means the same theorem with its arguments exchanged, and for congruence it means the second halves of both hypotheses.',
     walk: [
       {tac:'⟨star_emp_left P, star_emp_left_intro P⟩', h:'Discharges both components at once. <code>⊣⊢</code> is a conjunction of two entailments, so the goal splits into <code>emp ∗ P ⊢ P</code> and <code>P ⊢ emp ∗ P</code> — which are, in that order, the two theorems of <code>m4-1</code> and <code>m4-2</code> at the argument <code>P</code>. Left-to-right goes first, because that is the order <code>AssertionEquiv</code> writes them in.'},
       {tac:'⟨star_emp_right P, star_emp_right_intro P⟩', h:'The same two goals with <code>emp</code> on the other side, closed by the halves of <code>m4-1</code> and <code>m4-2</code> you wrote yourself.'},
       {tac:'⟨star_comm P Q, star_comm Q P⟩', h:'Commutativity is its own converse. Swapping the arguments turns <code>P ∗ Q ⊢ Q ∗ P</code> into <code>Q ∗ P ⊢ P ∗ Q</code>, which is the second component\'s type exactly.'},
       {tac:'⟨star_mono hp.1 hq.1, star_mono hp.2 hq.2⟩', h:'The first component improves both conjuncts forwards; the second improves both backwards. <code>hp.1 : P ⊢ P\'</code> and <code>hp.2 : P\' ⊢ P</code>, so each half of the pair is monotonicity applied in one direction.'}
     ],
     deep: [
       {t:'trace', title:'What ⊣⊢ splits into',
        start:'P Q : Assertion\n⊢ P ∗ Q ⊣⊢ Q ∗ P',
        steps:[
          {tac:'constructor',
           state:'case left\nP Q : Assertion\n⊢ P ∗ Q ⊢ Q ∗ P\n\ncase right\nP Q : Assertion\n⊢ Q ∗ P ⊢ P ∗ Q',
           h:'The two goals of <code>star_comm_iff</code>, printed together. They are the same statement at exchanged arguments, which is why one theorem closes both. The corpus writes the pair as a term and never runs <code>constructor</code>; this is what the term is filling.'}
        ],
        done:'· exact star_comm P Q   · exact star_comm Q P'},
       {t:'trace', title:'And for star_congr',
        start:'P P\' Q Q\' : Assertion\nhp : P ⊣⊢ P\'\nhq : Q ⊣⊢ Q\'\n⊢ P ∗ Q ⊣⊢ P\' ∗ Q\'',
        steps:[
          {tac:'constructor',
           state:'case left\nP P\' Q Q\' : Assertion\nhp : P ⊣⊢ P\'\nhq : Q ⊣⊢ Q\'\n⊢ P ∗ Q ⊢ P\' ∗ Q\'\n\ncase right\nP P\' Q Q\' : Assertion\nhp : P ⊣⊢ P\'\nhq : Q ⊣⊢ Q\'\n⊢ P\' ∗ Q\' ⊢ P ∗ Q',
           h:'Read the two goals against the hypotheses. The first wants the forward halves, <code>hp.1</code> and <code>hq.1</code>; the second wants the backward halves. Both are <code>star_mono</code>.'}
        ],
        done:'· exact star_mono hp.1 hq.1   · exact star_mono hp.2 hq.2'},
       {t:'code', tag:'illustration', cap:'What congruence is for: two <code>emp</code>s deleted from the middle of a formula, in one term, with neither conjunct unfolded.',
        src:'example (P Q : Assertion) : (emp ∗ P) ∗ (Q ∗ emp) ⊣⊢ P ∗ Q :=\n  star_congr (star_emp_left_iff P) (star_emp_right_iff Q)'}
     ],
     pitfall: 'Writing <code>⟨star_comm P Q, star_comm P Q⟩</code> for <code>star_comm_iff</code>. The type of the second component is <code>Q ∗ P ⊢ P ∗ Q</code>, and Lean prints both types: <code>The last star_comm P Q argument has type P ∗ Q ⊢ Q ∗ P but is expected to have type Q ∗ P ⊢ P ∗ Q</code>. A symmetric theorem is not the same as a theorem that is its own converse at the same arguments, and the fix is to swap them.',
     variants: 'Weaken <code>star_congr</code>\'s hypotheses to entailments and you get <code>star_mono</code> back, so nothing is lost — but you can no longer use the result to rewrite, because rewriting needs to travel in both directions. Keep one hypothesis an equivalence and make the other an entailment and the theorem is unprovable as stated: the backward component would need the missing direction. Ask for the converse of <code>star_congr</code> — from <code>P ∗ Q ⊣⊢ P\' ∗ Q\'</code> conclude <code>P ⊣⊢ P\'</code> — and it fails for the reason <code>m4-5</code>\'s variants gave, with a witness you can write down: put <code>Q = Q\' = aFalse</code>. A star whose right conjunct is <code>aFalse</code> holds at no heap, so both entailments of the premise are vacuous and <code>P ∗ aFalse ⊣⊢ P\' ∗ aFalse</code> holds for every pair — including <code>aTrue</code> and <code>aFalse</code>, which are not equivalent at <code>Heap.empty</code> or anywhere else.'},

    /* ================================================================ close === */

    {t:'sec', s:'The projection, refuted once and for all'},

    {t:'p', h:'Unit 14 refuted <code>P ∗ Q ⊢ P</code> for two named assertions by finding the address where it fails. With the unit law in hand the general statement can be proved instead, and the proof needs no addresses at all: if the rule held for every pair, it would hold for <code>emp</code> and <code>0 ↦ 0</code>, and composing it with the intro law would give <code>(0 ↦ 0) ⊢ emp</code>, which Unit 13 already refuted.'},

    {t:'code', tag:'verified', cap:'Weakening, refuted in general. Four lines, and the only heap mentioned is a single cell chosen because Unit 13 has a theorem about it.',
     src:'theorem star_not_weakening : ¬ (∀ P Q : Assertion, P ∗ Q ⊢ P) := by\n  intro hbad\n  have h : (emp ∗ (0 ↦ 0)) ⊢ emp := hbad emp (0 ↦ 0)\n  have h2 : (0 ↦ 0) ⊢ emp := entails_trans (star_emp_left_intro _) h\n  exact pointsTo_not_emp 0 0 h2'},

    {t:'p', h:'The third line is the first chain in the course: two entailments composed with <code>entails_trans</code>, in term mode, with no <code>intro</code> and no heap. <code>star_emp_left_intro _</code> goes from <code>0 ↦ 0</code> to <code>emp ∗ (0 ↦ 0)</code>, the assumed rule goes from there to <code>emp</code>, and the composite is what Unit 13 says cannot exist. Unit 17\'s <code>star_swap_middle</code> is two of these nested inside each other and nothing else: four theorem names, two of them from this page and two from associativity, no <code>by</code> and no heap.'},

    /* ======================================================== retrospective === */

    {t:'sec', s:'Retrospective'},

    {t:'p', h:'Three questions. The answers are behind the folds, and are worth attempting first.'},

    {t:'detail', title:'Which of these laws are equivalences, and which are only entailments?', tag:'aside', open:false, blocks:[
      {t:'p', h:'The unit laws and commutativity are equivalences, and <code>x36</code> packaged all three. Distribution over <code>∨</code> and over <code>∃</code> are equivalences too, but only their left-to-right halves are proved here; the converses are Unit 17\'s, and the reason they are set separately is that a reader who has written <code>star_or_left</code> should discover for themselves that running it backwards is possible.'},
      {t:'p', h:'The universal case is a strict entailment: one direction is <code>star_forall_left</code> and the other is refuted by <code>star_forall_right_fails</code>. And monotonicity is not an entailment at all — it is a rule, taking two entailments and producing a third. Asking whether it is an equivalence is a category error, though there is a related question with a real answer: from <code>P ∗ Q ⊢ P\' ∗ Q\'</code> you cannot recover <code>P ⊢ P\'</code>, so the rule has no converse.'}
    ]},

    {t:'detail', title:'Where exactly did union_comm\'s disjointness hypothesis end up in star_comm?', tag:'aside', open:false, blocks:[
      {t:'p', h:'It came out of the star\'s own third slot, as <code>hd</code>, and it was spent twice in adjacent positions: once as <code>disjoint_symm hd</code>, filling the new star\'s disjointness conjunct, and once as the argument of <code>union_comm hd</code> inside the equation slot. One hypothesis, two uses, and it never leaves the proof.'},
      {t:'p', h:'That is the general pattern for this connective, and it is worth naming. On paper a separating conjunction carries a side condition that is invisible because <code>⊎</code> hides it. In Lean it is a named hypothesis in a slot, and every law whose heap-level counterpart needs disjointness gets it from there rather than from an assumption on the theorem. It is why none of the theorems on this page takes a disjointness argument, even though <code>union_comm</code> does.'}
    ]},

    {t:'detail', title:'Why is there no star_and_left?', tag:'aside', open:false, blocks:[
      {t:'p', h:'The direction the name suggests is provable, in one <code>exact</code>: the same cut serves both conjuncts, so each is rebuilt against it.'},
      {t:'code', tag:'illustration', cap:'The <code>∧</code> analogue of <code>star_or_left</code>. Two tuples over one cut.',
       src:'example (P Q R : Assertion) : (aAnd P Q) ∗ R ⊢ aAnd (P ∗ R) (Q ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, ⟨hp, hq⟩, hr⟩\n  exact ⟨⟨h₁, h₂, hd, hu, hp, hr⟩, ⟨h₁, h₂, hd, hu, hq, hr⟩⟩'},
      {t:'p', h:'It is not in the corpus because it is never the direction anyone wants. Normalising an assertion means pulling structure <i>out</i> of a star so that the star can be attacked conjunct by conjunct, and for <code>∨</code> and <code>∃</code> that direction exists. For <code>∧</code> it does not, and the reason is the one the <code>∀</code> fold already gave: a conjunction is a universal quantifier over a two-element type, so the two conjuncts may hold at two different cuts and there need be no single cut serving both.'},
      {t:'code', tag:'illustration', cap:'The counterexample, which is <code>star_forall_right_fails</code> with the quantifier written out. <code>Pcx false</code> owns address 0 and <code>Pcx true</code> owns address 1, and the two stars use opposite cuts of the same two-cell heap.',
       src:'example : ¬ (∀ P Q R : Assertion, aAnd (P ∗ R) (Q ∗ R) ⊢ (aAnd P Q) ∗ R) := by\n  intro hbad\n  have hlhs : aAnd (Pcx false ∗ aTrue) (Pcx true ∗ aTrue) (fun _ => 0)\n      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) := by\n    constructor\n    · exact ⟨Heap.singleton 0 4, Heap.singleton 1 7,\n        singleton_disjoint 4 7 (by simp), rfl, rfl, trivial⟩\n    · refine ⟨Heap.singleton 1 7, Heap.singleton 0 4,\n        singleton_disjoint 7 4 (by simp), ?_, rfl, trivial⟩\n      exact union_comm (singleton_disjoint 4 7 (by simp))\n  obtain ⟨h₁, h₂, _, _, ⟨e0, e1⟩, _⟩ := hbad (Pcx false) (Pcx true) aTrue _ _ hlhs\n  have : Heap.singleton 0 4 0 = Heap.singleton 1 7 0 := by rw [← e0, ← e1]\n  rw [singleton_same, singleton_other 1 0 7 (by simp)] at this\n  exact absurd this (by simp)'},
      {t:'p', h:'Unit 17 answers the question the reader should ask next: if a conjunction cannot be pulled out of a star, how do you attach an ordinary fact — one that owns no memory — to a separating conjunction at all?'}
    ]},

    {t:'dod', h:'You can prove both unit laws and both converses and say why they are four theorems rather than two; choose a forced cut by reading the conjuncts backwards; decide whether an equation slot wants <code>.symm</code> by reading the two types in the error rather than the lemma\'s name, and name the one law where dropping it is silently harmless; prove commutativity and point at both places <code>hd</code> is spent; prove monotonicity, derive its two one-sided forms as term proofs, and say why the proof mentions no heap lemma; prove distribution over <code>∨</code> and <code>∃</code> with the cut handed back unchanged; package a pair of entailments as a <code>⊣⊢</code> and rewrite inside a star with <code>star_congr</code>; and say why <code>∗</code> commutes with <code>∃</code> in both directions and with <code>∀</code> in one.'},

    {t:'p', h:'Unit, commutative, monotone, distributive. One law is missing, and it is the one that lets you stop thinking about a <i>tree</i> of stars and start thinking about a <i>list</i> of owned resources. It is also the only one whose proof has to manufacture hypotheses — but Unit 11 already did that work.'}

  ]
});
