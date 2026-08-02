registerChapter({
  id: 'small-footprint',
  num: '23',
  phase: 'Phase 4 · The program logic',
  title: 'Rules that mention only what they touch',
  blurb: 'Three rules for the three memory commands, each stated on exactly the cells its command touches. Then two multi-command programs: one that composes out of them, and one that does not.',

  orient: {
    youWill: [
      'State a rule whose precondition is a single cell, and say what that commits you to about every other cell.',
      'Say why <code>{ l ↦ v } free(l) { emp }</code> is a theorem under Unit 13&rsquo;s reading of <code>↦</code> and is refuted by a heap from Unit 07 under the other one.',
      'Choose between <code>fact</code> and <code>pure</code> in a postcondition by asking which of them lets the heap grow.',
      'Prove the load rule by naming the cut of the final heap — and see that the cut has only one candidate.',
      'Prove the write and free rules, each in one line of real content, and name the Unit 06 equation that line is.',
      'Compose two triples with <code>hoare_seq</code> when the first rule&rsquo;s postcondition is on the nose the second rule&rsquo;s precondition, and watch the same move fail when it carries one conjunct more.',
      'Build a two-command derivation by hand out of <code>Exec.seq</code>, and say exactly which step of the failed composition forced you to.'
    ],
    needs: [
      'Unit 22: <code>Hoare</code>, <code>hoare_seq</code>, and that proving a triple means <i>building</i> a derivation and naming the final state.',
      'Unit 19: <code>Exec</code>&rsquo;s <code>load</code>, <code>write</code>, <code>free</code> and <code>seq</code> rules, and that each of the first three carries a lookup premise.',
      'Unit 13: <code>↦</code> as an equation on the heap, and <code>emp</code>. Unit 17: <code>pure</code>, and that <code>pure φ ∗ P</code> and <code>aAnd (fact φ) P</code> entail each other.',
      'Unit 06: <code>write_singleton</code> and <code>erase_singleton</code>. Unit 07: exercises <code>x16</code> and <code>x18</code>, and the heap <code>twoCells</code>.'
    ],
    payoff: 'These are the first rules in the course that mention an address, and every specification of a program after this page is built from them or from a generalisation of one of them. They are also, on their own, almost useless: the last exercise here is a two-command program whose proof cannot be assembled out of them, and the gap it opens is what Module 6 spends five units closing.'
  },

  blocks: [

    /* =================================================== the principle === */

    {t:'p', h:'How much memory should a rule mention? Each of the three commands that touch the heap touches exactly one cell. So a rule about one of them has one cell it cannot avoid speaking about, and the whole of the rest of memory to make a decision about.'},

    {t:'p', h:'Take <code>x := [l]</code>. It faults unless <code>l</code> is allocated, so the precondition has to guarantee that much. Unit 07 put two candidates in front of you: <i>the heap has <code>v</code> at <code>l</code></i>, and <i>the heap is the single cell <code>l</code> holding <code>v</code></i>. Unit 13 took the second and wrote it <code>l ↦ v</code>. Use it as a precondition and the rule commits to something much stronger than <i>the load will not fault</i>: it commits to being applied only in a world containing nothing else.'},

    {t:'p', h:'That sounds like a rule nobody could use. Nearly every real heap has other cells in it. The bet is that the missing generality can be recovered once, by a single structural rule, instead of being written into every specification — and the rest of this unit is the setting up of that bet.'},

    {t:'txt', cap:'The three rules, in the notation Unit 18 gave the commands. Each precondition is one cell; each postcondition describes the whole of the memory that cell became. Nothing else in the heap appears, in any of the six slots.',
     src:"   { l ↦ v }      x := [l]      { x = v  ∗  l ↦ v }\n\n   { l ↦ old }    [l] := e      { l ↦ e }\n\n   { l ↦ v }      free(l)       { emp }"},

    {t:'defn', term:'Small-footprint specification',
     h:'A specification whose precondition owns exactly the cells the command touches, and whose postcondition describes exactly what those cells became. The <i>footprint</i> is Unit 07&rsquo;s word: the part of memory the assertion pins down. A small-footprint rule pins down the part the command reads or changes, and says nothing at all about the rest — not that it is absent, not that it is unchanged, nothing.',
     cap:'The term names a style of specification, not a new construct. All three rules above are in it; none of the four rules of Unit 22 is, because none of them mentions memory at all.'},

    {t:'p', h:'The alternative is to make the precondition big and add side conditions. A write rule in that style says: <i>for any heap in which <code>l</code> is allocated, after <code>[l] := e</code> the heap is the same everywhere except at <code>l</code>, where it holds <code>e</code></i>. That rule is true, and stating it costs a universally quantified address and a disequality — the same disequality Unit 00 added to the aliased triple on its opening page, and the same one that made it unusable. Two writes in sequence then need a proof that their addresses differ before they can be composed, and a program with four cells in play needs six such proofs, none of which is about what the program does.'},

    {t:'p', h:'So the choice is about where the bookkeeping lives. The big-precondition rule spreads it across every specification and every composition, in proportion to the number of cells the program has in play. The small-footprint rule concentrates all of it into one theorem, invoked wherever a program owns more than the command touches. That theorem does not exist yet.'},

    /* ====================================================== free ========= */

    {t:'sec', s:'The rule exactness makes true'},

    {t:'p', h:'Of the three, deallocation is where the choice of <code>↦</code> is visible, so take it first. <code>free(l)</code> removes the cell at <code>l</code>. Start from a heap that <i>is</i> that cell, and what is left is a heap with nothing in it: <code>{ l ↦ v } free(l) { emp }</code>.'},

    {t:'p', h:'Now read the same triple with Unit 07&rsquo;s other candidate in the precondition — <code>ptsAtLeast l v</code>, the heap has <code>v</code> at <code>l</code>. Exercise <code>x16</code> proved that <code>twoCells</code>, the heap holding <code>3</code> at address <code>4</code> and <code>7</code> at address <code>9</code>, satisfies it at address <code>4</code>. Exercise <code>x18</code> proved that <code>Heap.erase twoCells 4 ≠ Heap.empty</code>. Those two exercises are, between them, a refutation of the free rule under the loose reading: the precondition holds, the command runs, and the postcondition is false.'},

    {t:'cmp',
     left:{t:'Exact <code>↦</code> — the rule is a theorem', kind:'good',
       h:'<code>l ↦ v</code> says the heap <i>is</i> <code>Heap.singleton l v</code>. Erase <code>l</code> from it and you get <code>Heap.empty</code>, which is what <code>emp</code> asks for. The proof is one application of a Unit 06 equation, and no other cell can be present because the precondition forbade it.'},
     right:{t:'Loose <code>↦</code> — the rule is false', kind:'bad',
       h:'<code>ptsAtLeast l v</code> says the heap has <code>v</code> at <code>l</code> and is silent about everywhere else. Erasing <code>l</code> leaves whatever else was there. <code>x16</code> supplies a heap satisfying the precondition and <code>x18</code> supplies the refutation of the postcondition, at address <code>9</code>.'}},

    {t:'note', kind:'key', title:'Where the Unit 07 decision is spent',
     h:'The stronger claim is not that the loose reading makes the free rule false. It is that under the loose reading there is <i>no</i> rule to state, at any length. A postcondition is a claim about the final state alone, and the final heap after <code>free(l)</code> is the initial heap minus <code>l</code> — so if the precondition did not fix the initial heap, no assertion about the final state describes it. You could recover a statement by carrying the initial heap into the triple as a parameter, and then the specification of a one-cell deallocation mentions the whole of memory. Exactness is what removes that parameter: <code>l ↦ v</code> and <code>emp</code> are both equations pinning the entire heap, and the command turns one into the other.'},

    /* ====================================================== load ========= */

    {t:'sec', s:'What the load rule has to say'},

    {t:'p', h:'<code>x := [l]</code> changes the store and leaves the heap alone. Both halves of that have to appear in the postcondition, and the second is the one that looks odd on first sight: the cell <code>l ↦ v</code> is in the precondition and in the postcondition, unchanged. Reading is not destructive. If the cell vanished from the postcondition, the triple would say that loading from a cell consumes it, and a program that reads the same address twice could not be specified.'},

    {t:'p', h:'The store half is <i>the variable <code>x</code> now holds <code>v</code></i>, and there are two assertions in hand that say it: <code>fact (fun σ => σ x = v)</code> and <code>pure (fun σ => σ x = v)</code>. Unit 17 ruled on which of them may sit under a <code>∗</code>. This is the rule where that ruling gets spent, and the wrong choice does not announce itself: it goes through.'},

    {t:'code', tag:'illustration', cap:'Compiled. The <code>fact</code> version of the load rule is provable, by the same cut and the same moves. So the choice is not between a rule that works and one that does not.',
     src:"example (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l)) (fact (fun σ => σ x = v) ∗ (l ↦ v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩\n  exact ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm,\n    by show Store.set σ x v x = v; simp [Store.set], rfl⟩"},

    {t:'p', h:'What it costs is the footprint. In <code>fact φ ∗ (l ↦ v)</code> the star cuts the heap in two and hands the left piece to <code>fact φ</code>, which accepts any heap whatever. So the assertion holds of every heap that contains the cell at <code>l</code> and anything else besides. That is Unit 07&rsquo;s loose reading, arriving through the assertion language instead of through the definition of <code>↦</code>.'},

    {t:'code', tag:'illustration', cap:'Compiled. The witness is the two-cell heap holding <code>7</code> at address <code>1</code> and <code>4</code> at address <code>0</code>; the left slot of the star takes the extra cell and <code>fact</code> raises no objection.',
     src:"example : ¬ (fact (fun _ => True) ∗ (0 ↦ 4) ⊢ (0 ↦ 4)) := by\n  intro hall\n  have h := hall (fun _ => 0) (Heap.union (Heap.singleton 1 7) (Heap.singleton 0 4))\n    ⟨Heap.singleton 1 7, Heap.singleton 0 4, singleton_disjoint 7 4 (by simp), rfl, trivial, rfl⟩\n  have h1 := congrFun h 1\n  rw [union_of_some (Heap.singleton 0 4) (singleton_same 1 7), singleton_other 0 1 4 (by simp)] at h1\n  exact some_ne_none 7 h1"},

    {t:'p', h:'<code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so the left piece of the cut is forced to be <code>Heap.empty</code> and the whole heap is the right piece. The postcondition therefore still pins memory down to one cell, and the store fact rides along at no cost in resources.'},

    {t:'code', tag:'illustration', cap:'Compiled, and every name in it is one you have proved: <code>star_pure_left</code> from Unit 17, and the projection <code>and_right</code> composed onto it with <code>entails_trans</code>, both from Unit 12. The corresponding statement with <code>fact</code> in place of <code>pure</code> is the non-entailment above.',
     src:"example (φ : Store → Prop) (P : Assertion) : pure φ ∗ P ⊢ P :=\n  entails_trans (star_pure_left φ P) (and_right _ _)"},

    {t:'p', h:'One more choice, and it is between two assertions that entail each other. Unit 17 proved <code>pure φ ∗ P ⊢ aAnd (fact φ) P</code> and the converse, so writing the postcondition as <code>aAnd (fact (fun σ => σ x = v)) (l ↦ v)</code> would state exactly the same thing, and its proof is a line shorter.'},

    {t:'code', tag:'illustration', cap:'Compiled. One tactic shorter than the star version, and the postcondition&rsquo;s constructor has two slots to fill instead of six.',
     src:"example (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l)) (aAnd (fact (fun σ => σ x = v)) (l ↦ v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩\n  show Store.set σ x v x = v\n  simp [Store.set]"},

    {t:'p', h:'The <code>∗</code> form is kept anyway, and the reason is shape rather than strength. The rule the next module is working towards adds untouched memory to both ends of a triple, and it does so with a <code>∗</code>: both ends of everything it produces are stars. A postcondition already written as a star is at worst a rearrangement away from meeting it. A postcondition written with <code>aAnd</code> is not a star at all, so it has to be converted before that rule can be applied — by the rule of consequence, at every single use. Speaking the connective the next rule speaks costs one extra slot in one proof, once.'},

    {t:'p', h:'That fixes the statement. The proof then asks for three things inside one term: the final state, a derivation that reaches it, and a cut of the final heap into two disjoint pieces. Only the first of the three is a decision. The derivation is a single rule of <code>Exec</code>, and the cut is the one <code>pure</code> forces.'},

    {t:'ex',
     id: 'm7-1',
     name: 'hoare_load',
     hard: false,
     why: 'The deepest witness construction in the course so far: a state, a derivation, a cut of a heap into two, and a store lookup, all inside one term. It is also the only one of the three whose postcondition <i>constrains</i> the store — the write rule reads the store to find a value and the free rule ignores it, and neither says anything about it afterwards — so this is the rule every later program uses to get a value out of memory and into a variable a specification can talk about. Downstream it is cited twice, both times in Unit 29 — once in the framed re-proof of this unit&rsquo;s last exercise, and once in a program that copies one cell into another.',
     setup: 'In scope: <code>Hoare</code>, <code>Exec</code> and its <code>load</code> rule, <code>singleton_same</code>, <code>disjoint_empty_left</code>, <code>union_empty_left</code>, <code>Store.set</code>, <code>pure</code>, <code>∗</code>. After the <code>intro</code> and the <code>subst</code>: two <code>refine</code>s, a <code>show</code> and a <code>simp</code>. The <code>Exec.load</code> rule takes one premise, a proof that the cell is allocated.',
     goal: "theorem hoare_load (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l)) (pure (fun σ => σ x = v) ∗ (l ↦ v)) := by",
     hints: [
       'Unfolded, the goal is: for every store <code>σ</code> and heap <code>h</code> with <code>h = Heap.singleton l v</code>, there is a state <code>s\'</code> such that <code>Exec (.load x l) ⟨σ, h⟩ s\'</code> and <code>(pure (fun σ => σ x = v) ∗ (l ↦ v))</code> holds at <code>s\'.store</code> and <code>s\'.heap</code>. Three things have to be produced: the state, the derivation, and a cut of the final heap into two disjoint pieces.',
       'The precondition is an equation, so replace <code>h</code> by the singleton everywhere. The command is a load, so the final store is <code>σ</code> with <code>x</code> set to <code>v</code> and the final heap is the singleton, unchanged. Then the star wants the final heap written as a union of two disjoint pieces, one satisfying <code>pure</code> and one satisfying <code>l ↦ v</code>. <code>pure</code> demands its piece be empty, so there is only one way to cut.',
       'Use <code>intro</code>, then <code>subst</code> on the precondition, then <code>refine</code> with a hole for the postcondition, then a second <code>refine</code> supplying the six components of the star. The empty-heap facts you need are <code>disjoint_empty_left</code> and <code>union_empty_left</code>; the latter points the wrong way, so it needs <code>.symm</code>. Finish with <code>show</code> and <code>simp [Store.set]</code>.',
       'After <code>intro σ h hp</code> and <code>subst hp</code> the line is <code>refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩</code>. That names the final state and discharges the derivation, leaving the star as the only goal, at that state&rsquo;s two projections.'
     ],
     sol: "theorem hoare_load (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l)) (pure (fun σ => σ x = v) ∗ (l ↦ v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩\n  refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩\n  show Store.set σ x v x = v\n  simp [Store.set]",
     solNote: 'Six lines, and four of them are decisions: which state, which rule, which cut, which of the star&rsquo;s six slots is left open. If you climbed all four hints and are still stuck, open this. What you want from it is the sequence of choices, and reading it once is enough to make the next two rules routine.',
     expl: 'Everything after <code>subst</code> is construction. The final state is built by hand because <code>Exec</code> is a relation and there is nothing to compute; the derivation is one constructor because a load is one step; and the cut is forced because <code>pure</code> owns the empty heap and nothing else. The only tactic that does any work on a goal rather than supplying a term is the last <code>simp</code>, and what it settles is <code>(if x = x then v else σ x) = v</code>.',
     walk: [
       {tac:'intro σ h hp', h:'Two binders from the <code>∀</code> and one from the arrow. <code>hp : (l ↦ v) σ h</code> is displayed folded, but <code>pointsTo</code> is defined as an equation, so it <i>is</i> <code>h = Heap.singleton l v</code>.'},
       {tac:'subst hp', h:'Replaces <code>h</code> by <code>Heap.singleton l v</code> everywhere and deletes both <code>h</code> and <code>hp</code> from the context. From here the goal mentions a concrete heap, which is what lets <code>singleton_same</code> discharge the load&rsquo;s premise.'},
       {tac:'refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩', h:'Three slots of the existential-and-conjunction at once. The first is the final state, written as a <code>State</code> literal; the second is the derivation, and <code>Exec.load</code>&rsquo;s premise <code>hl : s.heap l = some v</code> is exactly <code>singleton_same l v</code>. The hole is the postcondition, and it arrives with the state&rsquo;s <code>.store</code> and <code>.heap</code> projections still unreduced.'},
       {tac:'refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩', h:'The six components of a star: left heap, right heap, disjointness, the equation saying the whole is their union, and one proof for each side. <code>union_empty_left h</code> says <code>Heap.union Heap.empty h = h</code> and the star wants the equation the other way round, hence <code>.symm</code>. The fifth slot is <code>pure</code>, which is a conjunction, so it is written as a nested pair; the hole is its store half and <code>rfl</code> is its <code>emp</code> half.'},
       {tac:'show Store.set σ x v x = v', h:'The remaining goal displays as <code>fact (fun σ => σ x = v)</code> applied to a projection and to <code>Heap.empty</code>. <code>show</code> restates it as the arithmetic it definitionally is, with the heap argument gone — <code>fact</code> discards it — and the projection reduced.'},
       {tac:'simp [Store.set]', h:'Unfolds the store update to <code>if x = x then v else σ x</code> and settles the condition. This is the only line of the proof that is not a term being handed over.'}
     ],
     deep: [
       {t:'trace', title:'hoare_load, tactic by tactic',
        start:"x : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.load x l) ((_root_.pure fun σ => σ x = v) ∗ l ↦ v)",
        steps:[
          {tac:'intro σ h hp',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.load x l) { store := σ, heap := h } s' ∧ ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) s'.store s'.heap",
           h:'The definition of <code>Hoare</code> unfolds on contact: two <code>∀</code>s and an arrow.'},
          {tac:'subst hp',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.load x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) s'.store s'.heap",
           h:'<code>h</code> and <code>hp</code> are gone and a concrete heap is in their place.'},
          {tac:'refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store\n    { store := σ.set x v, heap := Heap.singleton l v }.heap",
           h:'The existential and the derivation are discharged in one line. The projections on the state literal are left unreduced in the display; they cause no trouble because the next line supplies a term rather than matching on the goal.'},
          {tac:'refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store Heap.empty",
           h:'Five of the six slots close. What is left is the store half of <code>pure</code> — and its heap argument is <code>Heap.empty</code>, which is the cut being visible in the goal.'},
          {tac:'show Store.set σ x v x = v',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ σ.set x v x = v",
           h:'<code>fact</code> ignores its heap argument, so restating the goal deletes <code>Heap.empty</code> along with the projection.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The state after the second <code>refine</code> is the whole argument for <code>pure</code> in one line. <code>Heap.empty</code> is sitting in the goal because the cut put it there, and it got into the cut because nothing else would have satisfied the left conjunct. Had the postcondition used <code>fact</code>, that slot would accept any heap and the cut would have been a free choice — which is what the two illustrations above this exercise measure.'}
     ],
     pitfall: 'Cutting the heap the other way round. <code>refine ⟨Heap.singleton l v, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, ⟨?_, rfl⟩, rfl⟩</code> is a legitimate cut of the same heap, and the first four slots go through untouched: the two pieces really are disjoint and their union really is the whole. It dies inside the fifth. That slot is <code>pure</code>, whose second half is <code>emp</code>, and <code>emp</code> is now being asked about the piece you put on the left — the one-cell heap: <code>Application type mismatch: The argument rfl has type ?m.44 = ?m.44 but is expected to have type emp { store := σ.set x v, heap := Heap.singleton l v }.store (Heap.singleton l v)</code>. The star is not symmetric in its slots. The left piece is the left conjunct&rsquo;s, and the left conjunct here owns nothing at all.',
     variants: 'Flattening the tuple does not work here. Writing the fifth and sixth slots as three flat components — <code>…, ?_, rfl, rfl⟩</code> — makes Lean nest the extra one on the <b>right</b>, so it tries to build the sixth slot, an equation, out of a pair, and reports <code>Insufficient number of fields for ⟨...⟩ constructor: Constructor Eq.refl does not have explicit fields, but 2 were provided</code>. A conjunction in a slot that is not the last has to be written as an explicit pair. · Drop <code>pure</code> for <code>fact</code> and the theorem stays true and gets weaker, exactly as the illustration above shows. · Drop the second conjunct <code>l ↦ v</code> and the postcondition becomes bare <code>pure (fun σ => σ x = v)</code>, whose <code>emp</code> half claims the heap is now empty. That is false, and the point where it fails is the cell the load read: instantiate at <code>l := 0</code>, <code>v := 4</code>, feed the triple <code>Heap.singleton 0 4</code>, invert the run with <code>cases hex with | load hl</code>, and evaluate the postcondition at address <code>0</code>, where it demands <code>Heap.singleton 0 4 0 = Heap.empty 0</code> — that is <code>some 4 = none</code>, closed by <code>some_ne_none</code>. Reading is not destructive, so the cell is still there to contradict it.'
    },

    /* ============================================== write and free ======= */

    {t:'sec', s:'Two rules, one Unit 06 equation each'},

    {t:'p', h:'The write rule has one wrinkle, and it is about where a binder goes. The postcondition should say <i>the cell at <code>l</code> now holds the value of <code>e</code></i> — but <i>the value of <code>e</code></i> is <code>Atom.eval σ e</code>, and <code>σ</code> is the store the assertion is being evaluated at. An <code>Assertion</code> binds its own store, so the postcondition has to be written as a function of it and cannot be a bare <code>l ↦ …</code>.'},

    {t:'code', tag:'sketch', cap:'The postcondition you would write first. The declaration stops at <code>:= by</code> with no proof, so Lean answers <code>unsolved goals</code> — and prints the statement it accepted, which is the part to look at.',
     src:"theorem hoare_write_bad (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (l ↦ (e.eval σ)) := by"},

    {t:'state', cap:'Lean&rsquo;s report on the sketch above. The first line of the context was not written by anybody.',
     src:"σ : Store\nl : Loc\ne : Atom\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l e) (l ↦ Atom.eval σ e)"},

    {t:'p', h:'Lean did not reject the statement. An identifier that appears in a declaration&rsquo;s type and is bound nowhere is not an error to Lean: it inserts a binder for it — an <b>auto-bound implicit</b>, here <code>{σ : Store}</code>, in front of every other binder. So the store the postcondition evaluates <code>e</code> in is fixed <i>before</i> the triple quantifies over starting stores, and the two have nothing to do with each other. The statement is not only oddly scoped; it is false.'},

    {t:'p', h:'The repair is to bind the store inside the assertion. Write the postcondition as <code>fun σ h => (l ↦ (e.eval σ)) σ h</code> and the <code>σ</code> that <code>e</code> is evaluated in is the one the assertion is handed — the store at the moment the postcondition is read. It is heavier on the page than <code>l ↦ …</code>, and it is the only version that says what the write rule means.'},

    {t:'detail', title:'Refuting the auto-bound version', open:false, blocks:[
      {t:'p', h:'Run <code>[0] := x₀</code> from a store in which <code>x₀</code> holds <code>1</code>, and ask for a postcondition evaluated in the store where <code>x₀</code> holds <code>0</code>. The cell ends up holding <code>1</code> and the postcondition demands <code>0</code>.'},
      {t:'code', tag:'illustration', cap:'Compiled. <code>cases hex with | write hl</code> is inversion on the derivation, which replaces <code>s\'</code> by the state the write rule builds. The <code>have</code> restates the resulting equation at address <code>0</code>, where the two lookup laws take it to <code>some 1 = some 0</code>.',
       src:"example : ¬ ∀ (σ : Store) (l : Loc) (e : Atom) (old : Val),\n    Hoare (l ↦ old) ((.write l e)) (l ↦ (e.eval σ)) := by\n  intro hc\n  obtain ⟨s', hex, hq⟩ := hc (fun _ => 0) 0 (.var 0) 0 (fun _ => 1) (Heap.singleton 0 0) rfl\n  cases hex with\n  | write hl =>\n    have h0 : Heap.write (Heap.singleton 0 0) 0 1 0 = Heap.singleton 0 0 0 := congrFun hq 0\n    rw [write_same, singleton_same] at h0\n    simp at h0"}
    ]},

    {t:'p', h:'With that settled the proof has one line of content. The final heap is <code>Heap.write (Heap.singleton l old) l (e.eval σ)</code> — that is what the <code>Exec.write</code> rule produces, and there is no choice about it. The postcondition asks for <code>Heap.singleton l (e.eval σ)</code>. Those are two different expressions for the same heap, and the equation between them is <code>write_singleton</code>, proved in Unit 06.'},

    {t:'ex',
     id: 'm7-2',
     name: 'hoare_write',
     hard: false,
     why: 'The first place where the Unit 06 interface pays a visible dividend: the whole content of the proof is one equation between heaps, and you do not prove it here, because it was proved in Unit 06. Downstream it is cited twice in the verified Lean — once in Unit 27, where it is the first triple the missing structural rule is applied to, and once in Unit 28, where it is the write that closes the question this course opened on. Unit 29 does not cite it; it proves a generalisation, for a write whose value depends on the store.',
     setup: 'In scope: <code>Exec.write</code>, whose premise is a proof that the cell is allocated, and <code>write_singleton (l : Loc) (v w : Val) : Heap.write (Heap.singleton l v) l w = Heap.singleton l w</code>. The same two mechanical lines as the last proof, and then one <code>exact</code> whose tuple has three slots.',
     goal: "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by",
     hints: [
       'Unfolded: for every store <code>σ</code> and heap <code>h</code> equal to <code>Heap.singleton l old</code>, there is a state <code>s\'</code> with <code>Exec (.write l e) ⟨σ, h⟩ s\'</code> such that <code>s\'.heap = Heap.singleton l (Atom.eval s\'.store e)</code>. The store is untouched by a write, so the second component of the state you produce is the only interesting one.',
       'Replace <code>h</code> by the singleton. The <code>write</code> rule of <code>Exec</code> fixes the final state completely: same store, heap updated at <code>l</code>. So write that state down, and what remains is to see that updating the one-cell heap at its own address gives the one-cell heap with the new value.',
       'One <code>intro</code>, one <code>subst</code>, one <code>exact</code> with a three-slot tuple. The premise of <code>Exec.write</code> is <code>singleton_same</code>. The last slot is a Unit 06 equation applied to <code>l</code>, <code>old</code> and <code>e.eval σ</code>.',
       'After <code>intro σ h hp</code> and <code>subst hp</code>, the term begins <code>exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩, Exec.write (singleton_same l old), …⟩</code> — with the last slot the equation that turns that heap into <code>Heap.singleton l (e.eval σ)</code>.'
     ],
     sol: "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,\n         Exec.write (singleton_same l old),\n         write_singleton l old (e.eval σ)⟩",
     solNote: 'The old value <code>old</code> appears in the precondition, in the premise of the write rule, and nowhere in the postcondition — which is right: after the write, what was there is gone and unrecoverable, and the rule says so by not mentioning it.',
     expl: 'The proof is a single term with three components: the state the write rule produces, the one-constructor derivation, and the equation <code>Heap.write (Heap.singleton l old) l w = Heap.singleton l w</code>. The third is <code>write_singleton</code>, and it is the entire mathematical content of the rule.',
     walk: [
       {tac:'intro σ h hp', h:'The store, the heap, and the precondition. <code>hp</code> is the equation <code>h = Heap.singleton l old</code>.'},
       {tac:'subst hp', h:'The heap variable disappears. Everything from here mentions <code>Heap.singleton l old</code> by name, which is what lets a Unit 06 lemma about singletons apply at all.'},
       {tac:'exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩, …⟩', h:'The first slot is the state. Its store is <code>σ</code> unchanged, because a write does not touch the store; its heap is the precondition&rsquo;s heap with <code>l</code> updated, because that is literally what <code>Exec.write</code>&rsquo;s conclusion says the final heap is.'},
       {tac:'Exec.write (singleton_same l old)', h:'The derivation. <code>Exec.write</code> demands <code>s.heap l = some old</code>; the heap is a singleton at <code>l</code>, so that is <code>singleton_same</code>, with no rewriting anywhere.'},
       {tac:'write_singleton l old (e.eval σ)', h:'The postcondition. It has to be <code>s\'.heap = Heap.singleton l (Atom.eval s\'.store e)</code>; the left side is <code>Heap.write (Heap.singleton l old) l (e.eval σ)</code> and the equation between the two is this Unit 06 theorem, at <code>w := e.eval σ</code>.'}
     ],
     deep: [
       {t:'trace', title:'hoare_write — two steps and a term',
        start:"l : Loc\ne : Atom\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l e) fun σ h => (l ↦ Atom.eval σ e) σ h",
        steps:[
          {tac:'intro σ h hp',
           state:"l : Loc\ne : Atom\nold : Val\nσ : Store\nh : Heap\nhp : (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap",
           h:'<code>Hoare</code> unfolds on contact and its two binders and one arrow come off. <code>hp</code> is displayed folded as <code>(l ↦ old) σ h</code>; underneath, <code>pointsTo</code> is an equation, and it is that equation the next tactic acts on.'},
          {tac:'subst hp',
           state:"l : Loc\ne : Atom\nold : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old } s' ∧\n      (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap",
           h:'<code>h</code> and <code>hp</code> leave the context and a concrete one-cell heap stands where the variable did. Neither tactic was a decision; what is left is one existential, and the rest of the proof is the term that inhabits it.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Here is the same theorem with <code>write_singleton</code> unavailable, so that the last slot has to be discharged where it stands.'},
       {t:'code', tag:'illustration', cap:'Compiled. The equation slot becomes a hole, and closing it is a function equality: <code>funext</code>, a case split on the address, and the two definitions in a <code>simp</code> bracket.',
        src:"example (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,\n          Exec.write (singleton_same l old), ?_⟩\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]"},
       {t:'p', h:'Two tactics longer than the real proof, so length is not the objection. What it is, is a proof about the definitions of <code>Heap.write</code> and <code>Heap.singleton</code> rather than about the interface over them — the thing Unit 06 was written to make unnecessary. Change either definition and this proof needs rewriting; <code>write_singleton</code> is a statement about heaps and survives. And you are asked, in the middle of a proof about a program, to decide what happens at an address that program never mentions.'}
     ],
     pitfall: 'Finishing the tuple with <code>rfl</code>. The two heaps are equal but not definitionally: <code>Heap.write (Heap.singleton l old) l w</code> and <code>Heap.singleton l w</code> are different functions of <code>x</code> until you case on whether <code>x = l</code>, and <code>rfl</code> does not case on anything. Lean answers <code>Application type mismatch: The argument rfl has type ?m.25 = ?m.25 but is expected to have type (fun σ h => (l ↦ Atom.eval σ e) σ h) { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.store …</code>.',
     variants: 'Drop the eta-expansion and write the postcondition as <code>l ↦ (e.eval σ)</code>: it compiles, with <code>σ</code> auto-bound in front of the triple, and the resulting statement is false — the refutation is in the fold above this exercise. · Restrict the expression to a constant and the eta-expansion becomes unnecessary: <code>Hoare (l ↦ old) (.write l (.const v)) (l ↦ v)</code> is proved by the same term <code>hoare_write l (.const v) old</code>, because <code>Atom.eval σ (.const v)</code> does not mention <code>σ</code>. That specialisation is the next exercise, and it is also what every later unit that applies this rule uses. · Weaken the precondition to <code>ptsAtLeast l old</code> and the statement becomes refutable, and not because writing needs exactness — it does not, since a write neither creates nor destroys a cell. It is the <i>postcondition</i> that fails: <code>l ↦ (e.eval σ)</code> says the heap is one cell, and the heap you started from was allowed to have others. The witness is <code>twoCells</code> at address <code>4</code>: the precondition <code>twoCells 4 = some 3</code> holds, the command <code>[4] := 3</code> runs, and the postcondition claims <code>Heap.write twoCells 4 3 = Heap.singleton 4 3</code>. Evaluate both sides at address <code>9</code> — <code>write_other</code> takes the write off the left — and it says <code>some 7 = none</code>. Address <code>9</code> is the single point of disagreement, and it is a cell the specification never mentioned.'
    },

    {t:'p', h:'Deallocation is the same shape with the other Unit 06 equation. <code>Exec.free</code> produces <code>Heap.erase (Heap.singleton l v) l</code>; <code>emp</code> asks for <code>Heap.empty</code>; <code>erase_singleton</code> says they are equal.'},

    {t:'ex',
     id: 'm7-3',
     name: 'hoare_free',
     hard: false,
     why: 'The rule that exactness was chosen for. It is three lines here, and under the loose reading it is not a theorem at all — Unit 07&rsquo;s <code>x18</code> is the refutation. It is also the last of the three, so after this exercise every command that touches memory has a rule, and the two that do not — the conditional and the loop — are the only gaps left in the language. It is cited three times downstream: once in Unit 27, in the first framed free, and twice in Unit 29.',
     setup: 'In scope: <code>Exec.free</code>, whose premise is that the cell is allocated, and <code>erase_singleton (l : Loc) (v : Val) : Heap.erase (Heap.singleton l v) l = Heap.empty</code>. The shape is <code>hoare_write</code>&rsquo;s, one lemma along.',
     goal: "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) ((.free l)) (emp) := by",
     hints: [
       'Unfolded: for every <code>σ</code> and every <code>h</code> equal to <code>Heap.singleton l v</code>, there is a state <code>s\'</code> with <code>Exec (.free l) ⟨σ, h⟩ s\'</code> and <code>s\'.heap = Heap.empty</code>. The store is unchanged by a free, so the only content is the heap.',
       'Substitute the precondition, name the state the free rule produces, and then observe that erasing the only cell of a one-cell heap leaves the empty heap. That last observation is a theorem you already have.',
       'The same three tactics as the write rule: <code>intro</code>, <code>subst</code>, <code>exact</code> with a three-slot tuple. The premise of <code>Exec.free</code> is <code>singleton_same</code>, and the postcondition is <code>erase_singleton</code>.',
       'After <code>intro σ h hp</code> and <code>subst hp</code>: <code>exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v), …⟩</code>, which leaves one slot, the postcondition. It is a Unit 06 equation applied to <code>l</code> and <code>v</code>.'
     ],
     sol: "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) ((.free l)) (emp) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,\n         Exec.free (singleton_same l v),\n         erase_singleton l v⟩",
     solNote: 'The value <code>v</code> appears in the precondition and in the premise of the free rule, and the postcondition has forgotten it — which is the point of deallocation. Nothing in the rule says the address may be reused, because this language has no way to obtain one.',
     expl: 'Three components, as before: the state, the derivation, and one Unit 06 equation. The equation is <code>erase_singleton</code>, and the reason the whole rule reduces to it is that both the precondition and the postcondition are equations pinning the entire heap.',
     walk: [
       {tac:'intro σ h hp', h:'Unfolds <code>Hoare</code> and strips its two binders and its arrow, leaving one existential over final states and putting the precondition in the context as <code>hp : (l ↦ v) σ h</code> — which is the equation <code>h = Heap.singleton l v</code>.'},
       {tac:'subst hp', h:'Deletes <code>h</code> and <code>hp</code> and puts <code>Heap.singleton l v</code> in the goal in place of the variable. That is what makes <code>erase_singleton</code> applicable at all: it is stated about a singleton, not about an arbitrary heap satisfying an equation.'},
       {tac:'⟨σ, Heap.erase (Heap.singleton l v) l⟩', h:'The final state. <code>Exec.free</code>&rsquo;s conclusion is <code>⟨s.store, Heap.erase s.heap l⟩</code>, so writing anything else here — <code>Heap.empty</code>, for instance — will not match the rule.'},
       {tac:'Exec.free (singleton_same l v)', h:'The derivation. The premise is that <code>l</code> is allocated, and it is, by <code>singleton_same</code>.'},
       {tac:'erase_singleton l v', h:'The postcondition. <code>emp</code> unfolds to <code>s\'.heap = Heap.empty</code>, and this theorem is that equation.'}
     ],
     deep: [
       {t:'trace', title:'hoare_free, after the two mechanical steps',
        start:"l : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.free l) emp",
        steps:[
          {tac:'intro σ h hp  ·  subst hp',
           state:"l : Loc\nv : Val\nσ : Store\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } s' ∧ emp s'.store s'.heap",
           h:'One existential with two conjuncts, both of them discharged by the single <code>exact</code> that follows.'}
        ],
        done:'No goals.'}
     ],
     pitfall: 'Naming the final heap <code>Heap.empty</code> instead of <code>Heap.erase (Heap.singleton l v) l</code>. It is the same heap and it is what the postcondition wants, but the <i>derivation</i> is checked first, and <code>Exec.free</code>&rsquo;s conclusion is fixed: <code>Application type mismatch: The argument Exec.free ?m.21 has type Exec (Cmd.free ?m.19) ?m.18 { store := State.store ?m.18, heap := (State.heap ?m.18).erase ?m.19 } but is expected to have type Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } { store := σ, heap := Heap.empty }</code>. The rule dictates the state; the lemma converts it afterwards.',
     variants: 'Weaken the precondition to <code>ptsAtLeast l v</code> and the statement becomes false, witnessed by <code>twoCells</code>: <code>x16</code> shows the precondition holds at address <code>4</code> and <code>x18</code> shows <code>Heap.erase twoCells 4 ≠ Heap.empty</code>. · Strengthen the postcondition to <code>aAnd emp (fact (fun σ => True))</code> and the proof gains one slot, <code>trivial</code>, and nothing else — the added conjunct costs no resources, which is a way of seeing that <code>emp</code> is already the strongest thing sayable about a heap with no cells in it. · Drop the premise from the <code>Exec.free</code> application and what sits in the derivation slot is still a function: <code>The argument Exec.free has type State.heap ?m.18 ?m.19 = some ?m.20 → Exec (Cmd.free ?m.19) ?m.18 …</code>. The rule will not fire until you have shown the cell exists, and that obligation is the whole reason a free needs a precondition at all.'
    },

    {t:'note', kind:'key', title:'The layering, stated once',
     h:'Both of the last two proofs end in a theorem from Unit 06 and neither contains a <code>funext</code>. That is not luck. <code>write_singleton</code> and <code>erase_singleton</code> were proved as equations between heaps in a unit that did nothing else, so here they are cited, and what is cited is the interface rather than the definitions underneath it. Had they not been proved there, each of these two rules — and every later specification that applies one — would have to open <code>Heap.write</code> or <code>Heap.erase</code> and split on an address, inside a proof about a program. The discipline of Unit 05 said <i>never unfold a heap operation again</i>; this is the first page where obeying it decides what a specification proof looks like.'},

    /* ============================================= programs that work ==== */

    {t:'sec', s:'Naming a program, and chaining two rules'},

    {t:'p', h:'Give a command a name and the rule specialises to it without any work. <code>clearCell l</code> is <code>[l] := 0</code>, and its specification is the write rule at <code>e := .const 0</code>: the postcondition <code>fun σ h => (l ↦ (Atom.eval σ (.const 0))) σ h</code> reduces, because <code>Atom.eval</code> on a constant is a pattern match that fires, to <code>l ↦ 0</code>. The two triples are then the same proposition, and no rule of consequence is needed to get from one to the other.'},

    {t:'ex',
     id: 'm7-4',
     name: 'clearCell_spec',
     hard: false,
     why: 'The smallest possible use of a rule. It comes before the two-command programs because it isolates one thing: what it costs to instantiate a small-footprint rule at a concrete command. The answer is nothing, and the reason is that the postcondition computes.',
     setup: '<code>def clearCell (l : Loc) : Cmd := .write l (.const 0)</code> is given. You need one term, and it is <code>hoare_write</code> applied to three arguments. No tactic block.',
     goal: "theorem clearCell_spec (l : Loc) (old : Val) : Hoare (l ↦ old) ((clearCell l)) (l ↦ 0) :=",
     hints: [
       'The goal is <code>Hoare (l ↦ old) (clearCell l) (l ↦ 0)</code>. Unfolding <code>clearCell</code> makes the command <code>.write l (.const 0)</code>, which is exactly the command <code>hoare_write</code> speaks about.',
       'The write rule has a postcondition mentioning the value of the expression in the current store. The expression here is a constant, so its value does not depend on the store at all — and two assertions that reduce to the same thing are the same assertion.',
       'Give the term, not a tactic proof: <code>hoare_write</code> takes an address, an <code>Atom</code> and the old value, in that order.',
       'The whole proof is <code>hoare_write l (.const 0) old</code>. If it does not typecheck, check the argument order rather than reaching for <code>hoare_consequence</code>.'
     ],
     sol: "theorem clearCell_spec (l : Loc) (old : Val) : Hoare (l ↦ old) ((clearCell l)) (l ↦ 0) :=\n  hoare_write l (.const 0) old",
     solNote: 'One line, and both of the definitional steps it relies on are invisible: <code>clearCell l</code> unfolds to the command, and <code>Atom.eval σ (.const 0)</code> reduces to <code>0</code> under the binder. If either had needed a rewrite, the proof would have been three lines and would have needed the rule of consequence.',
     expl: 'A small-footprint rule applied at a specific command and a specific expression. Nothing is proved that was not proved in <code>hoare_write</code>; what is demonstrated is that the specialisation is free, because the postcondition is a function of the store that computes as soon as the expression is closed.',
     walk: [
       {tac:'hoare_write l (.const 0) old', h:'One application. Lean has to see that the stated type and the term&rsquo;s type agree, which takes two unfoldings it does silently: <code>clearCell l</code> becomes <code>Cmd.write l (Atom.const 0)</code>, and <code>fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h</code> becomes <code>l ↦ 0</code> — the first by unfolding the definition, the second by reducing the pattern match and then by eta.'}
     ],
     deep: [
       {t:'trace', title:'The two silent unfoldings, made loud',
        start:"l : Loc\nold : Val\n⊢ Hoare (l ↦ old) (clearCell l) (l ↦ 0)",
        steps:[
          {tac:'show Hoare (l ↦ old) (.write l (.const 0)) (fun σ h => (l ↦ ((Atom.const 0).eval σ)) σ h)',
           state:"l : Loc\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h",
           h:'A <code>show</code> succeeds exactly when the two statements are definitionally equal, so this line is a demonstration rather than a step: the goal you started with and the type of <code>hoare_write l (.const 0) old</code> are the same proposition. The solution omits it because Lean does the same check when the term is handed over.'}
        ],
        done:'<code>exact hoare_write l (.const 0) old</code> — no goals.'},
       {t:'code', tag:'illustration', cap:'Compiled. The reduction the whole thing depends on, isolated: evaluating a constant atom is a match that fires, in any store.',
        src:"example (σ : Store) : (Atom.const 0).eval σ = 0 := rfl"},
       {t:'p', h:'Everything about this exercise turns on the expression being closed. Replace <code>.const 0</code> by <code>.var y</code> and <code>Atom.eval σ (.var y)</code> is <code>σ y</code>, which does not reduce further and which mentions the store — so the postcondition cannot be written as a bare <code>l ↦ …</code> at all, and the specification of such a command has to carry the eta-expanded form that <code>hoare_write</code> already has. Unit 29 gives the general rule a name and a proof; here it is enough to see why the constant case is the easy one.'}
     ],
     pitfall: 'Reaching for <code>hoare_consequence</code> to convert the write rule&rsquo;s postcondition into <code>l ↦ 0</code>. It works, and it is three lines instead of one, and it obscures the point: nothing needs converting, because the two postconditions are the same assertion and Lean already knows it.',
     variants: 'Change the postcondition to <code>l ↦ 1</code> and the same term stops typechecking, which shows that the two constants are being compared rather than assumed to match: <code>hoare_write l (Atom.const 0) old has type Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h but is expected to have type Hoare (l ↦ old) (clearCell l) (l ↦ 1)</code>. The check that succeeds for <code>0</code> is a real check. · Drop the <code>old</code> argument and the term is still a function, so nothing has been inferred: <code>hoare_write l (Atom.const 0) has type ∀ (old : Val), Hoare (l ↦ old) …</code>. The value is determined by the goal, since it appears in the precondition, but <code>hoare_write</code> declares it explicitly and an explicit argument is never filled in from the expected type of the whole application. Write <code>hoare_write l (.const 0) _</code> and it is — the underscore is what puts unification back in charge.'
    },

    {t:'p', h:'Now two commands. <code>[l] := 1 ;; [l] := 2</code> writes the same cell twice, and Unit 22&rsquo;s <code>hoare_seq</code> is the rule that joins two triples end to end: it needs a middle assertion <code>Q</code> that is the first command&rsquo;s postcondition and the second command&rsquo;s precondition. Here the first write leaves <code>l ↦ 1</code> and the second write demands a cell at <code>l</code> holding something. They fit.'},

    {t:'ex',
     id: 'x48',
     name: 'writeTwice_spec',
     hard: false,
     why: 'The baseline. This is composition working, with no structural rule beyond <code>hoare_seq</code>, and it works for one reason: the write rule&rsquo;s postcondition is a bare <code>↦</code>, which is exactly the shape the write rule&rsquo;s precondition asks for, so the assertion that leaves the first command is already the assertion the second demands. Keep the shape of this proof in mind for the next exercise, where every part of it is the same except that one.',
     setup: 'In scope: <code>hoare_seq</code> from Unit 22 and <code>hoare_write</code> from this unit, and nothing else. One term and two applications, with no tactic block. A tactic proof works as well, and then <code>hoare_seq</code> needs its middle assertion supplied by name, because both of its arguments would be holes.',
     goal: "theorem writeTwice_spec (l : Loc) (old : Val) :\n    Hoare (l ↦ old) ((.write l (.const 1) ;; .write l (.const 2))) (l ↦ 2) :=",
     hints: [
       'Unfolded, the goal is: for every <code>σ</code> and every <code>h = Heap.singleton l old</code>, there is a state <code>s\'</code> with <code>Exec (.write l (.const 1) ;; .write l (.const 2)) ⟨σ, h⟩ s\'</code> and <code>s\'.heap = Heap.singleton l 2</code>.',
       'You are not meant to build that state: the command is a sequence, and every triple you need about its two halves is already a theorem on this page. After the first write the cell at <code>l</code> holds <code>1</code> and the heap is nothing else. That is the middle assertion, and each half is then a triple about a single write with a constant on the right.',
       'Two applications of <code>hoare_write</code>, joined by <code>hoare_seq</code>. Each application needs the address, the <code>Atom</code>, and the value the cell held <i>before</i> that command.',
       'The term is <code>hoare_seq (hoare_write l (.const 1) old) (hoare_write l (.const 2) …)</code>, and the one thing left to supply is the value the second write is overwriting — which the first write put there.'
     ],
     sol: "theorem writeTwice_spec (l : Loc) (old : Val) :\n    Hoare (l ↦ old) ((.write l (.const 1) ;; .write l (.const 2))) (l ↦ 2) :=\n  hoare_seq (hoare_write l (.const 1) old) (hoare_write l (.const 2) 1)",
     solNote: 'No <code>(Q := …)</code> is needed in the term form: both arguments are fully applied, so their types determine the middle assertion and there is nothing left for Lean to guess. The named argument is only needed when a hole stands where one of the two triples should be.',
     expl: 'Two instances of one rule, glued by <code>hoare_seq</code>. The middle assertion <code>l ↦ 1</code> is produced by the first application and consumed by the second, and it matches on the nose: <code>hoare_write</code>&rsquo;s postcondition at <code>.const 1</code> reduces to <code>l ↦ 1</code>, which is <code>hoare_write</code>&rsquo;s precondition at <code>old := 1</code>.',
     walk: [
       {tac:'hoare_seq _ _', h:'Turns the goal about the sequence into two goals about its components, with a shared assertion in the middle. Because both arguments are supplied as complete terms, that assertion is read off them rather than guessed.'},
       {tac:'hoare_write l (.const 1) old', h:'The first component. Precondition <code>l ↦ old</code>, which is the goal&rsquo;s precondition; postcondition <code>l ↦ 1</code>, which becomes the middle assertion.'},
       {tac:'hoare_write l (.const 2) 1', h:'The second component. Its <code>old</code> argument is <code>1</code> — the value the previous command left — so its precondition is <code>l ↦ 1</code> and matches the middle assertion exactly. Its postcondition <code>l ↦ 2</code> is the goal&rsquo;s.'}
     ],
     deep: [
       {t:'trace', title:'The same proof, as a script',
        start:"l : Loc\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l (Atom.const 1) ;; Cmd.write l (Atom.const 2)) (l ↦ 2)",
        steps:[
          {tac:'refine hoare_seq (Q := (l ↦ 1)) ?_ ?_',
           state:"case refine_1\nl : Loc\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l (Atom.const 1)) (l ↦ 1)",
           h:'The first of two goals. The middle assertion has to be supplied by name here, because both triples are holes and nothing determines it.'},
          {tac:'· exact hoare_write l (.const 1) old',
           state:"case refine_2\nl : Loc\nold : Val\n⊢ Hoare (l ↦ 1) (Cmd.write l (Atom.const 2)) (l ↦ 2)",
           h:'The second goal, with the middle assertion now in the precondition position. The two goals share it, which is the whole content of sequencing.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Everything that made this work is in the two goal states: the same address in both triples, and therefore the same one-cell heap threaded from the postcondition of the first to the precondition of the second. Nothing was added and nothing was dropped.'}
     ],
     pitfall: 'Passing <code>old</code> to the second write as well. Its precondition is then <code>l ↦ old</code>, which is not what the first command leaves, and the error names both assertions: <code>The argument hoare_write l (Atom.const 2) old has type Hoare (l ↦ old) (Cmd.write l (Atom.const 2)) … but is expected to have type Hoare (fun σ h => (l ↦ Atom.eval σ (Atom.const 1)) σ h) (Cmd.write l (Atom.const 2)) (l ↦ 2)</code>. The expected precondition is the first write&rsquo;s postcondition, still in its unreduced form — which is the middle assertion, shown to you by the failure. The <code>old</code> of a write rule is the value being overwritten, and after the first command that value is <code>1</code>.',
     variants: 'Give the two writes different addresses and there is no proof to adjust — it cannot be written at all. <code>hoare_seq (hoare_write l (.const 1) old) (hoare_write l\' (.const 2) old\')</code> fails at the <i>first</i> argument, with <code>hoare_write l (Atom.const 1) old has type Hoare (l ↦ old) … but is expected to have type Hoare (l ↦ old ∗ l\' ↦ old\') …</code>: the precondition of the program owns two cells and the rule owns one, and nothing in this unit can bridge that. · Make the second command <code>free(l)</code> instead of a second write and the composition still goes through: <code>hoare_seq (hoare_write l (.const 1) old) (hoare_free l 1)</code> proves <code>Hoare (l ↦ old) ([l] := 1 ;; free(l)) emp</code>, because the write&rsquo;s postcondition <code>l ↦ 1</code> is exactly the free&rsquo;s precondition. So it is not sequencing, and not <code>free</code>, that breaks in the next exercise — it is one particular postcondition.'
    },

    /* =================================================== the defeat ====== */

    {t:'sec', s:'The program that will not go through'},

    {t:'p', h:'<code>x := [l] ;; free(l)</code>. Read a cell, then release it. The value is now in a variable, the memory is gone, and the specification writes itself: <code>{ l ↦ v } readAndFree { x = v }</code>, with the postcondition <code>pure (fun σ => σ x = v)</code> — the store fact, and no memory left.'},

    {t:'p', h:'Both commands have rules. The first is <code>hoare_load</code>, the second is <code>hoare_free</code>, and <code>hoare_seq</code> is how two rules become one. Apply it.'},

    {t:'code', tag:'sketch', cap:'The composition, written down. It does not typecheck, and the message below is what Lean says about it.',
     src:"example (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l ;; .free l)) (pure (fun σ => σ x = v)) :=\n  hoare_seq (hoare_load x l v) (hoare_free l v)"},

    {t:'state', cap:'Reported on the second argument. The middle assertion is determined by the first triple, and the second triple does not accept it.',
     src:"error: Application type mismatch: The argument\n  hoare_free l v\nhas type\n  Hoare (l ↦ v) (Cmd.free l) emp\nbut is expected to have type\n  Hoare ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) (Cmd.free l) (_root_.pure fun σ => σ x = v)\nin the application\n  hoare_seq (hoare_load x l v) (hoare_free l v)"},

    {t:'p', h:'Look at the two assertions in the middle. The load leaves <code>pure (fun σ => σ x = v) ∗ (l ↦ v)</code>; the free wants <code>l ↦ v</code>. <code>hoare_seq</code> asks for <i>one</i> assertion appearing in both positions, and these are two, so there is nothing for it to match. The extra conjunct is the store fact, and the free rule has no slot anywhere in its statement that could hold it.'},

    {t:'p', h:'Try the rule of consequence on it. On the precondition side it works, and it works already: <code>pure φ ∗ P ⊢ P</code> is the entailment proved earlier on this page, at <code>P := (l ↦ v)</code>. So the load&rsquo;s postcondition really does entail the free&rsquo;s precondition, and the store fact can be dropped.'},

    {t:'p', h:'The other side is where it dies. Having dropped the store fact to get into the free rule, you have to get it back out: consequence would need <code>emp ⊢ pure (fun σ => σ x = v)</code>, and an assertion about the store cannot be established from a heap being empty. The information was not weakened, it was discarded.'},

    {t:'code', tag:'illustration', cap:'Compiled. The witness is a store in which <code>x</code> holds <code>v + 1</code>; the empty heap satisfies <code>emp</code> there and the store fact is false.',
     src:"example (x : Var) (v : Val) : ¬ (emp ⊢ pure (fun σ => σ x = v)) := by\n  intro hc\n  obtain ⟨hφ, _⟩ := hc (fun _ => v + 1) Heap.empty rfl\n  have : v + 1 = v := hφ\n  exact absurd this (by simp)"},

    {t:'p', h:'So the store fact has to travel <i>across</i> the free, untouched, rather than being dropped before it and re-derived after. No rule available here does that. Supply the middle assertion by hand and the mismatch relocates rather than disappearing.'},

    {t:'code', tag:'sketch', cap:'The first half now goes through — <code>hoare_load</code> is exactly this triple. The state below is what is left, and nothing in this unit proves it.',
     src:"refine hoare_seq (Q := (pure (fun σ => σ x = v) ∗ (l ↦ v))) (hoare_load x l v) ?_"},

    {t:'state', cap:'The residual goal. It is the free rule with a store fact attached to both ends and never mentioned in between.',
     src:"x : Var\nl : Loc\nv : Val\n⊢ Hoare ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) (Cmd.free l) (_root_.pure fun σ => σ x = v)"},

    {t:'p', h:'Read that goal against <code>hoare_free</code>. The command is the same. The precondition is the free rule&rsquo;s precondition with <code>pure (fun σ => σ x = v) ∗</code> in front of it, and the postcondition is the free rule&rsquo;s postcondition <code>emp</code> with the same thing in front — up to <code>P ∗ emp</code> and <code>P</code> entailing each other, which Unit 15 proved. So what is missing is one move: <i>take a triple, and add the same assertion to both ends</i>. Nothing on this page supplies it, and the three attempts above are between them the reason: the bare application has nowhere to put the extra conjunct, consequence discards it instead of carrying it, and supplying the middle assertion by hand only relocates the demand.'},

    {t:'p', h:'Which leaves one way to prove the program correct: abandon the rules and build the derivation. <code>Exec.seq</code> takes a derivation for the first command and one for the second and produces one for the sequence, and the two component derivations are the same one-constructor terms that appeared inside <code>hoare_load</code> and <code>hoare_free</code>. Doing that is the exercise; noticing which step of it you would not want to write a second time is what it is for.'},

    {t:'ex',
     id: 'm7-5',
     name: 'readAndFree_spec',
     hard: false,
     why: 'The deliberate defeat. Every ingredient of the proof already exists as a theorem on this page, and you cannot assemble them; you have to go back under the rules and build the run. That is the need Module 6 answers, and feeling it is the point. While you work, keep track of which line you are writing that <code>hoare_load</code> and <code>hoare_free</code> had already written for you.',
     setup: '<code>def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l</code> is given. <code>hoare_seq</code> will not close this goal — the two rules do not compose — so work from the definition of <code>Hoare</code> and from <code>Exec.seq</code>. The postcondition <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so it contributes two of the goals, not one.',
     goal: "theorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by",
     hints: [
       'Unfolded: for every <code>σ</code> and every <code>h = Heap.singleton l v</code>, there is a state <code>s\'</code> with <code>Exec (.load x l ;; .free l) ⟨σ, h⟩ s\'</code>, and at that state <code>s\'.store x = v</code> and <code>s\'.heap</code> is empty. Three obligations, not two, because <code>pure</code> is a conjunction.',
       'Run the program on paper. The load puts <code>v</code> into <code>x</code> and leaves the heap alone; the free removes the cell. So the final state is <code>σ</code> with <code>x</code> set to <code>v</code>, and the heap is the singleton with <code>l</code> erased. Write that state down and then prove the three things about it separately.',
       'Use <code>refine</code> with four holes in one tuple: the state, the derivation, and the two halves of <code>pure</code>. The derivation is <code>Exec.seq</code> applied to the load and free derivations you built in the two earlier exercises. The store half needs <code>show</code> and <code>simp [Store.set]</code>; the heap half is <code>erase_singleton</code>.',
       'After <code>intro σ h hp</code> and <code>subst hp</code>, the line is <code>refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩</code> — one hole for the derivation and two for the conjuncts of the postcondition, then a bullet for each.'
     ],
     sol: "theorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩\n  · exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))\n  · show Store.set σ x v x = v\n    simp [Store.set]\n  · exact erase_singleton l v",
     solNote: 'Eight lines, and six of them are lines you have already written today — inside <code>hoare_load</code> and inside <code>hoare_free</code>. If you climbed all four hints and are still stuck, open this without hesitation: what this exercise measures is not whether you can build the derivation but whether you can see that you should not have had to. You will prove this same program again in Unit 29, out of <code>hoare_seq</code>, the rule of consequence twice, and one rule you do not have yet — with <code>hoare_load</code> and <code>hoare_free</code> cited rather than re-proved, and no <code>Exec</code> constructor anywhere in it.',
     expl: 'The proof is <code>hoare_load</code> and <code>hoare_free</code> textually interleaved. <code>Exec.seq</code> joins the two derivations; the store obligation is the load&rsquo;s last two lines; the heap obligation is the free&rsquo;s last line. Nothing new is proved. What is spent is the modularity: the two commands were specified separately and had to be re-proved together.',
     walk: [
       {tac:'intro σ h hp  ·  subst hp', h:'The same opening as the three rules. The heap becomes <code>Heap.singleton l v</code> and the goal is one existential.'},
       {tac:'refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩', h:'Four slots, from three nested constructors: the existential&rsquo;s witness, the derivation, and the two conjuncts of <code>pure</code>. The state is the whole program run in your head — the load&rsquo;s store, the free&rsquo;s heap — and writing it down is the step that cannot be delegated to a rule.'},
       {tac:'exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))', h:'The derivation, as a tree with three nodes. The free&rsquo;s premise is <code>singleton_same l v</code> again: the load did not change the heap, so the cell is still there when the free runs. That fact is invisible in the rules — it is the reason the load&rsquo;s postcondition kept the cell — and here it is being used directly.'},
       {tac:'show Store.set σ x v x = v  ·  simp [Store.set]', h:'The store half of <code>pure</code>, restated past the projection and settled. Identical to the last two lines of <code>hoare_load</code>.'},
       {tac:'exact erase_singleton l v', h:'The heap half. Identical to the last line of <code>hoare_free</code>.'}
     ],
     deep: [
       {t:'trace', title:'The three obligations, after the state is named',
        start:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (readAndFree x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      _root_.pure (fun σ => σ x = v) s'.store s'.heap",
        steps:[
          {tac:'refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩',
           state:"case refine_1\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ Exec (readAndFree x l) { store := σ, heap := Heap.singleton l v }\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }",
           h:'The derivation, with both endpoints now concrete. The command is still displayed folded as <code>readAndFree x l</code>, and nothing needs to unfold it: <code>Exec.seq</code> matches through the definition. This goal is the one no rule on this page produces.'},
          {tac:'· exact Exec.seq …',
           state:"case refine_2\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
           h:'The store half of <code>pure</code>. <code>fact</code> ignores the second argument, which is why <code>show</code> can delete the projection wholesale.'},
          {tac:'· show Store.set σ x v x = v  ·  simp [Store.set]',
           state:"case refine_3\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
           h:'The heap half. Unfolded it is <code>Heap.erase (Heap.singleton l v) l = Heap.empty</code>, which is <code>erase_singleton</code>.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Count what the derivation goal cost. Building it required knowing the shape of both commands, both <code>Exec</code> rules, and the fact that the load leaves the heap intact so that the free&rsquo;s premise still holds. All three of those were already established, each inside a theorem, and none of them could be cited. A proof that cannot cite its own lemmas is a proof that does not scale, and a four-command program in this style is a page.'}
     ],
     pitfall: 'Opening with <code>refine ⟨⟨…⟩, ?_, ?_⟩</code> — three slots instead of four. It is the natural guess, since the existential has a derivation and a postcondition; but <code>pure</code> is <code>aAnd (fact φ) emp</code>, so the postcondition slot is itself a pair, and unless you open a hole for each half the anonymous constructor leaves the conjunction whole. Two goals come back, not three, and the second is <code>⊢ _root_.pure (fun σ => σ x = v) { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap</code>. The three bullets you then write are one too many, and the complaint arrives in the wrong place — on the <code>show</code> in the second bullet, <code>&#39;show&#39; tactic failed, pattern σ.set x v x = v is not definitionally equal to target _root_.pure (fun σ => σ x = v) …</code>, because <code>show</code> is being aimed at a conjunction; and then again at the end as <code>No goals to be solved</code>. Neither message says <i>you opened too few holes</i>. Count the conjuncts of the postcondition before choosing the number.',
     variants: 'Reverse the two commands — <code>free(l) ;; x := [l]</code> — and no triple with precondition <code>l ↦ v</code> holds, however weak the postcondition; <code>¬ Hoare (l ↦ v) ((.free l ;; .load x l)) aTrue</code> is provable in eight lines. The point of failure is not the postcondition, which is <code>aTrue</code> and cannot fail. It is the existential: <code>Hoare</code> demands a final state, and there is none. Feed the triple <code>Heap.singleton l v</code>, take the run apart with <code>cases hex with | seq h₁ h₂</code> and then <code>cases h₁ with | free hl</code>, and <code>h₂</code> is a run of the load from the heap <code>Heap.erase (Heap.singleton l v) l</code>. Rewrite that with <code>erase_singleton</code> and it is <code>Heap.empty</code>, at which point Unit 19&rsquo;s <code>exec_load_stuck</code> says no such run exists. · Drop the store conjunct and specify only <code>emp</code> and the proof collapses to one <code>exact</code> with a three-component tuple — no bullets, no <code>show</code> — and the specification loses its point: it would say the program ends with no memory, and not that anything was read. · Replace <code>pure</code> by <code>fact</code> and the proof loses the <code>erase_singleton</code> line, and the specification stops saying the memory was released — which is the half of the program a separation logic exists to talk about.'
    },

    /* ==================================================== the debt ======= */

    {t:'sec', s:'What that cost'},

    {t:'dod',
     h:'You can state a rule on the cells its command touches and prove it, and you have three of them, one per memory command. You can specialise one to a named program, and you can chain two of them when the assertion one leaves is on the nose the assertion the next demands. You have also proved a two-command program from the operational semantics, by hand, having watched three separate attempts to compose the rules fail — the bare application, the rule of consequence, and the middle assertion supplied by hand. That failure is the deliverable of this unit. Nothing here is broken; the three rules are correct and so is the program. What is missing is a move.'},

    {t:'p', h:'Three questions, and the answers are the next unit&rsquo;s definition.'},

    {t:'ol', items:[
      'What did the load&rsquo;s postcondition have that the free&rsquo;s precondition did not want? Name it as an assertion, and say what would have to be true of the free command for that assertion to be droppable and re-attachable.',
      'If a command runs correctly on a small heap, what would you have to know in order to conclude that it runs correctly inside a bigger one — that it does not fault, that it terminates, and that it leaves the extra memory exactly as it found it?',
      'Name a command for which that conclusion would be <b>false</b>. Not one in this language, necessarily: describe an operation whose behaviour on a small heap does not determine its behaviour on a larger one.'
    ]},

    {t:'p', h:'Question (iii) has an answer, and it is the reason the next module takes five units instead of one. Three correct rules that will not compose, and one program proved from the semantics: the missing tool is a rule saying <i>a command that works on its own memory still works inside a bigger heap</i>. That rule cannot be assumed — it is a claim about what commands <i>do</i> — so the next unit has to find out what it would take for it to be true.'}

  ]
});
