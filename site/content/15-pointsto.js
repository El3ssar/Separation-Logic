registerChapter({
  id: 'pointsto',
  num: '13',
  phase: 'Phase 2 · The logic of ownership',
  title: 'emp, ↦, and exact ownership',
  blurb: 'Two definitions, each an equation between heaps, and the two theorems they make possible: that a value is determined by the resource, and that ownership cannot be thrown away.',

  orient: {
    youWill: [
      'Write <code>emp</code> and <code>pointsTo</code> as equations on the heap, and say what an equation gives you that a lookup or a quantified statement does not — with both alternatives compiled beside it.',
      'Declare an infix notation at precedence 60 and read a goal in which two different turnstiles appear with no brackets between them.',
      'Read <code>l ↦ v</code> in the first person, and use that reading to say in advance which entailments between it and Unit 07\'s loose reading can hold.',
      'Spend a hypothesis of type <code>(l ↦ v) σ h</code> with <code>subst</code>, though nothing about its type looks like an equation.',
      'Prove that two claims on the same address force the two values to agree, and say why the conclusion has to be wrapped in <code>fact</code>.',
      'Prove that an entailment is <b>false</b>, and say what a machine-checked non-entailment is evidence of.'
    ],
    needs: [
      'Unit 12: <code>Assertion</code>, <code>⊢</code>, <code>⊣⊢</code>, <code>aAnd</code>, <code>aFalse</code>, <code>fact</code>, and that <code>intro σ h hp</code> works because <code>⊢</code> is a folded <code>def</code>.',
      'Unit 07: the two candidate readings of “<code>l</code> holds <code>v</code>”, and the heap <code>twoCells</code> that separates them.',
      'Unit 05: <code>Heap.empty</code>, <code>Heap.singleton</code> and the six lookup laws. Unit 06: <code>write_empty</code>.',
      'Unit 08: <code>subst</code>. Unit 02: <code>Option.some.inj</code> — taught eleven units ago, needed for the first time here.'
    ],
    payoff: 'Everything the rest of this course owns, it owns through <code>↦</code>. The connective of Unit 14 divides a heap between two assertions, and the assertions it divides it between are almost always these. The second theorem on this page — an entailment that is false — is the first member of a family: Unit 14 proves two more, and the first of those is the reason the frame rule has to exist.'
  },

  blocks: [

    /* =============================================================== opening === */

    {t:'p', h:'Two candidates, and Unit 07 already ran the experiment that separates them. Under the loose reading — the cell <code>l</code> holds <code>v</code>, and the heap may hold anything else besides — the rule that frees a cell and concludes that memory is now empty is refutable, and the refutation is compiled. Under the exact reading it is not. What Unit 07 could not do was write either reading down as a proposition of the logic, because there was no type to write it at. There is now, and each reading is one line.'},

    {t:'p', h:'This page writes down the exact one, twice: once for the heap that holds nothing, and once for the heap that holds exactly one cell. Take the smaller of the two first, because the choice that has to be made is the same in both and is easier to see with nothing in the way.'},

    /* ================================================================== emp === */

    {t:'sec', s:'Owning nothing'},

    {t:'p', h:'What should <i>I hold no memory at all</i> say about a heap <code>h</code>? Three spellings suggest themselves. The heap <i>is</i> the empty one: <code>h = Heap.empty</code>. Or: every address is unallocated, <code>∀ l, h l = none</code>. Or: the domain of <code>h</code> is empty. The third turns out to be the second in other clothing. No heap in this course carries a domain — Unit 05 refused to package one in, and Unit 08 priced writing domains down as predicates and refused that too — so <i>the domain of <code>h</code> is empty</i> has to be spelled <code>∀ l, ¬ defined h l</code>, and <code>defined</code> unfolds to an existential over exactly the lookup the second spelling tests. That leaves an equation and a family of equations, and they are not the same shape.'},

    {t:'code', tag:'verified', cap:'The assertion satisfied by exactly one heap.',
     src:'def emp : Assertion := fun _ h => h = Heap.empty'},

    {t:'p', h:'The store binder is an underscore, as it is in every definition on this page: nobody owns a variable, and <code>emp</code> makes no claim about one. What is left is an equation, and an equation is a strange thing to find in a logic of ownership — it does not test the heap, it names it. That is the point of it. One equation fixes every address at once, with no quantifier to instantiate and no address to choose.'},

    {t:'p', h:'The difference shows up when the assertion is a <i>hypothesis</i> rather than a goal. An equation can be spent: <code>subst</code> deletes the heap variable from the proof and puts <code>Heap.empty</code> everywhere it stood, after which the goal is a closed statement about a known heap. A family of equations cannot be spent — it can only be instantiated, one address at a time, at addresses you have to pick yourself.'},

    {t:'code', tag:'illustration', cap:'The same small fact, proved from each spelling. <code>empPointwise</code> is declared here and nowhere else; the course does not use it.',
     src:'def empPointwise : Assertion := fun _ h => ∀ l, h l = none\n\nexample (σ : Store) (h : Heap) (hp : emp σ h) :\n    Heap.write h 4 3 = Heap.singleton 4 3 := by\n  subst hp\n  exact write_empty 4 3\n\nexample (σ : Store) (h : Heap) (hp : empPointwise σ h) :\n    Heap.write h 4 3 = Heap.singleton 4 3 := by\n  funext x\n  by_cases hx : x = 4\n  · rw [hx, write_same, singleton_same]\n  · rw [write_other h 4 x 3 hx, hp x, singleton_other 4 x 3 hx]'},

    {t:'p', h:'Two lines against four, and the four are not four lines of insight: they are Unit 03\'s three-move shape, run again, to rebuild by hand a heap the first proof was handed outright. Every later theorem that takes ownership as a hypothesis would pay that, every time. That is what the equation buys, and it is the only reason to prefer it. Whether the two spellings even describe the same heaps is not settled by anything above: one is an equation between functions, the other a family of equations between values, and Unit 03 is where you learned those are different things.'},

    /* ============================================================ pointsTo === */

    {t:'sec', s:'Owning one cell'},

    {t:'p', h:'Now the same choice one cell up, where the two candidates genuinely disagree. Unit 07 wrote both and named the verdict; here they are as definitions of the logic.'},

    {t:'code', tag:'verified', cap:'The assertion that owns exactly one cell, and the notation for it.',
     src:'def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v\ninfix:60 " ↦ " => pointsTo'},

    {t:'p', h:'The body is an equation again, and it is the same equation Unit 07 called <code>ptsExactly</code> — same text, at a type that now has a name. The heap is not asked whether it contains <code>l</code>. It is told what it is: the one-cell heap, and nothing else.'},

    {t:'p', h:'The notation is declared at 60, which is above <code>⊢</code> at 40 and above the 55 that Unit 14 will use for the connective that cuts a heap in two. The consequence is the same against both: <code>l ↦ v</code> is the tightest-binding thing in any expression you will write, so it never needs brackets around it, and Lean will not print any.'},

    {t:'code', tag:'illustration', cap:'Two questions to Lean: what an application of the notation is, and how a mixed expression groups.',
     src:'#check (4 ↦ 3)\n#check fun (l : Loc) (v : Val) => (l ↦ v) ⊢ emp'},

    {t:'state', cap:'The two answers, one line each.',
     src:'4 ↦ 3 : Assertion\nfun l v => l ↦ v ⊢ emp : Loc → Val → Prop'},

    {t:'p', h:'The brackets that went in did not come back. Meet that here rather than in a goal, because the display it produces is the least readable thing on this page: a goal whose statement is <i>it is not the case that <code>l ↦ v</code> entails <code>emp</code></i> prints as <code>⊢ ¬l ↦ v ⊢ emp</code>. Three symbols, two of which are turnstiles and only one of which is this unit\'s. The leftmost is the goal display\'s, from Unit 00; the second is <code>Entails</code>; and the arrow between <code>l</code> and <code>v</code> binds tighter than either.'},

    {t:'quote', h:'Read <code>l ↦ v</code> in the first person. <b>I own the cell at address <code>l</code>, it holds <code>v</code>, and I own nothing else.</b> Not: the cell at <code>l</code> holds <code>v</code>. The last clause is the whole of the difference, and it is a clause about the speaker rather than about memory.'},

    {t:'p', h:'That reading earns its keep by predicting theorems before they are proved. Ask of any proposed entailment: <i>could someone holding the left-hand side truthfully say the right-hand side?</i> Holding exactly the cell <code>l</code>, can I truthfully say that the cell <code>l</code> holds <code>v</code>, without committing to what else I have? Yes — that direction throws information away, and throwing information away is what an entailment does. The reverse asks someone who has said only <i>the cell <code>l</code> holds <code>v</code></i> to commit to holding nothing else, which is a claim they never made.'},

    {t:'cmp',
     left: {t:'Unit 07\'s exact reading, now a definition', kind:'good', tag:'verified',
            src:'def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v',
            h:'Satisfied by one heap. The first person: <i>this is what I have.</i>'},
     right:{t:'Unit 07\'s loose reading, still available', tag:'verified',
            src:'def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v',
            h:'Satisfied by infinitely many heaps, including every extension of the first. The third person: <i>this is true of memory.</i>'}},

    {t:'p', h:'One direction is provable in three tactics: introduce the state and the premise, replace the heap by the one-cell heap the premise says it is, and read it at <code>l</code>. The middle step is doing something that deserves a section of its own, and gets one below.'},

    {t:'code', tag:'illustration', cap:'Exact ownership entails the loose reading.',
     src:'theorem exact_entails_loose (l : Loc) (v : Val) : (l ↦ v) ⊢ ptsAtLeast l v := by\n  intro σ h hp\n  subst hp\n  exact singleton_same l v'},

    {t:'p', h:'The other direction is false, which is a stronger verdict than <i>unproved</i>. Unit 07 exhibited a heap satisfying the loose reading and not the exact one; what that heap refutes, now that both readings are assertions, is an entailment. Refuting one has a fixed shape, and it is the shape of every refutation on this page: an entailment is a function of three arguments, so to attack it you choose the store, choose the heap, hand it a proof of the premise, and work on whatever comes back. The fold below runs that against Unit 07\'s two-cell heap.'},

    {t:'detail', title:'The converse, as a non-entailment', tag:'aside', open:false, blocks:[
      {t:'p', h:'The witness is Unit 07\'s two-cell heap, and the proof is Unit 07\'s two exercises with one move in front of them: apply the assumed entailment to a store, a heap and a proof of its premise, and then refute what comes back.'},
      {t:'code', tag:'illustration', cap:'The loose reading does not entail the exact one.',
       src:'theorem loose_not_entails_exact : ¬ (ptsAtLeast 4 3 ⊢ (4 ↦ 3)) := by\n  intro hcontra\n  have hne : (9 : Loc) ≠ 4 := by simp\n  have hne\' : (4 : Loc) ≠ 9 := by simp\n  have hloose : ptsAtLeast 4 3 (fun _ => 0) twoCells := by\n    show twoCells 4 = some 3\n    unfold twoCells\n    rw [write_other (Heap.singleton 4 3) 9 4 7 hne\', singleton_same]\n  have h := hcontra (fun _ => 0) twoCells hloose\n  have h9 := congrFun h 9\n  unfold twoCells at h9\n  rw [write_same, singleton_other 4 9 3 hne] at h9\n  exact some_ne_none 7 h9'},
      {t:'p', h:'Two of the three blocks are Unit 07\'s: proving <code>hloose</code> is <code>x16</code>, and the last four lines are <code>x17</code>. The only new line is the one that applies <code>hcontra</code>.'}
    ]},

    {t:'note', kind:'key', title:'The decision, made',
     h:'From here to the last page of this course, an assertion says <b>what you have</b>, not what is true of memory. <code>emp</code> is not “nothing is known about the heap”; it is “the heap is empty”. <code>l ↦ v</code> is not “<code>l</code> holds <code>v</code>”; it is “<code>l</code> holds <code>v</code> and that is all I have”. Unit 07 measured the two candidates by which theorems survive them; this is the one that survives, and the remaining twenty-five units are written in it.'},

    /* ================================================== an assertion that is === */

    {t:'sec', s:'A hypothesis that does not look like an equation'},

    {t:'p', h:'A hypothesis <code>hp : (l ↦ v) σ h</code> displays as a name applied to three arguments. Underneath it is <code>h = Heap.singleton l v</code>, and every tactic that wants an equation finds one, without being told to unfold anything — the same unfolding that let <code>.1</code> find a conjunction under <code>aAnd</code> in Unit 12, and <code>intro</code> find three binders under <code>Entails</code>. <code>subst</code> is the one that pays best.'},

    {t:'trace', title:'What <code>subst</code> does to a folded ownership hypothesis',
     start:'l : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ h l = some v',
     steps:[
       {tac:'subst hp',
        state:'l : Loc\nv : Val\nσ : Store\n⊢ Heap.singleton l v l = some v',
        h:'Both <code>h</code> and <code>hp</code> have left the context. Every occurrence of the heap variable has been replaced by the one-cell heap, so what remains is a lookup in a heap whose text is known — and the goal is now a statement Unit 05 has a law for.'},
       {tac:'exact singleton_same l v',
        state:'',
        h:'That law.'}
     ],
     done:'No goals.'},

    {t:'p', h:'<code>rw [hp]</code> and <code>congrFun hp l</code> reach through the fold in the same way, and which of the three you want depends on what you want left standing. <code>subst</code> removes the heap variable from the whole proof. <code>rw</code> replaces it where it occurs in one goal or one hypothesis, and leaves the equation behind for use again. <code>congrFun hp l</code> abandons the heap altogether and hands you the equation at a single address. The exercise below uses <code>rw</code>, backwards, twice; its notes give the same proof with the other two.'},

    /* ============================================================== the fact === */

    {t:'sec', s:'A value is determined by the resource'},

    {t:'p', h:'Now the first theorem that gets something out of an ownership claim, rather than measuring one claim against another. Suppose two claims are made about the same state: <i>I own <code>l</code>, holding <code>v₁</code></i>, and <i>I own <code>l</code>, holding <code>v₂</code></i>. Both are claims about all of the memory in hand, so both name it completely, and two complete names for one heap can be compared. The values must agree.'},

    {t:'p', h:'The conclusion of that sentence is <code>v₁ = v₂</code>, which is a proposition and not an assertion, so it cannot stand to the right of a turnstile. Lean says so before the proof is begun.'},

    {t:'code', tag:'sketch', cap:'A statement that does not typecheck. Only its type is at issue; there is no proof here to fail.',
     src:'example (l : Loc) (v₁ v₂ : Val) : Prop := aAnd (l ↦ v₁) (l ↦ v₂) ⊢ v₁ = v₂'},

    {t:'state', cap:'The complaint names the slot: the right-hand side of <code>⊢</code> takes an <code>Assertion</code>. The line-and-column prefix is dropped from every error on this page, and an error quoted inside a sentence has its line breaks removed.',
     src:'error: Application type mismatch: The argument\n  v₁ = v₂\nhas type\n  Prop\nbut is expected to have type\n  Assertion\nin the application\n  aAnd (l ↦ v₁) (l ↦ v₂) ⊢ v₁ = v₂'},

    {t:'p', h:'Unit 12 built the wrapper that fixes this, and <code>fact</code>\'s weakness is why it is the right one here. Anything stronger has to constrain the heap as well, and the two candidates fail in opposite directions. Conjoin <code>emp</code> and the theorem becomes false: the heap in question holds a cell. Conjoin <code>l ↦ v₁</code> and it becomes true and says nothing new — that conjunct is the premise handed straight back, which <code>and_left</code> already does in one line. Between the two is the statement worth having: a claim about a resource in, a fact about two values out, and nothing further asserted.'},

    {t:'p', h:'The exercise below proves that theorem, and a second one beside it whose verdict is negative. Read in the first person, <code>(l ↦ v) ⊢ emp</code> says that someone holding a cell may truthfully claim to hold nothing; the exercise refutes it, by choosing the state at which to attack it. A proof you could not find is a fact about you; <code>¬ (P ⊢ Q)</code> is a fact about the logic, and only the second kind can be cited by a later proof. This one is: two units from here the connective that divides a heap is shown to have no projection, and this refutation is the last line of that argument. What fails there fails because ownership, once claimed, cannot be given up.'},

    {t:'ex',
     id: 'm3-1',
     name: 'pointsTo_value_unique / pointsTo_not_emp',
     hard: false,
     why: 'The first theorem is the sentence “a value is determined by the resource”, and it is the shape of every later argument that gets information out of an ownership claim: turn two claims about one heap into one equation between two known heaps, evaluate at an address, strip the constructor. The second is the first entailment in this course proved <b>false</b>, and it is the seed of Unit 14, where two more non-entailments are proved; the first of them is why the frame rule has to be a theorem rather than a convenience. It is also cited by name, once, in Unit 15: it is the last line of the proof that the separating connective has no projection, and the whole of what makes that proof a refutation rather than a failure to find an argument.',
     setup: 'Two theorems in one box, with a <code>sorry</code> between them; delete it when you write the first proof. In the second, <code>h</code> is a proof and not a heap — the course\'s Lean reuses the letter and this is one of the places it does.',
     goal: 'theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by\n  sorry\n\ntheorem pointsTo_not_emp (l : Loc) (v : Val) :\n    ¬ ((l ↦ v) ⊢ emp) := by',
     hints: [
       'Unfolded, the first goal is <code>∀ σ h, (h = Heap.singleton l v₁ ∧ h = Heap.singleton l v₂) → v₁ = v₂</code>. The second is <code>(∀ σ h, h = Heap.singleton l v → h = Heap.empty) → False</code>: you are given a function, and you have to produce a contradiction out of it.',
       'First: two names for one heap make the two heaps equal, and two heaps that are equal agree at every address — so read both at <code>l</code>, where you know what each of them holds. Second: the hypothesis is a claim about <i>every</i> state, so you get to choose the state at which to attack it. Choose the one-cell heap, which satisfies the premise by construction, and see what the hypothesis then asserts about it.',
       'First: <code>intro</code> with a pattern for the conjunction, then a <code>have</code> stating the equation between the two singleton heaps, closed by rewriting backwards with each half of the hypothesis; then the two lookup laws, then <code>Option.some.inj</code> — introduced in Unit 02 and needed here for the first time. Second: <code>intro</code> the entailment, then apply it to a store, a heap and a proof of the premise; the premise is an equation both of whose sides are the same text, so <code>rfl</code> proves it.',
       'First line of the first proof: <code>intro σ h ⟨h1, h2⟩</code>, which gives you two hypotheses of type <code>(l ↦ v₁) σ h</code> and <code>(l ↦ v₂) σ h</code> and a goal <code>fact (fun x => v₁ = v₂) σ h</code>. First line of the second, after <code>intro hcontra</code>: <code>have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl</code>, which leaves you holding <code>emp (fun x => 0) (Heap.singleton l v)</code> — an equation saying that a one-cell heap is the empty one.'
     ],
     sol: 'theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by\n  intro σ h ⟨h1, h2⟩\n  have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]\n  rw [singleton_same, singleton_same] at this\n  exact Option.some.inj this\n\ntheorem pointsTo_not_emp (l : Loc) (v : Val) :\n    ¬ ((l ↦ v) ⊢ emp) := by\n  intro hcontra\n  have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl\n  have : Heap.singleton l v l = Heap.empty l := by rw [h]\n  rw [singleton_same] at this\n  exact absurd this (by simp [Heap.empty])',
     solNote: 'Neither proof mentions <code>pointsTo</code> or <code>emp</code> after its first line. Both definitions do their whole job by being equations, and then the argument is about heaps.',
     expl: 'The first proof transports one heap equation along another until both sides are singleton heaps, reads them at <code>l</code>, and strips the <code>some</code>. The second chooses the one state where the premise is free and the conclusion is absurd, and then collides <code>some v</code> against <code>none</code> — the same collision Unit 07 used, reached this time through an entailment instead of through a heap.',
     walk: [
       {tac:'intro σ h ⟨h1, h2⟩', h:'Four names at once: the store, the heap, and the conjunction split into its two halves as it arrives. The goal comes down from an entailment to <code>fact (fun x => v₁ = v₂) σ h</code>, a statement at one state.'},
       {tac:'have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]', h:'The heart of it. The stated equation is between two <i>known</i> heaps read at <code>l</code>; the proof of it rewrites <b>backwards</b> with each half of the hypothesis, which turns each singleton back into <code>h</code> and leaves <code>h l = h l</code>, closed by the <code>rfl</code> <code>rw</code> tries at the end. Forwards would fail: there is no <code>h</code> in the stated equation to rewrite.'},
       {tac:'rw [singleton_same, singleton_same] at this', h:'Two rewrites at the hypothesis, one per side, each replacing a lookup in a one-cell heap at its own address by the value stored there. <code>this</code> becomes <code>some v₁ = some v₂</code>.'},
       {tac:'exact Option.some.inj this', h:'Constructors are injective, so equal <code>some</code>s have equal contents. This is the goal — because <code>fact (fun x => v₁ = v₂) σ h</code> unfolds to <code>v₁ = v₂</code>, and <code>exact</code> checks up to unfolding.'},
       {tac:'intro hcontra', h:'The second theorem. <code>¬ P</code> is <code>P → False</code>, so introducing the negation gives you the entailment as a hypothesis and <code>False</code> as the goal.'},
       {tac:'have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl', h:'The entailment applied to a store, a heap and a premise. The store is arbitrary and this is the course\'s habitual one. The heap is chosen: the one-cell heap, which satisfies <code>l ↦ v</code> because <code>l ↦ v</code> at that heap is <code>Heap.singleton l v = Heap.singleton l v</code> — which is why the third argument is <code>rfl</code>. What comes back is <code>emp</code> at that heap.'},
       {tac:'have : Heap.singleton l v l = Heap.empty l := by rw [h]', h:'The returned equation is between whole heaps; read it at <code>l</code>. The subproof rewrites the goal with <code>h</code>, turning the left-hand side into <code>Heap.empty l</code> and leaving <code>rw</code>\'s trailing <code>rfl</code> to close it.'},
       {tac:'rw [singleton_same] at this', h:'The left-hand side is a lookup at the address the singleton was built at, so it is <code>some v</code>. The right-hand side is left alone: <code>rw</code> will not unfold <code>Heap.empty</code>.'},
       {tac:'exact absurd this (by simp [Heap.empty])', h:'<code>this</code> now says <code>some v = Heap.empty l</code>, and the bracketed subproof says it does not — <code>simp [Heap.empty]</code> is the way to ask for <code>Heap.empty</code>\'s value by name, and then <code>some v = none</code> is refuted because constructors are distinct. <code>absurd</code> takes a proof and a refutation and returns anything, including <code>False</code>.'}
     ],
     deep: [
       {t:'trace', title:'Two claims into one equation, tactic by tactic',
        start:'l : Loc\nv₁ v₂ : Val\n⊢ aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact fun x => v₁ = v₂',
        steps:[
          {tac:'intro σ h ⟨h1, h2⟩',
           state:'l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\n⊢ fact (fun x => v₁ = v₂) σ h',
           h:'Both halves of the conjunction arrive already separated, and both display folded. Neither has been recognised as an equation yet, and neither needs to be until something asks.'},
          {tac:'have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]',
           state:'l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\nthis : Heap.singleton l v₁ l = Heap.singleton l v₂ l\n⊢ fact (fun x => v₁ = v₂) σ h',
           h:'The step that does the work, and the only one that touches the hypotheses. What it produces mentions neither <code>h</code> nor <code>↦</code>: two one-cell heaps, read at the address they were built at.'},
          {tac:'rw [singleton_same, singleton_same] at this',
           state:'l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\nthis : some v₁ = some v₂\n⊢ fact (fun x => v₁ = v₂) σ h',
           h:'Both lookups computed. From here it is a fact about <code>Option</code>, and the goal — which still displays folded — is <code>v₁ = v₂</code> underneath.'}
        ],
        done:'<code>Option.some.inj this</code> closes it.'},
       {t:'trace', title:'The refutation, tactic by tactic',
        start:'l : Loc\nv : Val\n⊢ ¬l ↦ v ⊢ emp',
        steps:[
          {tac:'intro hcontra',
           state:'l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\n⊢ False',
           h:'The goal is now the emptiest goal there is, and everything from here is a search for something to contradict. Look at which of the two turnstiles in the opening goal survived: the entailment moved into the context, and the display\'s own turnstile stayed where it was.'},
          {tac:'have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl',
           state:'l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\nh : emp (fun x => 0) (Heap.singleton l v)\n⊢ False',
           h:'The chosen state, and what the entailment says about it. <code>h</code> is folded, and underneath it is <code>Heap.singleton l v = Heap.empty</code> — a false equation between two heaps whose texts are both known.'},
          {tac:'have : Heap.singleton l v l = Heap.empty l := by rw [h]',
           state:'l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\nh : emp (fun x => 0) (Heap.singleton l v)\nthis : Heap.singleton l v l = Heap.empty l\n⊢ False',
           h:'The equation read at one address. Any address would do for the shape of the argument; <code>l</code> is the one where the two sides visibly differ.'},
          {tac:'rw [singleton_same] at this',
           state:'l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\nh : emp (fun x => 0) (Heap.singleton l v)\nthis : some v = Heap.empty l\n⊢ False',
           h:'One side computed. The other has not moved, and will not until asked by name.'}
        ],
        done:'The last line supplies the refutation and closes the goal.'},
       {t:'p', h:'The first proof has an alternative that spends <code>subst</code> where the corpus spends a backwards rewrite. It is the same argument with the heap eliminated first instead of restored twice, and it is one line shorter.'},
       {t:'code', tag:'illustration', cap:'The same theorem, taking the hypothesis apart in the other order.',
        src:'example (l : Loc) (v₁ v₂ : Val) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by\n  intro σ h ⟨h1, h2⟩\n  subst h1\n  have := congrFun h2 l\n  rw [singleton_same, singleton_same] at this\n  exact Option.some.inj this'},
       {t:'state', cap:'The context after <code>subst h1</code>. The heap variable is gone; the second hypothesis is now a claim about a heap whose text is known.',
        src:'l : Loc\nv₁ v₂ : Val\nσ : Store\nh2 : (l ↦ v₂) σ (Heap.singleton l v₁)\n⊢ fact (fun x => v₁ = v₂) σ (Heap.singleton l v₁)'},
       {t:'p', h:'The third line is <code>congrFun h2 l</code> and not a second <code>subst</code>, and the reason is visible in that context. <code>subst</code> eliminates a <i>variable</i>, and there is no longer one: <code>h2</code> is an equation between two heaps whose texts are both spelled out. Ask for it anyway and Lean says exactly that — <code>Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)</code>, quoting <code>(l ↦ v₂) σ (Heap.singleton l v₁)</code> back at you. One <code>subst</code> per heap variable is all there is; after the first, an equation between heaps can only be read at a point.'},
       {t:'p', h:'One consequence of the first theorem belongs in front of you before the closing section, which is built on it: if the two values are known to differ, the conjunction is unsatisfiable rather than uninformative.'},
       {t:'code', tag:'illustration', cap:'Two different values at one address, claimed at once, entail falsehood.',
        src:'example (l : Loc) (v₁ v₂ : Val) (hne : v₁ ≠ v₂) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ aFalse := by\n  intro σ h hp\n  exact absurd (pointsTo_value_unique l v₁ v₂ σ h hp) hne'}
     ],
     pitfall: 'Writing the <code>have</code> in the first proof with <code>rw [h1, h2]</code> instead of <code>rw [← h1, ← h2]</code>. The direction is not a matter of taste: the goal you are proving is <code>Heap.singleton l v₁ l = Heap.singleton l v₂ l</code>, in which <code>h</code> does not occur, so rewriting forwards has nothing to match and Lean reports <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern h in the target expression</code>. Backwards, each hypothesis is used right to left, replacing a singleton heap by <code>h</code>. The general rule is Unit 02\'s and this is the place it bites hardest: <code>rw [e]</code> looks for the <i>left</i> side of <code>e</code> in the goal. The second proof invites a different mistake: attacking the entailment at <code>Heap.empty</code>, because <code>emp</code> is what you are trying to contradict. The heap is constrained by the <i>premise</i> and not by the conclusion, and the empty heap does not satisfy <code>l ↦ v</code>. Write <code>hcontra (fun _ => 0) Heap.empty rfl</code> and it is the third argument that is refused: <code>the argument rfl has type ?m.9 = ?m.9 but is expected to have type (l ↦ v) (fun x => 0) Heap.empty</code> — the numeral there is Lean\'s own counter and yours will differ. Choose the heap the premise forces, and take the contradiction from whatever the entailment hands back.',
     variants: 'End the first proof with <code>exact this</code> and it fails, because <code>some v₁ = some v₂</code> is not <code>v₁ = v₂</code>: <code>this has type some v₁ = some v₂ but is expected to have type fact (fun x => v₁ = v₂) σ h</code>. The wrapper is not the obstacle — <code>exact</code> unfolds <code>fact</code> without being asked — the constructor is. End the second proof with <code>exact some_ne_none v this</code> instead of the <code>absurd</code> line and it also compiles, which is the shorter route and the one Unit 07 took. Drop the store argument in <code>hcontra (Heap.singleton l v) rfl</code> and the first message is <code>the argument Heap.singleton l v has type Heap but is expected to have type Store</code> — an entailment has three arguments and the heap is the second. Finally, weaken the first theorem\'s conclusion from <code>fact</code> to nothing at all by asking for <code>aFalse</code> instead: that is <i>false</i> when <code>v₁ = v₂</code>, since the conjunction is then satisfied by the one-cell heap. Drop a conjunct from the first theorem and it fails at once — <code>(0 ↦ 3) ⊢ fact (fun _ => (3 : Val) = 4)</code> is refuted by <code>Heap.singleton 0 3</code>, which satisfies the premise and leaves the conclusion <code>3 = 4</code> — and the line where the missing conjunct would have been spent is the backwards rewrite, which has nothing to turn the second singleton back into. Generalise in the other direction and nothing breaks: <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ fact (fun _ => v₁ = v₂)</code> holds with no hypothesis relating the two addresses, but only one of its two cases is the proof above. Where the addresses agree it is that proof; where they differ the premise is unsatisfiable, which is the last section of this page.'
    },

    {t:'p', h:'A last question about <code>emp</code>, left standing since the first section: the equation and the pointwise reading. Nothing so far says they describe the same heaps, and the two are not the same statement — one fixes a function, the other fixes each of its values. Whether they agree is a theorem about assertions, and stating it is half the work.'},

    {t:'ex',
     id: 'x30',
     name: 'emp as “nothing anywhere”',
     hard: false,
     why: 'A design exercise, so what it drills is the statement and not the proof: you have to decide what relation holds between two assertions, and at which of the two available strengths. It also settles the doubt the first section left open — that writing ownership as an equation between heaps is a genuine choice and not a trick that quietly says less than it appears to. And it is the first proof on this page whose two halves are not variations of each other: one direction spends the equation, the other manufactures it.',
     setup: 'Nothing is given. Write a <code>theorem</code> of your own relating <code>emp</code> to the assertion <code>fun _ h => ∀ l, h l = none</code>, and prove it. The editor takes whatever you write, so a different correct statement of the same fact is accepted; the placeholder in the box is there only so the box has something to run, and you should delete it.',
     goal: '-- Delete the line below and write your own `theorem` about `emp`.\n-- Any correct statement of the fact will be accepted.\nexample : True := by',
     hints: [
       'At a state <code>σ h</code>, <code>emp σ h</code> is a single equation between two functions: <code>h = Heap.empty</code>. The other assertion at that same state says <code>∀ l, h l = none</code> — a family of equations between values, one per address. Both are <code>Assertion</code>s, so what you write has to be a statement relating two assertions: not an implication between two propositions, and not an equation between the two assertions themselves — Unit 12 priced that one, and it needs an axiom this course does without.',
       'Each direction is a small argument you can give in words first. Left to right: you are told the heap <i>is</i> the empty one, and asked what it holds at an arbitrary address — so replace it and look. Right to left: you are told what it holds at every address, and asked to prove an equation between two whole functions — so this is the move Unit 03 exists for. Both arguments go through, and that is what decides which of Unit 12\'s two relations between assertions you should be stating: one carries a single direction, the other is built from two of the first and is symmetric.',
       'The statement is <code>emp ⊣⊢ fun _ h => ∀ l, h l = none</code>. Split it with <code>constructor</code>. The left branch needs one more <code>intro</code> than you might expect, because after the store, the heap and the premise there is still an address to introduce. The right branch needs <code>funext</code>, on a goal that does not look like an equation between functions until you remember what <code>emp</code> is. Both branches end by asking for <code>Heap.empty</code>\'s value by name.',
       'Open with <code>constructor</code>, then <code>· intro σ h hp l</code>. That leaves <code>hp : emp σ h</code> and the goal <code>h l = none</code>; <code>rw [hp]</code> turns it into <code>Heap.empty l = none</code>, which <code>simp [Heap.empty]</code> closes. The second branch opens <code>· intro σ h hp</code> and then <code>funext l</code>.'
     ],
     sol: 'theorem emp_iff_all_none : emp ⊣⊢ fun _ h => ∀ l, h l = none := by\n  constructor\n  · intro σ h hp l\n    rw [hp]\n    simp [Heap.empty]\n  · intro σ h hp\n    funext l\n    simp [Heap.empty, hp l]',
     solNote: 'If you climbed all four hints and are still stuck, open this without guilt — the exercise is the statement as much as the proof, and there is a second and a third correct statement in the <i>variants</i> note below.',
     expl: 'Two assertions, each entailing the other, so the statement is an <code>⊣⊢</code> and the proof has two branches. Going right, the equation is spent by rewriting with it and the empty heap is then evaluated. Going left, the equation has to be built, and building an equation between two functions from a fact about each of their values is exactly what <code>funext</code> does.',
     walk: [
       {tac:'constructor', h:'<code>⊣⊢</code> is a folded <code>def</code> whose body is a conjunction of two entailments, so <code>constructor</code> finds one constructor with two fields and leaves two goals, <code>case left</code> and <code>case right</code>.'},
       {tac:'· intro σ h hp l', h:'Four binders, not three. The first three are the entailment\'s; the fourth is there because the goal after them, <code>(fun _ h => ∀ l, h l = none) σ h</code>, reduces to a <code>∀</code> and <code>intro</code> keeps going until it runs out of binders. Stopping at three is not a mistake: the goal is then <code>∀ (l : Loc), h l = none</code> and the next two lines close it with no change, because both of them work under a leading <code>∀</code>. Taking the fourth binder here puts the address in the context, which is where the rest of the branch talks about it.'},
       {tac:'rw [hp]', h:'<code>hp : emp σ h</code> is an equation between heaps, and rewriting with it replaces <code>h</code> in the goal, leaving <code>Heap.empty l = none</code>.'},
       {tac:'simp [Heap.empty]', h:'The one thing left is the value of the empty heap at an address, which is a definition and has to be asked for by name. <code>rw</code>\'s trailing <code>rfl</code> did not do it: Unit 09 recorded that it will not unfold <code>Heap.empty</code>.'},
       {tac:'· intro σ h hp', h:'The other direction. Three binders this time, because <code>emp σ h</code> unfolds to an equation rather than to a quantifier, so there is nothing more for <code>intro</code> to take.'},
       {tac:'funext l', h:'The goal is <code>emp σ h</code>, which does not look like an equation between functions and is one: <code>emp</code> unfolds to <code>h = Heap.empty</code>, and both sides are heaps, which are functions. <code>funext</code> reduces it to <code>h l = Heap.empty l</code> at an arbitrary <code>l</code>.'},
       {tac:'simp [Heap.empty, hp l]', h:'Two rules: the definition of the empty heap, which turns the right-hand side into <code>none</code>, and the hypothesis instantiated at <code>l</code>, which turns the left-hand side into <code>none</code> as well. The hypothesis goes in already applied: <code>hp</code> alone is a <code>∀</code>, and <code>simp</code> would take it as a rewrite rule, which also works here but says less about what is going on.'}
     ],
     deep: [
       {t:'trace', title:'Both branches, at the point where they differ',
        start:'⊢ emp ⊣⊢ fun x h => ∀ (l : Loc), h l = none',
        steps:[
          {tac:'constructor',
           state:'case left\n⊢ emp ⊢ fun x h => ∀ (l : Loc), h l = none\n\ncase right\n⊢ (fun x h => ∀ (l : Loc), h l = none) ⊢ emp',
           h:'Two goals, and the second runs the other way. Both display with two turnstiles — the goal\'s own and <code>Entails</code> — and in <code>case right</code> the lambda has kept its brackets, unlike the one printed above: a <code>fun</code> body runs as far to the right as it can, so a lambda on the <i>left</i> of <code>⊢</code> has to be closed off and one on the right never does.'},
          {tac:'· intro σ h hp l',
           state:'case left\nσ : Store\nh : Heap\nhp : emp σ h\nl : Loc\n⊢ h l = none',
           h:'The first branch, after the fourth <code>intro</code>. The equation is in the context and the goal is about one address.'},
          {tac:'rw [hp]',
           state:'case left\nσ : Store\nh : Heap\nhp : emp σ h\nl : Loc\n⊢ Heap.empty l = none',
           h:'The heap variable is gone from the goal. What is left is not closed by the <code>rfl</code> <code>rw</code> attempts, because that will not unfold a definition.'},
          {tac:'· intro σ h hp',
           state:'case right\nσ : Store\nh : Heap\nhp : ∀ (l : Loc), h l = none\n⊢ emp σ h',
           h:'The second branch. Notice the asymmetry: the hypothesis has unfolded to a readable <code>∀</code> because <code>intro</code> had to look inside it to find three binders, while the goal is still folded as <code>emp σ h</code>.'},
          {tac:'funext l',
           state:'case right\nσ : Store\nh : Heap\nhp : ∀ (l : Loc), h l = none\nl : Loc\n⊢ h l = Heap.empty l',
           h:'<code>funext</code> looked through <code>emp</code> to find an equation between two functions, and left the equation at an arbitrary point. Both sides are now lookups.'}
        ],
        done:'One <code>simp</code> per branch closes both.'},
       {t:'p', h:'The theorem is what licenses reading <code>emp</code> aloud as “nothing is allocated anywhere” while writing it as an equation — the reading a reader will use and the spelling every proof will use are now provably the same assertion. It costs eight lines once, and after it nothing on the page has to hedge.'},
       {t:'p', h:'The first section of this page set a third spelling aside — <i>the domain of <code>h</code> is empty</i>, which has to be written <code>∀ l, ¬ defined h l</code> — on the grounds that it is the pointwise one in other clothing. That claim is a theorem as well, and it costs one <code>cases</code>: a lookup answers in one of two ways, and going right to left the <code>some</code> branch is the one the hypothesis forbids.'},
       {t:'code', tag:'illustration', cap:'The third spelling, proved to be the same assertion as the first.',
        src:'example : emp ⊣⊢ fun _ h => ∀ l, ¬ defined h l := by\n  constructor\n  · intro σ h hp l ⟨w, hw⟩\n    rw [hp] at hw\n    simp [Heap.empty] at hw\n  · intro σ h hp\n    funext l\n    cases hl : h l with\n    | none => simp [Heap.empty]\n    | some w => exact absurd ⟨w, hl⟩ (hp l)'}
     ],
     pitfall: 'Forgetting <code>funext</code> in the second branch and going straight for <code>simp [Heap.empty, hp]</code> on the goal <code>emp σ h</code>. It reports <code>`simp` made no progress</code> rather than making partial progress, which is the least informative failure Lean has, and it is the same one you would get for the same reason at any other goal that is an equation between heaps with no <code>funext</code> in front of it. The hypothesis is about values and the goal is about functions; something has to move between those two levels, and only <code>funext</code> does.',
     variants: 'Two other statements are correct and would be accepted. <b>Two separate entailments</b> — <code>emp ⊢ fun _ h => ∀ l, h l = none</code> and its converse, as two theorems — is the same content unpackaged; it buys you the two halves as citable names, at the cost of the single name that later prose can point at. <b>A pointwise <code>↔</code></b>, <code>∀ σ h, emp σ h ↔ ∀ l, h l = none</code>, is provable by the same tactics with the two state binders hoisted to the front, and it buys the ability to <code>rw</code> with it at a state — but it is not a statement of the logic, so it cannot be chained with <code>entails_trans</code> or appear in any later rule. A third form, the <i>equality</i> <code>emp = fun _ h => ∀ l, h l = none</code>, is also true and is the one to avoid: proving it needs <code>propext</code>, exactly as Unit 12\'s equality of assertions did, and <code>⊣⊢</code> exists so that no theorem in this course has to depend on that axiom. Finally, drop the <code>∀</code> and state it at a fixed address — <code>emp ⊣⊢ fun _ h => h 0 = none</code> — and it is false: the heap holding only address 1 satisfies the right-hand side and not the left.'
    },

    /* ============================================================ two cells === */

    {t:'sec', s:'Two cells, and the conjunction that cannot hold them'},

    {t:'p', h:'A specification of anything larger than one cell needs to say <i>I own this cell and that one</i>. The only conjunction available is <code>aAnd</code>, and the first-person reading says at once what it will do: <code>l₁ ↦ v₁</code> claims that the whole heap in hand is the cell <code>l₁</code>, and <code>l₂ ↦ v₂</code> claims that the whole heap in hand is the cell <code>l₂</code>. Both, at once, about one heap. If the addresses differ, the two claims are two different complete descriptions of the same object, and no heap can answer to both.'},

    {t:'code', tag:'illustration', cap:'Two cells at distinct addresses, conjoined classically. The proof is the first theorem of <code>m3-1</code> with <code>singleton_other</code> in place of the second <code>singleton_same</code>, which turns an equation between two <code>some</code>s into a collision between <code>some</code> and <code>none</code>.',
     src:'example (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ aFalse := by\n  intro σ h ⟨h1, h2⟩\n  have he : Heap.singleton l₁ v₁ l₁ = Heap.singleton l₂ v₂ l₁ := by rw [← h1, ← h2]\n  rw [singleton_same, singleton_other l₂ l₁ v₂ hne] at he\n  exact some_ne_none v₁ he'},

    {t:'p', h:'So <code>aAnd</code> is not a weak way of saying <i>both cells</i>; it is a way of saying something else. Together with the exhibit in <code>m3-1</code>\'s notes — addresses equal, values different — it is unsatisfiable in every case but one: where both conjuncts are the same claim, and one cell is all you have.'},

    {t:'dod', h:'You can write <code>emp</code> and <code>pointsTo</code> as equations and say what an equation gives a later proof that a lookup or a quantified statement does not; read a goal containing two turnstiles and no brackets; state which entailments between the exact and the loose reading hold, and refute the one that does not; spend a folded ownership hypothesis with <code>subst</code>, <code>rw</code> or <code>congrFun</code>; prove that two ownership claims at one address force their values to agree, and say why the conclusion is wrapped in <code>fact</code>; and prove an entailment false by choosing the state at which to attack it.'},

    {t:'p', h:'<code>l₁ ↦ v₁</code> and <code>l₂ ↦ v₂</code> each claim to own <i>all</i> of the heap they are evaluated at, so <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂)</code> is nearly always false and is never what you mean. Saying “I own this cell <i>and separately</i> that one” needs a conjunction that divides the heap between its conjuncts. There is exactly one way to write it, and Module 2 has already proved everything it needs.'}

  ]
});
