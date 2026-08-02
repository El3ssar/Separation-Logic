registerChapter({
  id: 'symbolic',
  num: '29',
  phase: 'Phase 6 · Verification',
  title: 'Symbolic execution',
  blurb: 'The four moves a verification is made of — split, frame, apply, renormalise — the second way of discharging the frame rule’s third hypothesis, and three programs verified without the word Exec appearing in any of their proofs.',

  orient: {
    youWill: [
      'Name the four rules a verification is built from, and say which of the four steps requires a decision.',
      'Prove that <code>write</code> and <code>free</code> leave the store alone, and turn that into a proof that they preserve <i>every</i> assertion.',
      'Say which of the two <code>Preserves</code> dischargers applies to a given command and frame, and name the pairing for which neither does.',
      'Re-prove Unit 23&rsquo;s <code>readAndFree</code> from four applications of structural rules, with no store, no heap and no <code>Exec</code> in it.',
      'Read a store-dependent postcondition and say why the fact that would simplify it has nowhere to enter.',
      'Move a pure fact across a <code>∗</code> and recognise, in a stuck goal, which of Units 15 to 17&rsquo;s laws will move it.',
      'Choose the assertion between two commands by working out what the second command&rsquo;s footprint needs.',
      'Say why a specification proved for <code>(c₁ ;; c₂) ;; c₃</code> does not apply to <code>c₁ ;; (c₂ ;; c₃)</code>, and repair it.'
    ],
    needs: [
      'Unit 22: <code>Hoare</code>, <code>hoare_seq</code>, <code>hoare_consequence</code>, and named arguments <code>(Q := …)</code>.',
      'Unit 23: <code>hoare_load</code>, <code>hoare_write</code>, <code>hoare_free</code>, and <code>readAndFree_spec</code> — the proof this unit replaces.',
      'Unit 24: <code>Preserves</code>, <code>HeapOnly</code>, <code>preserves_of_heapOnly</code>, <code>not_heapOnly_pure</code>. Unit 27: <code>hoare_frame</code>.',
      'Unit 12: <code>aAnd</code>, <code>fact</code>, <code>entails_refl</code>, <code>entails_trans</code>. Units 15–17: <code>star_comm</code>, <code>star_mono_right</code>, <code>star_assoc_left</code>, <code>star_emp_left</code>, <code>star_pure_left</code>.'
    ],
    payoff: 'Everything after this unit uses the frame rule without discussing it. The shape of the proofs on this page — a chain of <code>hoare_seq</code> steps, each a framed small rule wrapped in a consequence — is what you reach for first from here on, and the next unit asks you to drive it unaided on a program twice this size, and to find out where it stops paying.'
  },

  blocks: [

    /* ==================================================== the method ==== */

    {t:'p', h:"Routine means this: for every command in the program, the same four steps in the same order, and at no point does the argument descend below the level of triples. Nothing in this unit is a new fact about heaps. Everything in it is a way of arranging facts you already have, so that the arrangement does the work instead of you."},

    {t:'p', h:"There is a test that tells you whether you are doing it, and you are held to it. <b>If <code>Exec</code> appears in one of your proofs, you are missing a lemma.</b> Unit 23&rsquo;s <code>readAndFree_spec</code> fails that test: it names a store, a heap built out of another heap, and an <code>Exec.seq</code> derivation assembled by hand. That proof is correct and it is a dead end — change one command in the program and nothing in it survives, because every line of it is about <i>this</i> program&rsquo;s run rather than about the two commands it is made of."},

    {t:'txt', cap:'The four moves. Every verification on this page is these, repeated.',
     src:"To prove   Hoare P (c₁ ;; c₂ ;; … ;; cₙ) Q :\n\n  SPLIT        hoare_seq          choose the assertion between cᵢ and cᵢ₊₁\n  FRAME        hoare_frame        cut off the part of the state cᵢ does not touch\n  APPLY        a small rule       hoare_load, hoare_write, hoare_free, hoare_assign\n  RENORMALISE  hoare_consequence  reshape ∗ until the next command's rule fits"},

    {t:'p', h:"<b>Split.</b> <code>hoare_seq</code> takes <code>Hoare P c₁ Q</code> and <code>Hoare Q c₂ R</code> and gives you <code>Hoare P (c₁ ;; c₂) R</code>. Its <code>Q</code> is implicit, and Unit 22 showed you the error you get when nothing determines it. The way to find it is to stop looking at <code>c₁</code> and look at <code>c₂</code>: write down the cells <code>c₂</code>&rsquo;s rule owns, write down the facts about the store that rule needs, and put everything else — the cells <code>c₂</code> will not touch — beside it under a <code>∗</code>."},

    {t:'p', h:"<b>Frame.</b> The small rules mention one cell. The state has more than one cell in it. <code>hoare_frame</code> is what closes that gap, and it asks for three things: the triple <code>Hoare P c Q</code>, which is the small rule; <code>HeapLocal c</code>, which Units 24 to 26 proved for every command in the language, so it is always a name you look up; and <code>Preserves c R</code>, which depends on the frame <code>R</code> you chose and is the only one of the three that can cost you anything."},

    {t:'p', h:"<b>Apply</b> is looking up the rule for the command. <b>Renormalise</b> is the step that has no command in it at all. What the previous step handed you is a triple whose postcondition is some arrangement of <code>∗</code>, and what the next step wants is a different arrangement of the same conjuncts. <code>hoare_consequence</code> takes an entailment on each side; the precondition side is almost always <code>entails_refl _</code>, because you are not weakening anything, and the postcondition side is a chain of Unit 15&rsquo;s and Unit 16&rsquo;s laws joined by <code>entails_trans</code>. The whole of it is <code>∗</code>-algebra, and no heap is ever named inside it."},

    {t:'note', kind:'key', title:'The one creative act', h:"Choosing the assertion between two commands is verifying the program. Everything else in this unit — which frame to cut, which small rule to apply, which law reshapes the star — is forced by that choice, and a reader who has made the choice can finish the proof by following the types. When the proofs below get long, their length is bookkeeping and their content is one line: the <code>(Q := …)</code>."},

    /* ============================================ the third hypothesis ==== */

    {t:'sec', s:'The hypothesis that costs'},

    {t:'p', h:"Both stores in <code>Preserves c R</code> come out of one run, and its heap argument does not move: <code>R</code> must hold at the finishing store having held at the starting one, at one and the same <code>hFrame</code>. The heap side of that is free — <code>hFrame</code> is the frame, and locality already said the command does not go near it. The store side is not, and it is the whole content of the hypothesis."},

    {t:'p', h:"Unit 24 gave one way to discharge it, and it works on the assertion rather than on the command: if <code>R</code> never consults the store, then nothing a command does to the store can falsify it. That is <code>preserves_of_heapOnly</code>, and with <code>heapOnly_pointsTo</code>, <code>heapOnly_emp</code> and <code>heapOnly_star</code> it covers every frame built out of <code>↦</code> and <code>∗</code> — which is most of them."},

    {t:'p', h:"It does not cover the frame in the very next proof. Framing a <code>free</code> is going to require carrying <code>pure (fun σ => σ x = v)</code> across it, and that assertion is a statement about the store; Unit 24 refuted <code>HeapOnly</code> for exactly this shape in <code>not_heapOnly_pure</code>. Trying it anyway produces the clearest possible statement of what is wrong:"},

    {t:'code', tag:'sketch', cap:'The frame is a fact about the store, so the heap-only route cannot start.',
     src:"example (φ : Store → Prop) (l : Loc) (e : Atom) : Preserves (.write l e) (pure φ) :=\n  preserves_of_heapOnly _ (by exact fun σ σ' h hr => hr)"},

    {t:'state', cap:'What Lean says. The two stores are different stores, and no amount of arranging will make one proof serve for both.',
     src:"error: Type mismatch\n  hr\nhas type\n  _root_.pure φ σ h\nbut is expected to have type\n  _root_.pure φ σ' h"},

    {t:'p', h:"So make the hypothesis a claim about the command instead. If running <code>c</code> cannot change the store at all, then <code>σ</code> and <code>σ'</code> in that error message are the same store, and the mismatch disappears — for <i>every</i> assertion, not only the store-blind ones."},

    {t:'code', cap:'A property of a command, in the shape of Unit 24&rsquo;s locality properties: quantify over runs, and say what the run left alone.',
     src:"def StoreStable (c : Cmd) : Prop := ∀ s s', Exec c s s' → s'.store = s.store"},

    {t:'p', h:"The definition mentions <code>Exec</code>, and so do <code>HeapLocal</code> and <code>Preserves</code>. That is where <code>Exec</code> belongs: in the statement of a property of the language, proved once. The rule at the top of this page is about <i>verifications</i> — proofs that a particular program meets a particular specification — and none of the three properties is one of those."},

    {t:'p', h:"Which commands have it? <code>write</code> and <code>free</code> change the heap and nothing else, so both should. Each has exactly one <code>Exec</code> rule that can produce it, and that rule builds the final state out of the initial one with the store slot copied across, so once you have looked at the derivation there is nothing left to prove. The third theorem is the payoff: store-stability of <code>c</code> gives <code>Preserves c R</code> for an <code>R</code> you never look at."},

    /* -------------------------------------------------------------- x57 --- */

    {t:'ex',
     id:'x57',
     name:'storeStable_write / storeStable_free / preserves_of_storeStable',
     why:"This is the second discharger for the frame rule&rsquo;s third hypothesis, and the one that gets used for every framed <code>write</code> and every framed <code>free</code> on the rest of this page. The third theorem is the interesting one: it takes a fact about a <i>command</i> and produces the <code>Preserves</code> obligation for an assertion it never inspects, which is what makes the frame side of a verification stop depending on what you chose to frame. Honest note: <code>preserves_of_storeStable</code> is cited three times in this unit and nowhere else in the corpus — Unit 30&rsquo;s capstone takes the direct semantic route. What travels is the pattern, not the name.",
     setup:"<code>StoreStable</code> is given. <code>Preserves</code>, <code>Exec</code> and inversion by <code>cases</code> are Units 24, 19 and 19.",
     goal:"theorem storeStable_write (l : Loc) (e : Atom) : StoreStable (.write l e) := by\n  sorry\n\ntheorem storeStable_free (l : Loc) : StoreStable (.free l) := by\n  sorry\n\ntheorem preserves_of_storeStable {c : Cmd} (h : StoreStable c) (R : Assertion) :\n    Preserves c R := by",
     hints: [
       "Unfolded, <code>StoreStable (.write l e)</code> is <code>∀ s s', Exec (.write l e) s s' → s'.store = s.store</code>: for any run of the write, the final store equals the initial one. Unfolded, <code>Preserves c R</code> is <code>∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame</code>: you are handed a run, a heap, and <code>R</code> at the starting store, and must produce <code>R</code> at the finishing store.",
       "For the first two: only one of <code>Exec</code>&rsquo;s rules can have produced a run of a write, and that rule says what the final state is. Once the final state is written out rather than named, the two sides of the equation are the same term. For the third: if the two stores are equal then <code>R s'.store hFrame</code> and <code>R s.store hFrame</code> are the same proposition, so the proof is the hypothesis you were given, once the goal has been rewritten.",
       "Three tactics between them. <code>intro</code> to take the universally quantified things; <code>cases</code> on the execution hypothesis to replace the final state by the one the rule built; <code>rfl</code>. For the third, no <code>cases</code> — apply the store-stability hypothesis to get an equation and <code>rw</code> with it.",
       "<code>intro s s' hex</code> leaves <code>⊢ s'.store = s.store</code> with <code>hex : Exec (Cmd.write l e) s s'</code>. <code>cases hex</code> replaces <code>s'</code> throughout by <code>{ store := s.store, heap := s.heap.write l (Atom.eval s.store e) }</code>, so the goal becomes an equation between that structure&rsquo;s <code>.store</code> field and <code>s.store</code>, which <code>rfl</code> closes. For the third, <code>h s s' hex : s'.store = s.store</code>, so <code>rw [h s s' hex]</code> turns <code>⊢ R s'.store hFrame</code> into <code>⊢ R s.store hFrame</code>."
     ],
     sol:"theorem storeStable_write (l : Loc) (e : Atom) : StoreStable (.write l e) := by\n  intro s s' hex; cases hex; rfl\n\ntheorem storeStable_free (l : Loc) : StoreStable (.free l) := by\n  intro s s' hex; cases hex; rfl\n\ntheorem preserves_of_storeStable {c : Cmd} (h : StoreStable c) (R : Assertion) :\n    Preserves c R := by\n  intro s s' hex hFrame hr\n  rw [h s s' hex]; exact hr",
     solNote:"Two identical one-line proofs and a two-line one. The reason the first two are one line each is that inversion did all of the work: <code>cases</code> did not split into branches, it substituted.",
     expl:"The first two theorems are inversions with nothing after them. The third never looks at a command, a heap or an assertion: it takes an equation between stores and rewrites the goal into the hypothesis.",
     walk: [
       {tac:'intro s s\' hex', h:"Takes the two states and the run. The goal is now the equation <code>⊢ s'.store = s.store</code>, with <code>s'</code> still an opaque variable, so nothing is provable yet."},
       {tac:'cases hex', h:"Inversion. <code>Exec.write</code> is the only rule whose conclusion is a run of <code>.write l e</code>, so there is one branch, and in it <code>s'</code> is gone — replaced everywhere by the state that rule builds, <code>{ store := s.store, heap := s.heap.write l (Atom.eval s.store e) }</code>. Two hypotheses appear inaccessible, the old value and the lookup that licensed the write; neither is used."},
       {tac:'rfl', h:"The goal is now <code>{ store := s.store, heap := … }.store = s.store</code>. Projecting a field out of a structure literal reduces, so the two sides are the same term."},
       {tac:'intro s s\' hex  (free)', h:"The same three tactics. <code>Exec.free</code> builds <code>{ store := s.store, heap := s.heap.erase l }</code> — a different heap slot, the same store slot, which is the entire reason the two proofs are identical."},
       {tac:'intro s s\' hex hFrame hr', h:"Four things this time, because <code>Preserves</code> quantifies over the frame heap and hands you <code>R</code> at the starting store. The goal is <code>⊢ R s'.store hFrame</code>; <code>hr : R s.store hFrame</code> is one store away from it."},
       {tac:'rw [h s s\' hex]', h:"<code>h</code> is the store-stability hypothesis, a function; applied to the two states and the run it is the equation <code>s'.store = s.store</code>. Rewriting with it left-to-right replaces <code>s'.store</code> in the goal by <code>s.store</code>, so the goal becomes <code>⊢ R s.store hFrame</code> — literally <code>hr</code>&rsquo;s type."},
       {tac:'exact hr', h:"Hands it back."}
     ],
     deep: [
       {t:'trace', title:'storeStable_write, and what inversion substituted',
        start:"l : Loc\ne : Atom\n⊢ StoreStable (Cmd.write l e)",
        steps:[
          {tac:'intro s s\' hex',
           state:"l : Loc\ne : Atom\ns s' : State\nhex : Exec (Cmd.write l e) s s'\n⊢ s'.store = s.store",
           h:"Nothing here is provable. <code>s'</code> is an arbitrary state; the only thing tying it to <code>s</code> is <code>hex</code>, and <code>hex</code> is not yet an equation."},
          {tac:'cases hex',
           state:"case write\nl : Loc\ne : Atom\ns : State\nold✝ : Val\nhl✝ : s.heap l = some old✝\n⊢ { store := s.store, heap := s.heap.write l (Atom.eval s.store e) }.store = s.store",
           h:"<code>s'</code> has disappeared from the context. That is what inversion on a relation with a computed conclusion does: the rule&rsquo;s conclusion fixes what the final state is, so the variable is eliminated rather than constrained. The two daggered hypotheses are the write rule&rsquo;s premise and the value it overwrote."},
          {tac:'rfl', state:"No goals.", h:"The left-hand side is a projection out of a literal."}
        ]},
       {t:'trace', title:'preserves_of_storeStable — one rewrite and no case analysis',
        start:"c : Cmd\nh : StoreStable c\nR : Assertion\n⊢ Preserves c R",
        steps:[
          {tac:'intro s s\' hex hFrame hr',
           state:"c : Cmd\nh : StoreStable c\nR : Assertion\ns s' : State\nhex : Exec c s s'\nhFrame : Heap\nhr : R s.store hFrame\n⊢ R s'.store hFrame",
           h:"The goal and <code>hr</code> differ in exactly one subterm. <code>R</code> is a variable, so there is nothing to unfold and no possibility of proving this by computation: the only route is to make the two stores syntactically equal."},
          {tac:'rw [h s s\' hex]',
           state:"c : Cmd\nh : StoreStable c\nR : Assertion\ns s' : State\nhex : Exec c s s'\nhFrame : Heap\nhr : R s.store hFrame\n⊢ R s.store hFrame",
           h:"<code>c</code> is still an arbitrary command and <code>hex</code> is still an arbitrary run. Nothing was inspected; the hypothesis was spent."}
        ],
        done:"exact hr"},
       {t:'p', h:"Compare the two shapes. <code>preserves_of_heapOnly</code> is <code>fun s s' _ hFrame hr => h s.store s'.store hFrame hr</code> — it drops the run and repairs the assertion. <code>preserves_of_storeStable</code> keeps the run and repairs the store. Each throws away exactly what the other uses."}
     ],
     pitfall:"Reaching for <code>rfl</code> before <code>cases</code>. The goal <code>⊢ s'.store = s.store</code> looks like it should be true by definition, and it is not: <code>s'</code> is a variable. Lean answers <code>Tactic `rfl` failed: The left-hand side s'.store is not definitionally equal to the right-hand side s.store</code>, which is exactly right and easy to misread as a complaint about projections. The fix is not a different equality tactic; it is to find out where <code>s'</code> came from.",
     variants:"Drop the hypothesis from the third theorem and it becomes false, with a witness the course already has: Unit 24&rsquo;s <code>frame_needs_preserves</code> frames <code>pure (fun σ => σ x = 0)</code> onto <code>.assign x (.const 1)</code>. The point of failure is a single variable — the frame says <code>x</code> is 0, the command sets <code>x</code> to 1, and the postcondition it would license is refuted by the one run. Ask for the first theorem about <code>.assign</code> instead and it is false at one run too: <code>¬ StoreStable (.assign 0 (.const 5))</code> follows from <code>Exec.assign</code> out of the constantly-zero store, then <code>congrFun … 0</code> and <code>simp [Store.set]</code> — the same three lines as <code>load_not_storeStable</code> below, with the run cheaper to build because an assignment reads no memory and so needs no lookup as its premise. <code>.skip</code> is store-stable by the same one-line proof (<code>cases</code> on <code>Exec.skip</code> leaves the state unchanged rather than rebuilt), and nothing in the course needs it, because the only commands anyone ever frames past are the two that write memory."},

    {t:'p', h:"That <code>.load</code> is not store-stable is not a gap in the definition, it is the definition doing its job — the whole point of a load is to change the store. Refuting it costs an actual run: pick an address, put something in it, and read it into a variable that held something else."},

    {t:'code', tag:'illustration', cap:'Address 0 holds 5, the store is constantly 0, and the load makes the two disagree there.',
     src:"theorem load_not_storeStable : ¬ StoreStable (.load 0 0) := by\n  intro hst\n  have hex : Exec (.load 0 0) ⟨fun _ => 0, Heap.singleton 0 5⟩\n      ⟨Store.set (fun _ => 0) 0 5, Heap.singleton 0 5⟩ :=\n    Exec.load (singleton_same 0 5)\n  have h0 := congrFun (hst _ _ hex) 0\n  simp [Store.set] at h0"},

    {t:'p', h:"<code>hst _ _ hex</code> is an equation between two stores, which are functions; <code>congrFun … 0</code> evaluates both at variable 0, where one side is 5 and the other is 0. Supplying the run is the work — a theorem about <i>every</i> run is refuted by producing one, and <code>Exec.load</code> needs the lookup <code>singleton_same 0 5</code> to build it."},

    {t:'tbl', cap:'Two routes to the same obligation. Neither implies the other, and between them they cover every frame in this unit.',
     head:['', '<code>preserves_of_heapOnly</code>', '<code>preserves_of_storeStable</code>'],
     rows:[
       ['the hypothesis is about', 'the frame <code>R</code>', 'the command <code>c</code>'],
       ['proved once per', 'assertion shape', 'command'],
       ['covers', '<code>emp</code>, <code>l ↦ v</code>, any <code>∗</code> of those', 'every assertion whatever'],
       ['fails on', '<code>pure φ</code>, <code>fact φ</code> — anything reading the store', '<code>.load</code>, <code>.assign</code> — anything writing the store'],
       ['available for', 'every command in the language', '<code>.write</code>, <code>.free</code>, <code>.skip</code> — each by inversion, one line']
     ]},

    {t:'p', h:"Read the last two rows together and three cases fall out. A framed load with a <code>↦</code> frame has only the left column, because there is no store-stability theorem for a load and cannot be. A framed write or free with a store fact in the frame has only the right, because <code>pure</code> and <code>fact</code> read the store. A framed <i>load</i> with a store fact in the frame has neither, and nothing on this page frames one — which is the one gap this unit leaves open. Where both columns are filled, as they are for every <code>↦</code> frame below, the proofs take store-stability: it is one name, and it never has to look at the frame."},

    /* ================================================== readAndFree ==== */

    {t:'sec', s:'readAndFree, without the semantics'},

    {t:'p', h:"Unit 23 called <code>readAndFree</code> a defeat: three small rules that would not compose, and a specification proved instead by building the run. The missing tool was the frame rule, and it now exists. Here is what the proof looks like when it is used."},

    {t:'ol', items:[
      "The program is <code>x := [l] ; free(l)</code>, with precondition <code>l ↦ v</code> and postcondition <code>pure (fun σ => σ x = v)</code> — the value is remembered, the cell is gone.",
      "<code>hoare_load</code> ends at <code>pure (fun σ => σ x = v) ∗ (l ↦ v)</code>: the fact the load established, and the cell, still owned and unchanged.",
      "<code>hoare_free</code> starts at <code>l ↦ v</code> and nothing else. So the pure conjunct is not part of what the free rule sees — it is the frame.",
      "The frame rule puts the frame on the <i>right</i> of the <code>∗</code>, so the assertion between the two commands has to be <code>(l ↦ v) ∗ pure (fun σ => σ x = v)</code>, which is the load&rsquo;s postcondition with its two sides swapped.",
      "After the framed free the state is <code>emp ∗ pure (fun σ => σ x = v)</code>, and one unit law finishes it."
    ]},

    {t:'p', h:"Step 3 is the place the previous section was for. The frame here is <code>pure (fun σ => σ x = v)</code>, a claim about the store, so <code>preserves_of_heapOnly</code> is not available and <code>preserves_of_storeStable (storeStable_free l)</code> is. This is the only frame in the unit where the choice is forced; everywhere else both work."},

    /* -------------------------------------------------------------- x58 --- */

    {t:'ex',
     id:'x58',
     name:'readAndFree_framed',
     why:"Unit 23 proved this specification by hand and told you the proof was a dead end. This is the same theorem from four applications of structural rules — <code>hoare_seq</code> once, <code>hoare_consequence</code> twice, <code>hoare_frame</code> once — plus two small rules and two <code>∗</code> laws. It is the clearest before-and-after in the course: put the two proofs side by side and count the objects each one names.",
     setup:"<code>readAndFree x l</code> is <code>.load x l ;; .free l</code>, from Unit 23. Everything else is named in the plan above.",
     goal:"theorem readAndFree_framed (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=",
     hints: [
       "<code>readAndFree x l</code> is <code>.load x l ;; .free l</code>. Unfolded, the goal says: from any state whose heap is exactly the one cell <code>l</code> holding <code>v</code>, the two commands run to some final state, and in that state <code>x</code> holds <code>v</code> and the heap is empty — the emptiness is what <code>pure</code> adds to the bare store fact. Read the two ends against each other: the cell is in the precondition and is not in the postcondition, and the value it held is.",
       "Two commands means one assertion between them, and every other choice follows from it. Ask what the second command needs: the free rule owns the cell and nothing else. The fact the load established is about the store, and it has to survive to the end, so it cannot be part of what the free rule sees — it has to be carried past the free untouched, which is what the frame rule carries. A frame sits on the right of the <code>∗</code>. So between the two commands the cell comes first and the store fact second, and the free leaves <code>emp</code> where the cell was.",
       "For the first command: <code>hoare_load</code>, wrapped in <code>hoare_consequence</code> whose postcondition side is <code>star_comm</code>. For the second: <code>hoare_frame</code> applied to <code>hoare_free</code>, <code>heapLocal_free</code> and <code>preserves_of_storeStable (storeStable_free l)</code>, wrapped in a <code>hoare_consequence</code> whose postcondition side is <code>star_emp_left</code>. The precondition side of both is <code>entails_refl _</code>.",
       "The whole proof is one term, <code>hoare_seq A B</code>, with no <code>(Q := …)</code> needed — <code>A</code>&rsquo;s type determines the middle assertion. <code>A</code> is <code>hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _)</code>. Write that first and let Lean tell you what <code>B</code> must prove."
     ],
     sol:"theorem readAndFree_framed (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=\n  hoare_seq\n    (hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _))\n    (hoare_consequence (entails_refl _)\n      (hoare_frame (hoare_free l v) (heapLocal_free l)\n        (preserves_of_storeStable (storeStable_free l) _))\n      (star_emp_left _))",
     solNote:"Six lines of proof, eleven names, no tactic block and no <code>Exec</code>. If you wrote it with <code>refine hoare_seq (Q := …) ?_ ?_</code> and two bullets, that is the same proof; the term form is what it collapses to once both halves are known.",
     expl:"Two applications of <code>hoare_consequence</code>, one on each side of a <code>hoare_seq</code>. The first reshapes the load&rsquo;s postcondition into the middle assertion by commuting a star; the second frames the free rule and then discards the <code>emp</code> the freed cell left behind.",
     walk: [
       {tac:'hoare_seq', h:"Splits the program at its one <code>;;</code>, leaving two triples to supply. The assertion between them is implicit and is read off the first argument&rsquo;s type — no <code>(Q := …)</code> is needed here, because that argument is fully applied."},
       {tac:'hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _)', h:"<code>hoare_load x l v</code> is <code>Hoare (l ↦ v) (.load x l) (pure (fun σ => σ x = v) ∗ (l ↦ v))</code>. The precondition is already what is wanted, hence <code>entails_refl _</code>; the postcondition is right up to the order of the two conjuncts, and <code>star_comm</code> is the whole repair. The middle assertion is thereby fixed as <code>(l ↦ v) ∗ pure (fun σ => σ x = v)</code>."},
       {tac:'hoare_frame (hoare_free l v) (heapLocal_free l) (preserves_of_storeStable (storeStable_free l) _)', h:"Lifts <code>Hoare (l ↦ v) (.free l) emp</code> to <code>Hoare ((l ↦ v) ∗ R) (.free l) (emp ∗ R)</code>. The three arguments are the three hypotheses in order: the small rule, locality, preservation. The frame <code>R</code> is not written anywhere — it is determined by the goal, which is why the last argument ends in an underscore."},
       {tac:'preserves_of_storeStable (storeStable_free l) _', h:"The only place in this proof where a choice could have gone wrong. The frame is <code>pure (fun σ => σ x = v)</code>; <code>preserves_of_heapOnly</code> would need <code>HeapOnly (pure …)</code>, which Unit 24 refuted. Store-stability of <code>free</code> discharges it without looking at the frame at all, which is why the second argument is an underscore."},
       {tac:'star_emp_left _', h:"The framed free ends at <code>emp ∗ pure (fun σ => σ x = v)</code>. The postcondition wanted is the right-hand conjunct on its own, and <code>emp ∗ P ⊢ P</code> is the unit law. This is where the deallocation is recorded: the cell did not vanish from the assertion, it became <code>emp</code>, and <code>emp</code> was then absorbed."}
     ],
     deep: [
       {t:'trace', title:'The same proof staged with refine, so the two obligations are visible',
        start:"x : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (readAndFree x l) (_root_.pure fun σ => σ x = v)",
        steps:[
          {tac:'refine hoare_seq (Q := (l ↦ v) ∗ pure (fun σ => σ x = v)) ?_ ?_',
           state:"case refine_1\nx : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.load x l) (l ↦ v ∗ _root_.pure fun σ => σ x = v)\n\ncase refine_2\nx : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v ∗ _root_.pure fun σ => σ x = v) (Cmd.free l) (_root_.pure fun σ => σ x = v)",
           h:"The choice made explicit. Written this way the program has already disappeared: <code>readAndFree</code> unfolded into its two commands and each goal mentions exactly one of them."},
          {tac:'have step : … := hoare_frame (hoare_free l v) (heapLocal_free l) (preserves_of_storeStable (storeStable_free l) _)',
           state:"case refine_2\nx : Var\nl : Loc\nv : Val\nstep : Hoare (l ↦ v ∗ _root_.pure fun σ => σ x = v) (Cmd.free l) (emp ∗ _root_.pure fun σ => σ x = v)\n⊢ Hoare (l ↦ v ∗ _root_.pure fun σ => σ x = v) (Cmd.free l) (_root_.pure fun σ => σ x = v)",
           h:"Naming the framed triple before consuming it is the habit worth acquiring: the hypothesis and the goal now differ in one place, the postcondition, and the difference names the law that closes the gap. <code>exact hoare_consequence (entails_refl _) step (star_emp_left _)</code> finishes."}
        ]},
       {t:'cmp',
        left:{t:'Unit 23 · from the semantics', kind:'bad', tag:'verified',
          h:"Names a store, two heaps and a run. Builds the <code>Exec.seq</code> derivation by hand out of two <code>singleton_same</code> lookups, and finishes with a store computation and a heap equation.",
          src:"theorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩\n  · exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))\n  · show Store.set σ x v x = v\n    simp [Store.set]\n  · exact erase_singleton l v"},
        right:{t:'Unit 29 · from the rules', kind:'good', tag:'verified',
          h:"Names no store, no heap and no run. Eleven identifiers, of which two are small rules and two are <code>∗</code> laws. Replace <code>free</code> by any other store-stable command with a small rule and the shape is unchanged.",
          src:"theorem readAndFree_framed (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=\n  hoare_seq\n    (hoare_consequence (entails_refl _) (hoare_load x l v) (star_comm _ _))\n    (hoare_consequence (entails_refl _)\n      (hoare_frame (hoare_free l v) (heapLocal_free l)\n        (preserves_of_storeStable (storeStable_free l) _))\n      (star_emp_left _))"}}
     ],
     pitfall:"Choosing the middle assertion as <code>pure (fun σ => σ x = v) ∗ (l ↦ v)</code> — the load rule&rsquo;s postcondition, unchanged. It is the natural first guess and it makes the second half unprovable, because <code>hoare_frame</code>&rsquo;s conclusion is <code>Hoare (P ∗ R) c (Q ∗ R)</code> with the frame on the right. Where the complaint lands is worth knowing in advance: not at <code>hoare_seq</code>, where the choice was made, but inside the frame, as a demand that you prove a triple about the pure fact — the message is quoted in full in <code>variants</code> below. There is no version of the rule with the frame on the left, and Unit 27 priced the one you would have to prove instead: <code>Hoare (R ∗ P) c (R ∗ Q)</code> is equally true, and takes ten lines and four appeals to lemmas about heaps where the shipped proof needs none — after which every application inherits the swapped order. Put the commutation in your own proof instead, where it is one name.",
     variants:"Replace <code>preserves_of_storeStable (storeStable_free l) _</code> by <code>preserves_of_heapOnly _ (heapOnly_emp)</code> and it fails, because the frame is not <code>emp</code>; by anything built from <code>heapOnly_pointsTo</code> and it fails, because the frame is not a <code>↦</code>. There is no heap-only proof of this frame at all — that is <code>not_heapOnly_pure</code>. Drop the <code>hoare_consequence</code> around the first half and the middle assertion becomes the load rule&rsquo;s own postcondition, <code>pure φ ∗ (l ↦ v)</code> — and then the failure is reported not at <code>hoare_seq</code> but inside the frame: <code>hoare_free l v</code> <i>has type Hoare (l ↦ v) (Cmd.free l) emp but is expected to have type Hoare (_root_.pure fun σ =&gt; σ x = v) (Cmd.free l) ?m.15</i>. <code>hoare_frame</code> cut the star at its top level and took the <i>left</i> conjunct as the footprint, so it is asking you to prove a triple about the pure fact."},

    /* ================================================= the shape of a rule ==== */

    {t:'sec', s:'A rule&rsquo;s shape is a design decision'},

    {t:'p', h:"The next program copies a cell into another cell: read <code>src</code> into a temporary, then write the temporary into <code>dst</code>. Two commands again, and this time both of them touch memory, so both need framing."},

    {t:'code', cap:'Two commands and one temporary variable.',
     src:"def copyCell (tmp : Var) (src dst : Loc) : Cmd :=\n  .load tmp src ;; .write dst (.var tmp)"},

    {t:'p', h:"Before any Lean, decide what goes between the two commands. Work backwards from the write, because the write is what constrains it."},

    {t:'ol', items:[
      "The specification is <code>Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a))</code>: two cells owned, and afterwards the second one holds what the first one holds.",
      "The write&rsquo;s rule owns <code>dst</code> and nothing else. It also needs to know something the heap cannot tell it — that the atom <code>.var tmp</code> evaluates to <code>a</code>.",
      "It must not lose <code>src</code>, and it does not touch it, so <code>src ↦ a</code> is the write&rsquo;s frame and sits on the right of the <code>∗</code>.",
      "So the assertion between the two commands is <code>(the fact that tmp holds a, together with dst ↦ b) ∗ (src ↦ a)</code>, and everything before that point exists to produce it.",
      "The load&rsquo;s rule owns <code>src</code> and nothing else, so <code>dst ↦ b</code> is the load&rsquo;s frame — a different frame, on a different side of the program, and heap-only where the write&rsquo;s was not.",
      "What the load rule hands back is not in the shape step 4 asks for. The distance between them is the first half of the proof."
    ]},

    {t:'p', h:"Step 2 is the obstacle. <code>hoare_write l e old</code> has postcondition <code>fun σ h => (l ↦ (e.eval σ)) σ h</code> — the cell now holds whatever the atom evaluated to <i>in the store the write happened in</i>. For <code>.const 0</code> that reduces and Unit 23&rsquo;s <code>clearCell_spec</code> is one term. For <code>.var tmp</code> it reduces no further than a lookup in whichever store the write happened in, and that is not the postcondition you want:"},

    {t:'code', tag:'sketch', cap:'The obvious application of the rule you have.',
     src:"example (tmp : Var) (dst : Loc) (b a : Val) :\n    Hoare (dst ↦ b) (.write dst (.var tmp)) (dst ↦ a) :=\n  hoare_write dst (.var tmp) b"},

    {t:'state', cap:'The postcondition mentions the store, and the goal does not.',
     src:"error: Type mismatch\n  hoare_write dst (Atom.var tmp) b\nhas type\n  Hoare (dst ↦ b) (Cmd.write dst (Atom.var tmp)) fun σ h => (dst ↦ Atom.eval σ (Atom.var tmp)) σ h\nbut is expected to have type\n  Hoare (dst ↦ b) (Cmd.write dst (Atom.var tmp)) (dst ↦ a)"},

    {t:'p', h:"The gap is exactly the fact <code>σ tmp = a</code>, and there is nowhere in that triple to supply it. A postcondition is what you are given, not what you may assume; to consume a fact you need it in a <i>pre</i>condition. So the rule is restated with the fact moved to the front, and the value of the write named as a parameter rather than computed."},

    {t:'anat', src:"theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v)",
     parts:[
       {m:'(old v : Val)', h:"Two values now. <code>old</code> is what the cell held and is forgotten; <code>v</code> is what the atom is worth and is what the cell will hold. In <code>hoare_write</code> there was no <code>v</code>, because the postcondition computed it."},
       {m:'aAnd (fact (fun σ => e.eval σ = v))', h:"The obligation, as a precondition: whatever store you run this in, <code>e</code> is worth <code>v</code> there. <code>fact</code> is Unit 12&rsquo;s trivial embedding — a proposition about the store, imposing nothing on the heap — and it is joined by <code>aAnd</code>, which hands the <i>same</i> heap to both sides."},
       {m:'(l ↦ old)', h:"The cell, exactly owned. Because <code>aAnd</code> shares the heap and <code>fact</code> constrains none of it, the conjunction as a whole owns exactly what <code>l ↦ old</code> owns, so this precondition is still a small footprint and the frame rule still applies to it."},
       {m:'(l ↦ v)', h:"No store anywhere. That is the point: this postcondition can be the precondition of something else."}
     ]},

    {t:'p', h:"Its proof is Unit 23&rsquo;s proof of <code>hoare_write</code> with both ends changed. The precondition is a pair now, so an <code>obtain</code> takes it apart before anything else; and the fact that yields, <code>e.eval σ = v</code>, is spent by a <code>rw</code> at the finish, which is what turns the heap the write actually built into <code>Heap.singleton l v</code>. The run in between is the same run, built from the same lookup — which is the sense in which this is the old rule restated rather than a new one."},

    {t:'p', h:"Why <code>aAnd (fact φ) P</code> rather than <code>pure φ ∗ P</code>, which is the shape Unit 23 chose for the load rule&rsquo;s postcondition? Unit 17 proved the two equivalent, in <code>star_pure_left</code> and <code>star_pure_right</code>, so nothing about the mathematics is at stake. What is at stake is how many entailments stand between one rule&rsquo;s conclusion and the next rule&rsquo;s hypothesis. Unit 23 had a reason for its choice — under <code>∗</code>, a bare <code>fact</code> would own an arbitrary heap, and <code>pure</code> is what repairs that — and it is the standard textbook form. Here the assertion is under <code>aAnd</code>, where nothing is being cut, so the repair is not needed and the flat form is the cheaper one."},

    {t:'p', h:"That leaves the load&rsquo;s postcondition, <code>pure (fun σ => σ tmp = a) ∗ (src ↦ a)</code>, framed by <code>dst ↦ b</code>, sitting a short chain of <code>∗</code>-rearrangements away from what the write rule wants. Every link but the last is an existing law. The last one has to be proved, and proving it is the ordinary work of moving a pure fact around."},

    /* -------------------------------------------------------------- x59 --- */

    {t:'ex',
     id:'x59',
     name:'pure_star_regroup',
     why:"This is the bookkeeping entailment of the whole module: a pure fact learned about one conjunct, needed alongside a different conjunct. It is the last link of the chain in <code>copyCell_spec</code>, and it is the one link that could not have been assembled out of Unit 15 and Unit 16 alone without knowing what <code>pure</code> is. Proving it by hand once is also the last time on this page that a fact about heaps has to be <i>proved</i> rather than handed from one tuple to another.",
     setup:"<code>pure φ</code> is <code>aAnd (fact φ) emp</code>. The six components of a <code>∗</code> are <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code>: two heaps, their disjointness, the union equation, and the two halves.",
     goal:"theorem pure_star_regroup (φ : Store → Prop) (P R : Assertion) :\n    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by",
     hints: [
       "Unfolded: given a cut of <code>h</code> into a heap where <code>pure φ</code> holds and a heap where <code>P ∗ R</code> holds, produce a cut of <code>h</code> into a heap where <code>aAnd (fact φ) P</code> holds and a heap where <code>R</code> holds. The incoming cut is nested — the right half is itself a cut — so <code>intro</code> takes a pattern inside a pattern.",
       "<code>pure φ</code> owns the empty heap. So the incoming cut is really no cut at all: the left half is empty and the right half is the whole of <code>h</code>. The cut you must produce is therefore the inner one, unchanged, and the only work is proving that the two descriptions of <code>h</code> agree — <code>h</code> as empty-union-something, and <code>h</code> as the inner cut&rsquo;s two halves.",
       "<code>intro</code> with a nested destructuring pattern, then <code>subst</code> on the equation that says the outer left half is empty, then <code>refine</code> with the outgoing six-slot tuple leaving the union equation open, then <code>rw</code> with three equations: the outer union, the empty-unit law, and the inner union.",
       "<code>intro σ h hstar</code> then <code>obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar</code> — the fifth slot is a conjunction, so it needs its own pair pattern, and the sixth is the inner star. <code>subst he</code> replaces <code>h₀</code> by <code>Heap.empty</code> everywhere. The outgoing tuple is <code>⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩</code>, and the hole is <code>⊢ h = hP.union hR</code>."
     ],
     sol:"theorem pure_star_regroup (φ : Store → Prop) (P R : Assertion) :\n    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by\n  intro σ h hstar\n  obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar\n  subst he\n  refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩\n  rw [hu, union_empty_left, huPR]",
     solNote:"Five lines, of which the last is three rewrites in a row. The same theorem also has a proof whose body is a single line and names no heap at all; it is in the depth panel, and the reason the corpus keeps this one is that it is the only place in the module where you see what the regrouping actually does to the heaps.",
     expl:"The incoming star has an empty left half, so the outgoing star reuses the inner cut verbatim: five of its six slots are hypotheses handed straight back. The sixth is an equation between two descriptions of the same heap, and closing it is a chain of three rewrites.",
     walk: [
       {tac:'intro σ h hstar', h:"An entailment is a function of three arguments, so this is the whole of unfolding the goal. Afterwards <code>hstar : (pure φ ∗ P ∗ R) σ h</code> and the goal is the target assertion at the same <code>σ</code> and <code>h</code>."},
       {tac:'obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar', h:"Takes the outer cut apart and both of its halves. The fifth slot is <code>pure φ</code>, which is a conjunction, so it needs a pair pattern of its own — <code>hφ</code> for the store fact and <code>he : emp σ h₀</code>, which is the equation <code>h₀ = Heap.empty</code>. The sixth is the inner star and yields four more heaps&rsquo; worth of data."},
       {tac:'subst he', h:"Replaces <code>h₀</code> by <code>Heap.empty</code> throughout, including inside <code>hu</code>, which becomes <code>h = Heap.empty.union hPR</code>. Without this the rewrite at the end has nothing to match: <code>union_empty_left</code> is stated about <code>Heap.empty</code>, not about a variable that happens to equal it."},
       {tac:'refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩', h:"The outgoing cut is the inner one. Slots one, two, three and six are handed back untouched; slot five is the new conjunction, built from the store fact and the <code>P</code> half; slot four, the union equation, is the only thing that has to be proved, because it is the only slot that mentions the outer heap <code>h</code>."},
       {tac:'rw [hu, union_empty_left, huPR]', h:"Three rewrites, left to right on the goal <code>⊢ h = hP.union hR</code>. <code>hu</code> replaces <code>h</code> by <code>Heap.empty.union hPR</code>; <code>union_empty_left</code> collapses that to <code>hPR</code>; <code>huPR</code> replaces <code>hPR</code> by <code>hP.union hR</code>, and the trailing <code>rfl</code> that <code>rw</code> always tries closes it."}
     ],
     deep: [
       {t:'trace', title:'pure_star_regroup, and where the empty heap goes',
        start:"φ : Store → Prop\nP R : Assertion\nσ : Store\nh : Heap\nhstar : (_root_.pure φ ∗ P ∗ R) σ h\n⊢ (aAnd (fact φ) P ∗ R) σ h",
        steps:[
          {tac:'obtain ⟨h₀, hPR, hd, hu, ⟨hφ, he⟩, ⟨hP, hR, hdPR, huPR, hp, hr⟩⟩ := hstar',
           state:"σ : Store\nh h₀ hPR : Heap\nhd : h₀.disjoint hPR\nhu : h = h₀.union hPR\nhφ : fact φ σ h₀\nhe : emp σ h₀\nhP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ (aAnd (fact φ) P ∗ R) σ h",
           h:"Five heaps in scope and three equations relating them. <code>he</code> is the one that matters: <code>emp σ h₀</code> unfolds to <code>h₀ = Heap.empty</code>, so the outer cut is degenerate. The binder line for <code>φ P R</code> is omitted here and in the next two states."},
          {tac:'subst he',
           state:"σ : Store\nh hPR hP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\nhd : Heap.empty.disjoint hPR\nhu : h = Heap.empty.union hPR\nhφ : fact φ σ Heap.empty\n⊢ (aAnd (fact φ) P ∗ R) σ h",
           h:"<code>h₀</code> is gone and the three hypotheses that mentioned it have moved to the bottom of the context, rewritten. <code>hu</code> now literally says what the last rewrite needs."},
          {tac:'refine ⟨hP, hR, hdPR, ?_, ⟨hφ, hp⟩, hr⟩',
           state:"σ : Store\nh hPR hP hR : Heap\nhdPR : hP.disjoint hR\nhuPR : hPR = hP.union hR\nhp : P σ hP\nhr : R σ hR\nhd : Heap.empty.disjoint hPR\nhu : h = Heap.empty.union hPR\nhφ : fact φ σ Heap.empty\n⊢ h = hP.union hR",
           h:"Everything assertional has been discharged by handing back what came in. What is left is an equation between heaps, and the two sides are the outer and inner descriptions of the same memory."}
        ],
        done:"rw [hu, union_empty_left, huPR]"},
       {t:'code', tag:'illustration', cap:'The same theorem with no heap in it, as a chain of three names.',
        src:"theorem pure_star_regroup_derived (φ : Store → Prop) (P R : Assertion) :\n    pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R :=\n  entails_trans (star_assoc_right _ _ _) (star_mono_left R (star_pure_left φ P))"},
       {t:'p', h:"Read it in the order it runs. <code>star_assoc_right</code> rebrackets <code>pure φ ∗ (P ∗ R)</code> as <code>(pure φ ∗ P) ∗ R</code>. <code>star_mono_left</code> licenses rewriting inside the left half of a star, and what it rewrites with is <code>star_pure_left</code>, which turns <code>pure φ ∗ P</code> into <code>aAnd (fact φ) P</code>. Three theorems from Units 15 to 17 and no new content — which is the honest description of what the exercise proves."}
     ],
     pitfall:"Skipping <code>subst he</code>. The proof still gets as far as the last line and then <code>rw [hu, …]</code> reports <code>Did not find an occurrence of the pattern Heap.empty.union ?h in the target expression h₀.union hPR = hP.union hR</code> — <code>hu</code> fired, and then <code>union_empty_left</code> did not, because the heap is called <code>h₀</code> and is only <i>equal</i> to <code>Heap.empty</code>. The error names the second rewrite and the cause is the missing first tactic, which is the usual distance between the two in a <code>rw</code> chain.",
     variants:"Reverse the entailment and it is still true — <code>and_fact_star_intro</code> below is half of the return journey — but the proof is different, because the empty heap now has to be produced rather than consumed, and that is <code>disjoint_empty_left</code> plus <code>(union_empty_left _).symm</code>. Replace <code>pure φ</code> by <code>fact φ</code> and the theorem becomes false, with <code>P</code> and <code>R</code> both <code>emp</code> and the heap a single cell: <code>fact φ</code> under a <code>∗</code> owns an arbitrary heap, so the incoming cut can put the whole cell on the left, while the outgoing one has to put it in <code>P</code> or in <code>R</code>, and both of those are empty. That is the loss Unit 23 was avoiding when it put <code>pure</code> rather than <code>fact</code> in the load rule."},

    {t:'p', h:"Now the same question about the load rule that was asked about the write rule. <code>hoare_load</code> ends in <code>pure φ ∗ (l ↦ v)</code>. <code>hoare_write_val</code> begins in <code>aAnd (fact φ) (l ↦ old)</code>. Those are equivalent assertions in different shapes, so composing the two rules costs an entailment every time — and it is the same entailment every time, which is the signal that the shape of one of the rules is wrong."},

    /* -------------------------------------------------------------- x60 --- */

    {t:'ex',
     id:'x60',
     name:'hoare_load_and / and_fact_star / and_fact_star_intro',
     why:"The load rule again, in the shape that composes, plus the two entailments that move a fact in and out of a star. Together with <code>hoare_write_val</code> they let a load and a write on the <i>same</i> cell compose with nothing at all between them, which is measured immediately below. This is the concrete form of a claim that is easy to state and hard to believe until it is counted: the shape of a rule is a design decision, and its cost is an entailment per use.",
     setup:"The proof of <code>hoare_load_and</code> is Unit 23&rsquo;s <code>hoare_load</code> with the postcondition changed; comparing the two is most of the exercise.",
     goal:"theorem hoare_load_and (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (.load x l) (aAnd (fact (fun σ => σ x = v)) (l ↦ v)) := by\n  sorry\n\ntheorem and_fact_star (φ : Store → Prop) (P R : Assertion) :\n    (aAnd (fact φ) P) ∗ R ⊢ aAnd (fact φ) (P ∗ R) := by\n  sorry\n\ntheorem and_fact_star_intro (φ : Store → Prop) (P R : Assertion) :\n    aAnd (fact φ) (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by",
     hints: [
       "<code>Hoare P c Q</code> unfolds to <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>, so proving a small rule means producing the final state, the run that reaches it, and the postcondition there. For the two entailments: <code>aAnd</code> is a pair and <code>∗</code> is a six-slot tuple, and each theorem is the same data with the brackets moved.",
       "The load leaves the heap alone and sets <code>x</code> to what it read, so the final state is <code>⟨Store.set σ x v, Heap.singleton l v⟩</code> and the run is <code>Exec.load</code> applied to the lookup that says <code>l</code> holds <code>v</code>. The postcondition is now a pair rather than a cut, so its second component is the heap equation, which is true by reflexivity; only the store fact needs an argument. For the two entailments: in <code>(aAnd (fact φ) P) ∗ R</code> the fact is asserted at the left half of the cut, and in <code>aAnd (fact φ) (P ∗ R)</code> at the whole heap — but <code>fact</code> ignores the heap, so those are the same claim, and every other component passes straight through.",
       "<code>intro</code>, <code>subst</code> on the precondition, then one <code>refine</code> supplying the state, the run and the two components of the pair; <code>show</code> to put the store fact in readable form and <code>simp [Store.set]</code> to close it. Both entailments are a single <code>intro</code> with the six-name star pattern nested against a pair pattern, and then one <code>exact</code>.",
       "<code>refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩</code> — four slots, the last two being the two conjuncts of <code>aAnd</code>, and the heap one is <code>rfl</code>. The hole left is the store fact, displayed with unreduced projections; <code>show Store.set σ x v x = v</code> puts it in the form <code>simp [Store.set]</code> wants. For <code>and_fact_star</code>: <code>intro σ h ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩</code> and then <code>exact ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩</code> — the same seven things, regrouped."
     ],
     sol:"theorem hoare_load_and (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (.load x l) (aAnd (fact (fun σ => σ x = v)) (l ↦ v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩\n  show Store.set σ x v x = v\n  simp [Store.set]\n\ntheorem and_fact_star (φ : Store → Prop) (P R : Assertion) :\n    (aAnd (fact φ) P) ∗ R ⊢ aAnd (fact φ) (P ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩\n  exact ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩\n\ntheorem and_fact_star_intro (φ : Store → Prop) (P R : Assertion) :\n    aAnd (fact φ) (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R := by\n  intro σ h ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩\n  exact ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩",
     solNote:"The two entailments are each two lines and each line is a list of the same seven names in a different arrangement. That is what it looks like when an equivalence is true for no reason beyond the shape of the definitions.",
     expl:"<code>hoare_load_and</code> differs from <code>hoare_load</code> in one place: because the postcondition is a pair rather than a cut, there is no heap to split, so the four-slot tuple has an <code>rfl</code> where Unit 23&rsquo;s six-slot one had a cut into <code>Heap.empty</code> and the cell. The two entailments carry the fact across the star in both directions, and neither touches the heap.",
     walk: [
       {tac:'intro σ h hp', h:"Unfolds the triple. <code>hp : (l ↦ v) σ h</code> is the equation <code>h = Heap.singleton l v</code>."},
       {tac:'subst hp', h:"Replaces <code>h</code> by <code>Heap.singleton l v</code> in the goal, so the existential is now about a run starting in a known heap. Nothing about the load is decided yet."},
       {tac:'refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩', h:"Four slots, because <code>⟨…⟩</code> flattens: the final state, the run, and then the two components of the <code>aAnd</code>. The state is the store updated at <code>x</code> and the heap untouched. <code>Exec.load</code>&rsquo;s premise is that the address holds the value, which is <code>singleton_same</code>. The last slot, the heap half of the conjunction, is <code>rfl</code> — the heap is literally the singleton."},
       {tac:'show Store.set σ x v x = v', h:"The remaining hole displays as <code>fact (fun σ => σ x = v)</code> applied to two projections out of a structure literal. <code>show</code> replaces the display by the reduced form without changing the proposition, and it is the reduced form that <code>simp</code>&rsquo;s lemma will match."},
       {tac:'simp [Store.set]', h:"Unfolds the update and settles the <code>if x = x</code>."},
       {tac:'intro σ h ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩  (and_fact_star)', h:"The incoming assertion is a star whose left half is a pair, so the pattern nests: six names for the cut, and the fifth of them opened again into the store fact and the <code>P</code> half."},
       {tac:'exact ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩', h:"The outgoing assertion is a pair whose right half is a star, so the fact comes out to the front and the other six follow in order. <code>hφ : fact φ σ h₁</code> is accepted where <code>fact φ σ h</code> is wanted because <code>fact</code> discards its heap argument — that single fact is why both directions are one line."},
       {tac:'intro σ h ⟨hφ, h₁, h₂, hd, hu, hp, hr⟩  (and_fact_star_intro)', h:"The same seven names, taken apart in the other bracketing."},
       {tac:'exact ⟨h₁, h₂, hd, hu, ⟨hφ, hp⟩, hr⟩', h:"And put back in the first. Nothing is proved here that was not already true by unfolding; the value of the two theorems is that a chain of entailments can now cite them by name."}
     ],
     deep: [
       {t:'trace', title:'hoare_load_and — the same proof as hoare_load with one slot fewer',
        start:"x : Var\nl : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.load x l) { store := σ, heap := h } s' ∧ aAnd (fact fun σ => σ x = v) (l ↦ v) s'.store s'.heap",
        steps:[
          {tac:'subst hp',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.load x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      aAnd (fact fun σ => σ x = v) (l ↦ v) s'.store s'.heap",
           h:"<code>h</code> is gone. Everything that follows is about a run out of a heap with exactly one cell in it."},
          {tac:'refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_, rfl⟩',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store\n    { store := σ.set x v, heap := Heap.singleton l v }.heap",
           h:"One hole left, and it is the store fact with the projections unreduced. Unit 23&rsquo;s <code>hoare_load</code> had a second <code>refine</code> here, splitting the heap into <code>Heap.empty</code> and the cell for the <code>∗</code>; the <code>aAnd</code> form has no cut, so that whole line disappears and <code>rfl</code> takes its place inside the first tuple."},
          {tac:'show Store.set σ x v x = v',
           state:"x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ σ.set x v x = v",
           h:"Same proposition, readable form. The display now shows the dot notation for <code>Store.set</code>, which is what <code>simp [Store.set]</code> will unfold."}
        ],
        done:"simp [Store.set]"},
       {t:'code', tag:'illustration', cap:'The measurement: a load and a write on the same cell, twice.',
        src:"def copyBack (x : Var) (l : Loc) : Cmd := .load x l ;; .write l (.var x)\n\ntheorem copyBack_by_shape (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (copyBack x l) (l ↦ v) :=\n  hoare_seq (hoare_load_and x l v) (hoare_write_val l (.var x) v v)\n\ntheorem copyBack_by_pure (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (copyBack x l) (l ↦ v) :=\n  hoare_seq\n    (hoare_consequence (entails_refl _) (hoare_load x l v) (star_pure_left _ _))\n    (hoare_write_val l (.var x) v v)"},
       {t:'p', h:"Two names against four, and the difference is one <code>hoare_consequence</code> whose only job is to convert between two spellings of one assertion. Note also what did <i>not</i> need saying in either: that <code>(Atom.var x).eval σ</code> is <code>σ x</code>. Those are the same term after one reduction step, so <code>hoare_write_val</code>&rsquo;s precondition and <code>hoare_load_and</code>&rsquo;s postcondition match without any coaxing, even though Lean prints one of them as <code>Atom.eval σ (Atom.var x)</code>."},
       {t:'p', h:"The honest limit of the saving: it is one entailment per <i>join</i>, and only when the fact and the cell the next command needs are already attached to each other. In <code>copyCell</code> below they are not — the fact is about <code>src</code> and the next command owns <code>dst</code> — so the two cells have to change places, and that reshaping costs the same whichever load rule you started from. Choosing the better rule removes the conversion, not the commutation."}
     ],
     pitfall:"Carrying <code>hoare_load</code>&rsquo;s tail across unchanged. Unit 23&rsquo;s cut ended <code>…, ⟨?_, rfl⟩, rfl⟩</code> — the store fact, the empty-heap half, and the cell — so the fingers type <code>…, ?_, rfl, rfl⟩</code> here. The postcondition is an <code>aAnd</code> now, not a <code>∗</code>: there is no cut, only two components are wanted, and the third is pushed into the <code>Eq</code> that the second one already filled. Lean reports <i>Insufficient number of fields for <code>⟨...⟩</code> constructor: Constructor <code>Eq.refl</code> does not have explicit fields, but 2 were provided</i> — a complaint naming a constructor you never wrote, and the only error you get, so nothing points at the slot that is really wrong. Count the slots off the postcondition, not off the previous proof.",
     variants:"Drop <code>fact</code> and use the raw proposition and neither entailment typechecks: <code>φ σ</code> is a <code>Prop</code>, not an <code>Assertion</code>, and <code>aAnd</code> wants two of the latter. Replace <code>fact φ</code> by <code>pure φ</code> in <code>and_fact_star</code> and it becomes false, at <code>P := emp</code>, <code>R := 0 ↦ 0</code> and the one-cell heap: on the left <code>pure φ</code> only has to hold at the empty half of the cut, on the right it has to hold at the whole heap, and it asserts that its heap is empty. That is the asymmetry <code>pure_star_regroup</code> spends the empty heap on. Weaken <code>hoare_load_and</code>&rsquo;s postcondition to <code>l ↦ v</code> alone and it is still true and useless — the fact the load established is the only reason to have run one."},

    /* ===================================================== copyCell ==== */

    {t:'sec', s:'The first compositional verification'},

    {t:'p', h:"Every name the six-step plan needed now exists, so the proof is that plan written in Lean, with one <code>have step</code> per command naming the framed triple before it is consumed. Naming it is worth the line: the frame rule&rsquo;s conclusion is bulky, and a hypothesis whose type is written out is a hypothesis you can compare with the goal by eye."},

    {t:'p', h:"The two <code>hoare_frame</code> applications in it discharge their third hypothesis differently, and the difference is the two columns of the table above. The load is framed by <code>dst ↦ b</code>: a <code>↦</code>, so heap-only, and store-stability is not available anyway because a load writes the store. The write is framed by <code>src ↦ a</code>: also a <code>↦</code>, so <i>either</i> route works, and the proof takes store-stability because it is one name and does not have to inspect the frame."},

    /* ------------------------------------------------------------- m9-1 --- */

    {t:'ex',
     id:'m9-1',
     name:'copyCell_spec',
     hard: true,
     why:"Two commands, two frames, two small rules and a renormalisation chain: the first verification with all four moves in play at once, and at no point does the proof mention a heap, a union, a disjointness or a run. It is also the first one long enough that the four moves are visible as a pattern rather than as a one-off. Whether a longer program is more of the same or something else is the question the next unit is built to answer, on a program twice this size.",
     setup:"<code>copyCell tmp src dst</code> is <code>.load tmp src ;; .write dst (.var tmp)</code>, and the middle assertion is the one worked out in the numbered plan above. The six names the two framings take as arguments are all in scope: <code>hoare_load</code>, <code>heapLocal_load</code>, <code>preserves_of_heapOnly</code> and <code>heapOnly_pointsTo</code> from Units 23 and 24, and <code>heapLocal_write</code> from Unit 25 beside this page&rsquo;s <code>hoare_write_val</code>, <code>storeStable_write</code> and <code>pure_star_regroup</code>. Everything else the proof uses is a structural rule or a <code>∗</code> law you already have.",
     goal:"theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a)) := by",
     hints: [
       "<code>copyCell tmp src dst</code> is <code>.load tmp src ;; .write dst (.var tmp)</code>. Unfolded, the goal says: from any state whose heap is exactly two cells — <code>src</code> holding <code>a</code>, <code>dst</code> holding <code>b</code> — the two commands run to some final state, and there the heap is again exactly two cells, with <code>src</code> still holding <code>a</code> and <code>dst</code> now holding <code>a</code> as well. Read the two ends against each other: nothing is allocated, nothing is released, one value changed, and the value it changed to was already in the other cell.",
       "Two commands means one assertion between them, and every other choice follows from it. Work backwards from the write, because the write is what constrains it. Its rule owns <code>dst</code> and nothing else, and it needs one thing no heap can tell it: what the atom is worth in the store it runs in. It must not lose <code>src</code>, and it does not touch <code>src</code>, so that cell is the write&rsquo;s frame and sits on the right of the star. The load&rsquo;s rule owns <code>src</code> and nothing else, so the other cell is the load&rsquo;s frame — a different frame on the other side of the program. That is the numbered plan above, and turning its fourth line into an assertion is the exercise; everything after it is forced.",
       "Each half is the same three moves: the small rule, <code>hoare_frame</code> around it, <code>hoare_consequence</code> around that. The load&rsquo;s frame is a points-to, so its <code>Preserves</code> obligation goes through <code>preserves_of_heapOnly</code> and <code>heapOnly_pointsTo</code>; the write&rsquo;s goes through <code>preserves_of_storeStable</code> and this unit&rsquo;s <code>storeStable_write</code>. The locality arguments are <code>heapLocal_load</code> and <code>heapLocal_write</code>, and the small rules are <code>hoare_load</code> and <code>hoare_write_val</code> — not <code>hoare_write</code>. What is left after the first <code>hoare_consequence</code> is a single entailment with no command in it, and the names that close it, in the order they run, are <code>star_assoc_left</code>, <code>star_mono_right</code> with <code>star_comm</code> inside it, and <code>pure_star_regroup</code>, joined by <code>entails_trans</code>. The second half needs one <code>star_comm</code> and no chain.",
       "<code>refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_</code> is the first line and fixes everything else. In the first bullet, <code>have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src) ((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) := hoare_frame …</code>, then <code>refine hoare_consequence (entails_refl _) step ?_</code> leaves exactly one entailment, and the three links close it in the order given by hint 3."
     ],
     sol:"theorem copyCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a)) := by\n  refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_\n  · -- the load, framed by `dst ↦ b`, then renormalised\n    have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src)\n        ((pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)) :=\n      hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src)\n        (preserves_of_heapOnly _ (heapOnly_pointsTo dst b))\n    refine hoare_consequence (entails_refl _) step ?_\n    refine entails_trans (star_assoc_left _ _ _) ?_\n    refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_\n    exact pure_star_regroup _ _ _\n  · -- the write, with the value known from the pure fact, framed by `src ↦ a`\n    have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a))\n        (.write dst (.var tmp)) ((dst ↦ a) ∗ (src ↦ a)) :=\n      hoare_frame (hoare_write_val dst (.var tmp) b a) (heapLocal_write dst (.var tmp))\n        (preserves_of_storeStable (storeStable_write dst (.var tmp)) _)\n    exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))",
     solNote:"Sixteen lines, of which one is a decision and fifteen are consequences of it. If you climbed all four hints and are still assembling this, open it and read the two bullets against the six-step plan; that is what the exercise is for.",
     expl:"One <code>hoare_seq</code> with an explicit middle assertion, then the same three moves twice. Each half frames its small rule, wraps the result in a consequence whose precondition side is reflexivity, and closes the remaining entailment out of the <code>∗</code>-algebra. The two halves differ in which <code>Preserves</code> discharger they use and in how far the star has to be reshaped.",
     walk: [
       {tac:'refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_', h:"Splits the program and fixes the assertion between the two commands. Lean cannot infer this argument, and the reason is not a limitation: two different intermediate assertions give two different proofs of the same theorem, so there is nothing to infer from. Everything below is determined by this line."},
       {tac:'have step : Hoare ((src ↦ a) ∗ (dst ↦ b)) (.load tmp src) ((pure … ∗ (src ↦ a)) ∗ (dst ↦ b)) := hoare_frame …', h:"The framed load, named. Writing the type out is what makes the next line readable: the goal and <code>step</code> now agree on the precondition and the command and disagree only on the postcondition."},
       {tac:'hoare_frame (hoare_load tmp src a) (heapLocal_load tmp src) (preserves_of_heapOnly _ (heapOnly_pointsTo dst b))', h:"Three arguments, three hypotheses. The frame here is <code>dst ↦ b</code> — a points-to, hence heap-only, hence the left column of the table. Store-stability is not an option: a load is the archetype of a command that changes the store."},
       {tac:'refine hoare_consequence (entails_refl _) step ?_', h:"Consumes <code>step</code> and leaves one goal, an entailment: <code>((pure φ) ∗ (src ↦ a)) ∗ (dst ↦ b) ⊢ aAnd (fact φ) (dst ↦ b) ∗ (src ↦ a)</code>. No command appears in it. From here to the end of the bullet is pure assertion algebra."},
       {tac:'refine entails_trans (star_assoc_left _ _ _) ?_', h:"Rebrackets the left-hand side from <code>(pure φ ∗ (src ↦ a)) ∗ (dst ↦ b)</code> to <code>pure φ ∗ ((src ↦ a) ∗ (dst ↦ b))</code>, which puts the two cells next to each other so that the next step can swap them."},
       {tac:'refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_', h:"Swaps the two cells inside the right half. <code>star_mono_right</code> is what licenses rewriting under a star: it turns an entailment between the right halves into an entailment between the wholes. This is the step that puts <code>dst</code> where the write rule needs it."},
       {tac:'exact pure_star_regroup _ _ _', h:"The last link. The fact is currently attached to nothing in particular and needs to be attached to <code>dst ↦ b</code>; that is exactly the exercise proved in the previous section, with <code>P</code> instantiated to <code>dst ↦ b</code> and <code>R</code> to <code>src ↦ a</code>."},
       {tac:'have step : Hoare ((aAnd (fact (fun σ => (Atom.var tmp).eval σ = a)) (dst ↦ b)) ∗ (src ↦ a)) … := hoare_frame …', h:"The framed write. The type is written with <code>(Atom.var tmp).eval σ</code> where the goal has <code>σ tmp</code>; those are the same term after one reduction, and Lean accepts the mismatch without a word. The frame is <code>src ↦ a</code>, which the write must not disturb."},
       {tac:'preserves_of_storeStable (storeStable_write dst (.var tmp)) _', h:"The other column. The frame happens to be heap-only here too, so <code>preserves_of_heapOnly _ (heapOnly_pointsTo src a)</code> also compiles; store-stability is preferred because it is one name that works for any frame, and because it is the route that will still be there when the frame stops being a points-to."},
       {tac:'exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))', h:"The framed write ends at <code>(dst ↦ a) ∗ (src ↦ a)</code> and the specification asks for <code>(src ↦ a) ∗ (dst ↦ a)</code>. One commutation, and the second half has no chain at all — because its frame was already in the right place, which is what the middle assertion was chosen to arrange."}
     ],
     deep: [
       {t:'trace', title:'The two obligations, and the chain that closes the first',
        start:"tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (src ↦ a ∗ dst ↦ a)",
        steps:[
          {tac:'refine hoare_seq (Q := (aAnd (fact (fun σ => σ tmp = a)) (dst ↦ b)) ∗ (src ↦ a)) ?_ ?_',
           state:"case refine_1\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a)\n\ncase refine_2\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
           h:"The four binder lines are omitted from each goal here and below. <code>copyCell</code> has unfolded and every remaining goal is about one command."},
          {tac:'refine hoare_consequence (entails_refl _) step ?_',
           state:"case refine_1\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ ((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
           h:"The goal is an entailment and the two <code>⊢</code> on that line are different symbols: the outer one is Lean&rsquo;s turnstile, the inner one is Unit 12&rsquo;s notation for <code>Entails</code>. Left of it: what the framed load produced. Right of it: what the write step needs."},
          {tac:'refine entails_trans (star_assoc_left _ _ _) ?_',
           state:"case refine_1\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ (_root_.pure fun σ => σ tmp = a) ∗ src ↦ a ∗ dst ↦ b ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
           h:"One pair of brackets has moved. <code>∗</code> is right-associative, so the printed form with no brackets at all is the right-nested one."},
          {tac:'refine entails_trans (star_mono_right _ (star_comm (src ↦ a) (dst ↦ b))) ?_',
           state:"case refine_1\nstep : Hoare (src ↦ a ∗ dst ↦ b) (Cmd.load tmp src) (((_root_.pure fun σ => σ tmp = a) ∗ src ↦ a) ∗ dst ↦ b)\n⊢ (_root_.pure fun σ => σ tmp = a) ∗ dst ↦ b ∗ src ↦ a ⊢ aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a",
           h:"<code>src</code> and <code>dst</code> have changed places. The remaining difference between the two sides is <code>pure φ ∗ (P ∗ R)</code> against <code>aAnd (fact φ) P ∗ R</code>, which is <code>pure_star_regroup</code> exactly."}
        ],
        done:"exact pure_star_regroup _ _ _"},
       {t:'trace', title:'The second half, where the reduction is invisible',
        start:"case refine_2\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
        steps:[
          {tac:'have step : … := hoare_frame (hoare_write_val dst (.var tmp) b a) …',
           state:"step :\n  Hoare (aAnd (fact fun σ => Atom.eval σ (Atom.var tmp) = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp))\n    (dst ↦ a ∗ src ↦ a)\n⊢ Hoare (aAnd (fact fun σ => σ tmp = a) (dst ↦ b) ∗ src ↦ a) (Cmd.write dst (Atom.var tmp)) (src ↦ a ∗ dst ↦ a)",
           h:"Read the two preconditions: <code>Atom.eval σ (Atom.var tmp)</code> against <code>σ tmp</code>. They look different and they are the same term, because <code>Atom.eval</code> on the <code>var</code> constructor reduces to a store lookup in one step. No tactic is needed and none is written; <code>exact</code> checks up to reduction. The only real difference left is the order of the postcondition&rsquo;s two conjuncts."}
        ],
        done:"exact hoare_consequence (entails_refl _) step (star_comm (dst ↦ a) (src ↦ a))"},
       {t:'p', h:"Three entailments in the first half and one in the second. The asymmetry is not an accident of the proof: it is where the middle assertion was placed. Choosing it in the shape the <i>write</i> wants means the write&rsquo;s side is nearly free and the load&rsquo;s side pays for the reshaping. Choosing it in the shape the load produces would move all four links to the other bullet and leave the theorem exactly as true."}
     ],
     pitfall:"Starting with <code>refine hoare_seq ?_ ?_</code> and expecting to discover the middle assertion from the goals. Lean answers <code>don&rsquo;t know how to synthesize implicit argument `Q`</code> with context <code>⊢ Assertion</code>, which Unit 22 showed you; the reason it cannot guess is that there is genuinely nothing to guess from. The second, subtler version of the same mistake is choosing the middle assertion to be the load&rsquo;s postcondition — <code>(pure φ ∗ (src ↦ a)) ∗ (dst ↦ b)</code>. That works too, and it moves every one of the four entailments into the second bullet, where they are harder to see because the write&rsquo;s own precondition is already complicated.",
     variants:"Swap the two <code>Preserves</code> dischargers and one of the two swaps compiles: <code>preserves_of_heapOnly _ (heapOnly_pointsTo src a)</code> in the write step is fine, because that frame is a points-to. The other direction has no repair — there is no store-stability theorem for a load, and there cannot be one. Drop <code>hoare_write_val</code> back to <code>hoare_write</code> and the second bullet cannot be stated: the postcondition would be <code>dst ↦ σ tmp</code>, and no consequence turns that into <code>dst ↦ a</code>, because the entailment would have to consume a fact about the store and an entailment has nowhere to put one. Choose the middle assertion the other way — <code>(pure (fun σ => σ tmp = a) ∗ (src ↦ a)) ∗ (dst ↦ b)</code>, the load rule&rsquo;s own output — and the theorem is still provable in the same number of lines, with the first bullet reduced to a bare <code>exact</code> and the three-link chain moved to the <i>precondition</i> side of the second bullet&rsquo;s consequence. Compiled, and it is the version worth writing out once to see that the chain does not go away, it moves."},

    /* ===================================================== moveCell ==== */

    {t:'sec', s:'Reuse, and where the brackets are'},

    {t:'p', h:"With <code>copyCell</code> proved, a program that copies and then releases the source is three tactics. That is what compositionality buys, and it is the first time in this course that one program&rsquo;s specification is used inside another&rsquo;s."},

    {t:'code', cap:'A program built out of a program.',
     src:"def moveCell (tmp : Var) (src dst : Loc) : Cmd :=\n  copyCell tmp src dst ;; .free src"},

    {t:'p', h:"There is a trap here and it costs an afternoon if you meet it unwarned. <code>moveCell</code> is bracketed to the left: <code>copyCell tmp src dst ;; .free src</code> unfolds to <code>(load ;; write) ;; free</code>, and that is exactly why <code>copyCell_spec</code> fits its first slot. Write the same three commands out in a single line instead and <code>;;</code>&rsquo;s right associativity brackets them the other way, and it does not fit."},

    {t:'note', kind:'info', title:'Sequencing is associative for runs, not for terms', h:"<code>hoare_seq</code> splits at the outermost <code>;;</code>. In <code>(c₁ ;; c₂) ;; c₃</code> that gives <code>c₁ ;; c₂</code> and <code>c₃</code>; in <code>c₁ ;; (c₂ ;; c₃)</code> it gives <code>c₁</code> and <code>c₂ ;; c₃</code>. Feeding <code>copyCell_spec</code> to the second of those reports <code>Application type mismatch</code>, <i>has type Hoare … (copyCell tmp src dst) …</i> against <i>expected … (Cmd.load tmp src) …</i>, and leaves a second unsolved goal about the wrong two commands. The two programs are nevertheless the same program in every sense that matters — they have the same runs — and proving that is the next exercise."},

    /* ------------------------------------------------------------- m9-2 --- */

    {t:'ex',
     id:'m9-2',
     name:'exec_seq_assoc',
     why:"The repair for the trap above, and the one place in this unit where writing about <code>Exec</code> is the right thing to do: this is a theorem about the language, not a verification of a program, and once it exists a bracketing mismatch costs one application instead of a rewritten proof. It is also the cleanest example in the course of nested inversion — two <code>cases</code>, one inside the other, on a derivation whose premise is itself a derivation.",
     setup:"<code>Exec.seq</code> takes two runs and a middle state, which it leaves implicit. <code>cases … with | seq h₁ h₂ =></code> is Unit 19&rsquo;s inversion syntax.",
     goal:"theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :\n    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s' := by",
     hints: [
       "The goal is an <code>↔</code> between two claims about runs: that <code>(c₁ ;; c₂) ;; c₃</code> takes <code>s</code> to <code>s'</code>, and that <code>c₁ ;; (c₂ ;; c₃)</code> does. The three commands and the two states are arbitrary and stay arbitrary — nothing here is about what any particular command does. Each direction hands you one derivation and asks for the other, between the same two states.",
       "A run of <code>(c₁ ;; c₂) ;; c₃</code> is: a run of <code>c₁ ;; c₂</code> from <code>s</code> to some middle state, then a run of <code>c₃</code>. Take the first of those apart again and you have three runs and two middle states. Reassemble them with the other bracketing; the same two middle states serve, in the same order.",
       "<code>constructor</code>, then in each branch <code>intro</code>, then <code>cases … with | seq h₁ h₂ =></code>, then a second <code>cases</code> on whichever of the two halves is itself a sequence, then <code>exact</code> with two nested <code>Exec.seq</code> applications. Leading-dot notation abbreviates <code>Exec.seq</code> to <code>.seq</code> in a position where the expected type is known.",
       "Forward direction: <code>cases h with | seq h₁ h₂ =></code> gives <code>h₁ : Exec (c₁ ;; c₂) s s'✝</code> and <code>h₂ : Exec c₃ s'✝ s'</code>; <code>cases h₁ with | seq ha hb =></code> splits <code>h₁</code> again; the answer is <code>.seq ha (.seq hb h₂)</code>. The backward direction is the mirror image, taking <code>h₂</code> apart instead of <code>h₁</code>."
     ],
     sol:"theorem exec_seq_assoc {c₁ c₂ c₃ : Cmd} {s s' : State} :\n    Exec ((c₁ ;; c₂) ;; c₃) s s' ↔ Exec (c₁ ;; (c₂ ;; c₃)) s s' := by\n  constructor\n  · intro h\n    cases h with | seq h₁ h₂ => cases h₁ with | seq ha hb => exact .seq ha (.seq hb h₂)\n  · intro h\n    cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb => exact .seq (.seq h₁ ha) hb",
     solNote:"Five lines and perfectly symmetric: the two branches differ in which of <code>h₁</code> and <code>h₂</code> gets taken apart, and in where the brackets go in the answer.",
     expl:"Both directions take a derivation apart into three runs and put them back together with the brackets moved. Nothing about the states changes — the two middle states of one bracketing are the two middle states of the other.",
     walk: [
       {tac:'constructor', h:"An <code>↔</code> is a pair of implications, so this leaves two goals, <code>mp</code> and <code>mpr</code>."},
       {tac:'intro h', h:"Takes the derivation. <code>h : Exec ((c₁ ;; c₂) ;; c₃) s s'</code> — a derivation is a value, and this one can be inspected."},
       {tac:'cases h with | seq h₁ h₂ =>', h:"Inversion. Only <code>Exec.seq</code> can conclude a run of a <code>;;</code>, so there is one branch. The middle state it existentially carried appears as <code>s'✝</code>, inaccessible, and the two premises are named: <code>h₁ : Exec (c₁ ;; c₂) s s'✝</code> and <code>h₂ : Exec c₃ s'✝ s'</code>."},
       {tac:'cases h₁ with | seq ha hb =>', h:"The same move one level down, because <code>h₁</code> is itself a run of a sequence. A second inaccessible middle state appears, and now there are three runs — <code>c₁</code>, then <code>c₂</code>, then <code>c₃</code> — through two intermediate states."},
       {tac:'exact .seq ha (.seq hb h₂)', h:"Reassembly. The goal is <code>Exec (c₁ ;; c₂ ;; c₃) s s'</code>, whose outermost sequence splits after <code>c₁</code>, so the outer <code>.seq</code> takes <code>ha</code> and a run of <code>c₂ ;; c₃</code>, which is the inner <code>.seq</code>. The middle states are supplied by unification; nothing had to be named."},
       {tac:'intro h ; cases h with | seq h₁ h₂ => cases h₂ with | seq ha hb =>', h:"The backward direction. Here the <i>second</i> premise is the compound one, so it is <code>h₂</code> that is taken apart."},
       {tac:'exact .seq (.seq h₁ ha) hb', h:"And the brackets close on the left instead of the right."}
     ],
     deep: [
       {t:'trace', title:'The forward direction, one inversion at a time',
        start:"case mp\nc₁ c₂ c₃ : Cmd\ns s' : State\nh : Exec ((c₁ ;; c₂) ;; c₃) s s'\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
        steps:[
          {tac:'cases h with | seq h₁ h₂ =>',
           state:"case mp.seq\nc₁ c₂ c₃ : Cmd\ns s' s'✝ : State\nh₁ : Exec (c₁ ;; c₂) s s'✝\nh₂ : Exec c₃ s'✝ s'\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
           h:"One branch, and a state the rule had bound existentially is now in the context under a daggered name. The goal is unchanged — inversion on a <code>seq</code> tells you nothing about the final state, only about how it was reached."},
          {tac:'cases h₁ with | seq ha hb =>',
           state:"case mp.seq.seq\nc₁ c₂ c₃ : Cmd\ns s' s'✝¹ : State\nh₂ : Exec c₃ s'✝¹ s'\ns'✝ : State\nha : Exec c₁ s s'✝\nhb : Exec c₂ s'✝ s'✝¹\n⊢ Exec (c₁ ;; c₂ ;; c₃) s s'",
           h:"Three runs and two daggered middle states. Reading the chain from the top: <code>s</code> to <code>s'✝</code> by <code>c₁</code>, then to <code>s'✝¹</code> by <code>c₂</code>, then to <code>s'</code> by <code>c₃</code>. The goal wants exactly that chain with the brackets moved, and the superscript on the second dagger is how Lean distinguishes two names it cannot let you type."}
        ],
        done:"exact .seq ha (.seq hb h₂)"},
       {t:'code', tag:'illustration', cap:'From runs to triples, and the payoff: the right-nested program, for free — spending <code>moveCell_spec</code>, which is the exercise directly below this one.',
        src:"theorem hoare_seq_regroup {P Q : Assertion} {c₁ c₂ c₃ : Cmd}\n    (h : Hoare P ((c₁ ;; c₂) ;; c₃) Q) : Hoare P (c₁ ;; (c₂ ;; c₃)) Q := by\n  intro σ hh hp\n  obtain ⟨s', hex, hq⟩ := h σ hh hp\n  exact ⟨s', exec_seq_assoc.mp hex, hq⟩\n\ndef moveCellRight (tmp : Var) (src dst : Loc) : Cmd :=\n  .load tmp src ;; (.write dst (.var tmp) ;; .free src)\n\ntheorem moveCellRight_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCellRight tmp src dst) (dst ↦ a) :=\n  hoare_seq_regroup (moveCell_spec tmp src dst a b)"},
       {t:'p', h:"<code>hoare_seq_regroup</code> is where <code>exec_seq_assoc</code> is spent: a triple is an existential over runs, so replacing the run by an equivalent one leaves the state and the postcondition untouched and the two triples are interchangeable. Once it exists, a specification proved for one bracketing transfers to the other by application. The specification it is applied to here, <code>moveCell_spec</code>, is the next exercise — read this block as what that theorem will be worth rather than as something you have."}
     ],
     pitfall:"Naming three things in the pattern — <code>| seq sMid h₁ h₂ =></code> — because the middle state is visibly there in the goal. It is not a constructor argument: <code>Exec.seq</code> takes two premises and Lean infers the state from them, so this reports <i>Too many variable names provided at alternative <code>seq</code>: 3 provided, but 2 expected</i>. If you want the middle state under a name you can type, <code>rename_i</code> after the <code>cases</code> is the tool.",
     variants:"Drop one of the two directions and you have a one-way lemma, which is enough for <code>hoare_seq_regroup</code> as written but not for its converse. Try to state the same theorem as an equality of commands — <code>(c₁ ;; c₂) ;; c₃ = c₁ ;; (c₂ ;; c₃)</code> — and it is false: those are two different values of the inductive type <code>Cmd</code>, distinguished by their constructors, and <code>Cmd</code> knows nothing about what running them does. Unit 18&rsquo;s <code>a ;; b ;; c = a ;; (b ;; c) := rfl</code> is not a counterexample to that and does not contradict it: the parser brackets its left-hand side to the right before the elaborator sees it, so both sides of that <code>rfl</code> are one term and no bracket ever moved. Moving one is a property of <code>Exec</code>, which is why the theorem has to be stated about runs."},

    /* ------------------------------------------------------------- m9-3 --- */

    {t:'p', h:"Which leaves the specification itself. Its postcondition is <code>dst ↦ a</code> — one cell, where the precondition had two. The assertion language is not describing memory that happens to exist; it is describing what this piece of the program owns, and after the <code>free</code> it owns less."},

    {t:'ex',
     id:'m9-3',
     name:'moveCell_spec',
     why:"Three tactics, and what they buy is a measurement: reusing <code>copyCell_spec</code> costs nothing, provided the middle assertion is chosen to be its postcondition. Get that choice wrong by one commutation and the first half stops fitting — which is the <code>pitfall</code>, and the sharpest evidence on the page that the <code>(Q := …)</code> is where a verification is decided. Watching where the released cell then goes — into <code>emp</code>, and out through <code>star_emp_left</code> — is what makes it concrete that the logic tracked the deallocation rather than forgetting about it.",
     setup:"<code>copyCell_spec</code> is available. <code>moveCell tmp src dst</code> is <code>copyCell tmp src dst ;; .free src</code>, so the outermost <code>;;</code> splits exactly there.",
     goal:"theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a) := by",
     hints: [
       "<code>moveCell tmp src dst</code> is <code>copyCell tmp src dst ;; .free src</code>. Unfolded, the goal says: from a state whose heap is exactly <code>src</code> holding <code>a</code> and <code>dst</code> holding <code>b</code>, the program runs to a final state whose heap is exactly one cell, <code>dst</code>, holding <code>a</code>. Read the two ends against each other: the precondition owns two cells and the postcondition owns one, and the value that survives is the one that started in the cell that is gone.",
       "After the copy, both cells are owned and both hold <code>a</code>. The free rule owns <code>src</code> and gives back <code>emp</code>; the other cell has to be framed past it, so it goes on the right. That fixes the middle assertion as <code>(src ↦ a) ∗ (dst ↦ a)</code>, which is exactly <code>copyCell_spec</code>&rsquo;s postcondition — no reshaping is needed on the first half at all.",
       "<code>refine hoare_seq (Q := …) (copyCell_spec tmp src dst a b) ?_</code>, then <code>have step := hoare_frame (hoare_free src a) (heapLocal_free src) (preserves_of_storeStable (storeStable_free src) _)</code>, then one <code>hoare_consequence</code> whose postcondition side is <code>star_emp_left</code>.",
       "<code>refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_</code> leaves the single goal <code>⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)</code>. The framed free proves <code>Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a))</code>, and the gap between that and the goal is one unit law."
     ],
     sol:"theorem moveCell_spec (tmp : Var) (src dst : Loc) (a b : Val) :\n    Hoare ((src ↦ a) ∗ (dst ↦ b)) (moveCell tmp src dst) (dst ↦ a) := by\n  refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_\n  have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) :=\n    hoare_frame (hoare_free src a) (heapLocal_free src)\n      (preserves_of_storeStable (storeStable_free src) _)\n  exact hoare_consequence (entails_refl _) step (star_emp_left _)",
     solNote:"Three tactics, no chain, no reshaping on the first half. That is what it looks like when the middle assertion is already the shape both neighbours want.",
     expl:"One <code>hoare_seq</code> whose first argument is the previous exercise, and whose second is the standard framed small rule with a single unit law after it.",
     walk: [
       {tac:'refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_', h:"Splits at the outer <code>;;</code> and supplies the first half immediately. The middle assertion is chosen to be <code>copyCell_spec</code>&rsquo;s postcondition unchanged, which is the reason this half needs no consequence at all — the cell to be freed is already on the left, which is where the frame rule wants the small rule&rsquo;s footprint."},
       {tac:'have step : Hoare ((src ↦ a) ∗ (dst ↦ a)) (.free src) (emp ∗ (dst ↦ a)) := hoare_frame …', h:"The framed free, named. The frame is <code>dst ↦ a</code>, which is heap-only, so either discharger works; the proof takes store-stability, matching <code>readAndFree_framed</code>."},
       {tac:'exact hoare_consequence (entails_refl _) step (star_emp_left _)', h:"The framed free ends at <code>emp ∗ (dst ↦ a)</code>. The <code>emp</code> is the freed cell: the assertion did not shrink by one conjunct, it kept the conjunct and emptied it, and <code>star_emp_left</code> is what finally discards it. That is the whole record of the deallocation, and it is two characters wide."}
     ],
     deep: [
       {t:'trace', title:'moveCell_spec, three states',
        start:"tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ b) (moveCell tmp src dst) (dst ↦ a)",
        steps:[
          {tac:'refine hoare_seq (Q := (src ↦ a) ∗ (dst ↦ a)) (copyCell_spec tmp src dst a b) ?_',
           state:"tmp : Var\nsrc dst : Loc\na b : Val\n⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
           h:"One goal, not two: the first argument was supplied rather than left as a hole. <code>b</code> is still in the context and no longer occurs in the goal, which is the point of the whole program — the value that was in <code>dst</code> is gone."},
          {tac:'have step : … := hoare_frame (hoare_free src a) (heapLocal_free src) (preserves_of_storeStable (storeStable_free src) _)',
           state:"tmp : Var\nsrc dst : Loc\na b : Val\nstep : Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (emp ∗ dst ↦ a)\n⊢ Hoare (src ↦ a ∗ dst ↦ a) (Cmd.free src) (dst ↦ a)",
           h:"Hypothesis and goal agree on the precondition and the command. The single difference is <code>emp ∗ dst ↦ a</code> against <code>dst ↦ a</code>, and reading that difference off the two lines is how you find the name of the last step."}
        ],
        done:"exact hoare_consequence (entails_refl _) step (star_emp_left _)"},
       {t:'p', h:"Compare the two halves. The first cost nothing because the middle assertion was chosen as the previous theorem&rsquo;s postcondition; the second cost one law because the free rule hands its cell back as <code>emp</code> and the frame rule carries that <code>emp</code> along. Every verification in this course is some mixture of those two situations, and the mixture is decided by the <code>(Q := …)</code>."}
     ],
     pitfall:"Choosing <code>(Q := (dst ↦ a) ∗ (src ↦ a))</code> — the cells in the order the specification&rsquo;s postcondition suggests. Then <code>copyCell_spec</code> no longer fits the first slot, and Lean says so by printing the two types one under the other with a single difference between them: <i>Application type mismatch: the argument <code>copyCell_spec tmp src dst a b</code> has type <code>Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (src ↦ a ∗ dst ↦ a)</code> but is expected to have type <code>Hoare (src ↦ a ∗ dst ↦ b) (copyCell tmp src dst) (dst ↦ a ∗ src ↦ a)</code></i>. Reading a mismatch that shape — same precondition, same command, postcondition&rsquo;s conjuncts swapped — is how you find out that you have bought a <code>star_comm</code> in the first half to save nothing in the second. The middle assertion should be read off the neighbours, and one of the neighbours here is a theorem you already have.",
     variants:"Free <code>dst</code> instead of <code>src</code> and the specification becomes <code>Hoare ((src ↦ a) ∗ (dst ↦ b)) … (src ↦ a)</code>, provable by the same four lines with one <code>star_comm</code> added, because the cell to be freed is now on the wrong side of the star. Drop the frame and try to prove the free rule against the whole precondition and it fails at the precondition: <code>hoare_free</code> wants <code>src ↦ a</code> exactly, and <code>(src ↦ a) ∗ (dst ↦ a)</code> does not entail it. Dropping a conjunct is exactly the move <code>star_not_weakening</code> denies, and its unavailability is why the frame rule had to be a rule rather than a weakening."},

    {t:'p', h:"Three programs, three proofs, and in none of the three does <code>Exec</code> appear. It does appear elsewhere on this page — in the definition of <code>StoreStable</code> and the two inversions that establish it, in the run that refutes it for <code>load</code>, and in <code>exec_seq_assoc</code> — and every one of those is a statement about the <i>language</i>, proved once and then cited by name. That is the division the rule at the top of the page was pointing at."},

    {t:'dod', h:"You can state the four moves and say which one requires a decision. You can prove a command store-stable and turn that into <code>Preserves</code> for any frame, and say which of the two dischargers applies to a given command and frame — and name the one pairing, a load with a store fact beside it, for which neither does. You can re-prove <code>readAndFree</code> without naming a heap. You can read a store-dependent postcondition, say why the fact that would simplify it has nowhere to enter, and use the rule whose precondition carries that fact instead. You can move a pure fact across a <code>∗</code> in either direction. Given a two-command program, you can write down the assertion between the commands by looking at the second command&rsquo;s footprint, and then finish the proof by following the types. And when the specification you want to reuse has the other bracketing, you can say why <code>hoare_seq</code> refuses it and lift it across with <code>exec_seq_assoc</code>."},

    {t:'p', h:"Two programs, both two commands long, and one of them took a page. A four-command program will need four intermediate assertions, all chosen by hand — and the only thing you have not seen is what happens when a <i>load</i> has to preserve a fact about a different variable."}

  ]
});
