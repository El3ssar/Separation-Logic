registerChapter({
  id: 'frame',
  num: '27',
  phase: 'Phase 5 · Locality and the frame rule',
  title: 'The frame rule',
  blurb: 'The theorem the course exists to prove: a command that meets a specification on the memory it touches meets the same specification inside any larger heap, with the rest carried along untouched. Eight lines, no induction, and no lemma about heaps.',

  orient: {
    youWill: [
      "Prove <code>hoare_frame</code>, and say which of its eight lines performs which of the five moves of the informal argument.",
      "Identify the single decision in the proof — how to cut the final heap in two — and watch the other cut fail, on the goal <code>⊢ Q r.store hR</code>.",
      "Say why <code>HeapLocal</code>&rsquo;s conclusion is written with the frame on the <i>right</i> of both <code>Heap.disjoint</code> and <code>Heap.union</code>, and price the alternative: two lemmas about heaps, in the one proof in the course where locality has to meet <code>∗</code>.",
      "List what the proof does not contain: no induction, no case analysis on <code>Exec</code>, no lemma about <code>∗</code>, no lemma about heaps, no determinism — and check that claim by proving the same theorem about an arbitrary relation on states.",
      "Specify a two-cell program in a proof of four lines in which no heap, no run and no final state appear.",
      "Replace that program&rsquo;s one-cell frame by an arbitrary assertion that does not mention the store, and watch the proof not change.",
      "Say where <code>l ≠ other</code> comes from in a two-cell specification, given that it is never a hypothesis.",
      "Name the language features that would make the rule false, and the one that is coming."
    ],
    needs: [
      "Unit 24: <code>HeapLocal</code> and its five components, <code>Preserves</code>, <code>preserves_of_heapOnly</code>, <code>heapOnly_pointsTo</code>, <code>heapOnly_star</code>, and the frame proof left standing on one <code>sorry</code>.",
      "Unit 25 and Unit 26: <code>heapLocal_write</code>, <code>heapLocal_free</code>, and the fact that every command in the language is local.",
      "Unit 22: <code>Hoare</code> as an existential over final states, <code>hoare_consequence</code>, and <code>hoare_write</code> / <code>hoare_free</code> from Unit 23.",
      "Unit 14 and Unit 15: the six slots of <code>∗</code>, and <code>star_emp_left</code>.",
      "Unit 17: <code>two_cells_distinct</code>."
    ],
    payoff: "Every specification proved after this page is proved by this rule. Unit 28 uses it to answer the question the course opened with; Unit 29 makes it one of four moves in a fixed recipe; Unit 31 shows what it looks like when the postcondition is computed rather than guessed. It is applied six times in the remaining Lean, and after this page nothing in the course opens <code>HeapLocal</code> again: the definition appears exactly once more in the whole corpus, as a hypothesis of a Unit 31 theorem."
  },

  blocks: [

    /* ============================================================ the theorem === */

    {t:'p', h:"Eight lines. Here is what they have to establish. You have a command <code>c</code>, an assertion <code>R</code> the command knows nothing about, and three facts: <code>c</code> takes <code>P</code> to <code>Q</code>, <code>c</code> is local, and <code>c</code> leaves <code>R</code> alone. The conclusion is that <code>c</code> takes <code>P ∗ R</code> to <code>Q ∗ R</code>. Two of those three hypotheses are the ones Unit 24 read off a goal that would not close; the third is the specification you started with. Nothing else is in scope, and nothing else is needed."},

    {t:'anat', tag:'verified',
     src:"theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by",
     parts:[
       {m:'(hc : Hoare P c Q)', h:"The specification being lifted. It says nothing about <code>R</code> and nothing about heaps larger than the ones <code>P</code> admits — which is the whole reason a rule is needed to reach them."},
       {m:'(hlocal : HeapLocal c)', h:"A fact about the command, not about the triple. Units 24 to 26 proved it for all eight constructors of <code>Cmd</code>, so at every use below it is discharged by a name."},
       {m:'(hpres : Preserves c R)', h:"A fact about the command <i>and this particular</i> <code>R</code>. It is not quantified over assertions: a command may preserve one frame and destroy another, and <code>frame_needs_preserves</code> is a command that does exactly that."},
       {m:'Hoare (P ∗ R) c (Q ∗ R)', h:"The same <code>R</code> on both sides, unchanged. Not <code>R&#39;</code>, not <code>R</code> weakened: the frame comes out of the run in the state it went in, and that claim is what <code>hpres</code> and the last equation of <code>HeapLocal</code> jointly pay for."}
     ]},

    {t:'p', h:"The argument in words takes five moves. Read them before the Lean; each of the eight lines belongs to one of them, and the mapping is exact."},

    {t:'steps', title:'The five moves',
     items:[
       {k:'Take the precondition apart', h:"<code>(P ∗ R) σ h</code> says: <code>h</code> cuts into <code>hP</code> and <code>hR</code>, disjointly, with <code>P</code> holding of the first and <code>R</code> of the second. Everything below runs on the two pieces rather than on <code>h</code>."},
       {k:'Run the command on the small heap', h:"<code>hc</code> applied at <code>σ</code> and <code>hP</code> returns a final state <code>s&#39;</code>, a run of <code>c</code> from <code>⟨σ, hP⟩</code> to it, and <code>Q</code> holding at that state. This is the specification you were given, spent whole."},
       {k:'Lift the run to the big heap', h:"<code>hlocal</code> applied to that run, with <code>hR</code> as the frame, returns four things: the final small heap is still disjoint from <code>hR</code>, there is a run of <code>c</code> from <code>⟨σ, hP ∪ hR⟩</code> to some state <code>r</code>, <code>r</code>&rsquo;s store is <code>s&#39;</code>&rsquo;s, and <code>r</code>&rsquo;s heap is <code>s&#39;</code>&rsquo;s with <code>hR</code> beside it. That run is the answer to the goal&rsquo;s existential."},
       {k:'Rebuild the star', h:"<code>(Q ∗ R)</code> at <code>r</code> needs a cut of <code>r.heap</code>. Take <code>s&#39;.heap</code> and <code>hR</code>. Disjointness and the union equation are the two things move 3 handed back; <code>Q</code> at the first piece is move 2&rsquo;s, once the two stores are identified."},
       {k:'Re-establish R at the new store', h:"<code>R</code> held of <code>hR</code> at the <i>initial</i> store. The goal wants it at <code>r.store</code>. Nothing about heaps closes that gap, because the gap is not about heaps; <code>hpres</code> is the hypothesis that closes it, and this is the only line that uses it."}
     ]},

    {t:'sec', s:'The one decision'},

    {t:'p', h:"Four of the five moves are forced. Move 1 is the only way to use a hypothesis of the form <code>(P ∗ R) σ h</code>; moves 2 and 3 apply hypotheses that take exactly the arguments in scope; move 5 has one hypothesis and one goal, and they match. Move 4 is where something is chosen. <code>Hoare</code>&rsquo;s conclusion is an existential over final states, and locality manufactured exactly one candidate, so the state is not the choice either. The choice is how to cut its heap."},

    {t:'state', cap:"The goal after moves 1 to 3, showing the goal line only. Every goal display in this unit is Lean&rsquo;s own output through <code>trace_state</code>, and where a display is trimmed the caption says what was left off. Here the eighteen context lines are omitted; <code>m8-5</code> carries a fold that prints the whole state one tactic earlier, when it is twenty lines long.",
     src:"⊢ ∃ s', Exec c { store := σ, heap := hP.union hR } s' ∧ (Q ∗ R) s'.store s'.heap"},

    {t:'p', h:"Supplying <code>r</code> for the existential and <code>hrex</code> for the run leaves <code>(Q ∗ R) r.store r.heap</code>, which is six slots."},

    {t:'tbl', cap:"The six components of <code>(Q ∗ R) r.store r.heap</code>. Column three is the point: two of them are Unit 24&rsquo;s definition, one is the small triple, one is the third hypothesis, and only the first two are written by you.",
     head:['slot', 'filled with', 'where it comes from'],
     rows:[
       ['the first heap', '<code>s&#39;.heap</code>', 'chosen'],
       ['the second heap', '<code>hR</code>', 'forced once the first is chosen'],
       ['<code>Heap.disjoint s&#39;.heap hR</code>', '<code>hdEnd</code>', '<code>HeapLocal</code>&rsquo;s first conjunct, verbatim'],
       ['<code>r.heap = Heap.union s&#39;.heap hR</code>', '<code>hrhp</code>', '<code>HeapLocal</code>&rsquo;s last equation, verbatim'],
       ['<code>Q r.store s&#39;.heap</code>', '<code>hq</code>, after rewriting <code>r.store</code>', 'the small triple, plus <code>HeapLocal</code>&rsquo;s store equation'],
       ['<code>R r.store hR</code>', '<code>hpres … hR hr</code>', '<code>Preserves</code>']
     ]},

    {t:'p', h:"Rows three and four are the reason no lemma about heaps appears anywhere in this proof. <code>HeapLocal</code>&rsquo;s conclusion could have been written the other way round — <code>Heap.disjoint hFrame s&#39;.heap</code> and <code>r.heap = Heap.union hFrame s&#39;.heap</code> — and it would have been as true a statement about every command in the language. Under that orientation the two things locality returns no longer <i>are</i> slots three and four; they are those slots up to symmetry, and lining them up costs a <code>disjoint_symm</code> and a <code>union_comm</code>. Unit 26 would not have noticed: its proofs consume <code>HeapLocal</code> and produce <code>HeapLocal</code>, so a swapped orientation swaps on both sides and cancels. The orientation is felt only where locality has to meet <code>∗</code>, and in the whole course that happens once — in the eight lines below. Unit 24 made the choice; this is the page that pays for it, which is why it could not be priced there."},

    {t:'p', h:"Try the other cut, because it fails late. Give the two heaps as <code>hR</code> and <code>s&#39;.heap</code>, in that order. Slot three now wants <code>Heap.disjoint hR s&#39;.heap</code>, which <code>disjoint_symm hdEnd</code> supplies; slot four wants <code>r.heap = Heap.union hR s&#39;.heap</code>, which is <code>hrhp</code> followed by <code>union_comm hdEnd</code>. Two lemmas, both available, both fine. Then slot five:"},

    {t:'state', cap:"What the swapped cut leaves at slot five, goal line only; the eighteen context lines are the same ones as before. <code>Q</code> is being asked to hold of the frame&rsquo;s heap, which is not something any hypothesis says or any command makes true. The wrong cut is not caught where it is made; it is caught two slots later, after two lemmas have been spent making it look right.",
     src:"⊢ Q r.store hR"},

    {t:'ex',
     id:'m8-5',
     name:'hoare_frame',
     hard: true,
     why:"The theorem the course exists to prove. Five declarations in the remaining Lean apply it, six times over — one in Unit 28, three in Unit 29, one in Unit 31 — and not one of them opens <code>HeapLocal</code> or <code>∗</code>. After this proof, verifying a program is applying rules.",
     setup:"Everything you need is in the three hypotheses. No lemma from any earlier unit appears in the solution: not <code>union_comm</code>, not <code>disjoint_symm</code>, not <code>star_comm</code>, nothing about <code>Heap</code> at all. Unit 24 left this proof standing on a single <code>sorry</code>, with <code>hpres</code> not yet in the statement; the missing line is the one that uses it.",
     goal:"theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by",
     hints:[
       "Unfold nothing and read the goal. <code>Hoare (P ∗ R) c (Q ∗ R)</code> is: for every store <code>σ</code> and heap <code>h</code>, if <code>(P ∗ R) σ h</code> then there is a state <code>s&#39;</code> with a run of <code>c</code> from <code>⟨σ, h⟩</code> to <code>s&#39;</code> and <code>(Q ∗ R) s&#39;.store s&#39;.heap</code>. The hypothesis gives you a cut of <code>h</code>. The goal asks you for a cut of the final heap.",
       "Split <code>h</code> into <code>hP</code> and <code>hR</code>. Run <code>c</code> on <code>hP</code> alone — that is what <code>hc</code> is for — and get a final state <code>s&#39;</code>. Now lift that run to <code>hP ∪ hR</code> with locality, taking <code>hR</code> as the frame; it returns a run ending at a state whose heap is <code>s&#39;.heap ∪ hR</code>. Cut there. The <code>Q</code> half is the small run&rsquo;s postcondition; the <code>R</code> half is <code>hR</code>, which no one touched — but at the new store, and that is the last hypothesis.",
       "<code>intro</code>, then <code>obtain</code> three times: once on the star&rsquo;s six components, once on the existential <code>hc</code> returns, once on the five components <code>hlocal</code> returns. Then <code>subst</code> on the union equation, so that the goal stops mentioning <code>h</code> and starts mentioning <code>hP.union hR</code> — which is what the lifted run is a run on. Then one <code>refine</code> whose bracket has eight components: the existential&rsquo;s witness, the run, and the star&rsquo;s six, flattened. Six of the eight are names already in the context; leave the other two as <code>?_</code>. The first of those closes with <code>rw</code> on the store equation, and the second is the only place <code>hpres</code> is ever mentioned.",
       "<code>intro σ h hstar</code> then <code>obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar</code>. That leaves the goal unchanged and puts six things in the context: two heaps, <code>hd : hP.disjoint hR</code>, <code>hu : h = hP.union hR</code>, <code>hp : P σ hP</code> and <code>hr : R σ hR</code>. The next two lines apply <code>hc</code> and <code>hlocal</code>; the arguments they want are all in that list. <code>hd</code> is used exactly once in the whole proof, as an argument to <code>hlocal</code>."
     ],
     sol:"theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  obtain ⟨s', hex, hq⟩ := hc σ hP hp\n  obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex\n  subst hu\n  refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩\n  · rw [hrst]; exact hq\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
     solNote:"Lines 1 and 2 are move 1, line 3 is move 2, line 4 is move 3, lines 5 to 7 are move 4, line 8 is move 5. If you climbed all four hints and are still stuck, open this without guilt — the assembly is the lesson, not the search.",
     expl:"Three hypotheses, three <code>obtain</code>s, one <code>refine</code> and two one-line goals. The proof is the informal argument transcribed: every name that appears in it came out of a hypothesis a line or two above, and no name comes from the library.",
     walk:[
       {tac:'intro σ h hstar', h:"Peels the three binders of <code>Hoare</code>. The goal becomes the existential over final states, with <code>h</code> the whole heap and <code>hstar</code> the split-precondition assumption."},
       {tac:"obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar", h:"Consumes the star. Six things arrive at once: the two heaps, their disjointness, the equation saying they rebuild <code>h</code>, and the two assertions. Note what is <i>not</i> yet true: the goal still speaks of <code>h</code>, not of <code>hP.union hR</code>."},
       {tac:"obtain ⟨s', hex, hq⟩ := hc σ hP hp", h:"Applies the specification you were given, at the small heap. <code>hP</code> is the heap <code>P</code> holds of, and <code>hp</code> is the proof. Out comes the small run and its postcondition. This is the only line that mentions <code>hc</code>."},
       {tac:"obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex", h:"The lift. Locality wants a store, a small heap, a frame, a final state, a disjointness proof and a run — six arguments, all in the context. It returns five things, and four of them are consumed by the <code>refine</code> two lines down. <code>hd</code> is spent here and never mentioned again."},
       {tac:'subst hu', h:"Eliminates <code>h</code> everywhere in favour of <code>hP.union hR</code>. The goal now asks for a run of <code>c</code> on <code>hP.union hR</code> — which is exactly the run <code>hrex</code> is. Without this line <code>hrex</code> does not fit the slot; see the pitfall."},
       {tac:"refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩", h:"Eight components in one bracket: the existential&rsquo;s witness and the run, then the star&rsquo;s six, flattened. Slots three and four are the decision; slots five and six are <code>HeapLocal</code>&rsquo;s output placed where <code>∗</code> wants it, with no lemma in between."},
       {tac:'· rw [hrst]; exact hq', h:"The goal here is <code>Q r.store s&#39;.heap</code> — a mixed state, because the answer state is <code>r</code> but the heap you cut is <code>s&#39;</code>&rsquo;s. <code>hrst : r.store = s'.store</code> rewrites the store, and then the goal is literally <code>hq</code>."},
       {tac:"· exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr", h:"<code>Preserves c R</code> takes two states, a run between them, a heap and <code>R</code> at the first store. The initial state has to be written out, because the goal names only <code>r</code>; it is the state the lifted run starts from. The result is <code>R r.store hR</code>, which is the goal."}
     ],
     deep:[
       {t:'trace', title:'hoare_frame, six steps',
        start:"P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\n⊢ Hoare (P ∗ R) c (Q ∗ R)",
        steps:[
          {tac:'intro σ h hstar',
           state:"σ : Store\nh : Heap\nhstar : (P ∗ R) σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
           h:"Only the lines that changed are shown, here and in every step below; the five hypotheses of the statement stay in the context throughout. <code>Hoare</code>&rsquo;s body has appeared, and the pair <code>⟨σ, h⟩</code> is printed as the structure literal it is."},
          {tac:"obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
           state:"h hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
           h:"<code>hstar</code> is gone and six lines stand in its place. The goal has not moved: it still speaks of <code>h</code>, and <code>hu</code> is the only thing connecting <code>h</code> to the two pieces."},
          {tac:"obtain ⟨s', hex, hq⟩ := hc σ hP hp",
           state:"s' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
           h:"The small run. <code>hex</code> starts at <code>hP</code>, which is not the heap the goal is about — that is the gap locality exists to close."},
          {tac:"obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex",
           state:"hdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR",
           h:"Five lines, and four of them will be handed to the <code>refine</code> unmodified. The goal is unchanged and is left off here; the full twenty-line state is in the fold below."},
          {tac:'subst hu',
           state:"⊢ ∃ s', Exec c { store := σ, heap := hP.union hR } s' ∧ (Q ∗ R) s'.store s'.heap",
           h:"<code>h</code> and <code>hu</code> leave the context and every occurrence of <code>h</code> becomes <code>hP.union hR</code>. The goal&rsquo;s run and <code>hrex</code> now start from the same state."},
          {tac:"refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩",
           state:"case refine_1\n⊢ Q r.store s'.heap\n\ncase refine_2\n⊢ R r.store hR",
           h:"Six of the eight slots closed on the spot. What is left is one store mismatch and one appeal to <code>Preserves</code> — one line each."}
        ],
        done:'No goals.'},
       {t:'detail', title:'The whole state at step 4, all twenty lines', blocks:[
         {t:'p', h:"Everything the three hypotheses have produced, at the moment before <code>subst</code>. Read it once for the shape: twelve of the twenty lines were produced by the three <code>obtain</code>s, two more names are grouped onto line 7 beside the <code>h</code> they came out of, and the goal at the bottom is the only thing that has not moved since the first tactic."},
         {t:'state', src:"P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap"}
       ]},
       {t:'p', h:"The cut is not something Lean will find. Write the <code>refine</code> with all six star slots as holes and the third goal comes back with metavariables where the heaps should be:"},
       {t:'state', cap:"After <code>refine ⟨r, hrex, ?_, ?_, ?_, ?_, ?_, ?_⟩</code>, third goal, goal line only. <code>?refine_1</code> and <code>?refine_2</code> are the two heaps, still undetermined. Nothing later in the proof forces them, which is why they are written out rather than left to unification.",
        src:"⊢ Heap.disjoint ?refine_1 ?refine_2"}
     ],
     pitfall:"Dropping <code>subst hu</code>. Everything still elaborates until the bracket, and then the report names <code>And.intro</code>, which appears nowhere in what you wrote:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;hrex<br>has type<br>&nbsp;&nbsp;Exec c { store := σ, heap := hP.union hR } r<br>but is expected to have type<br>&nbsp;&nbsp;Exec c { store := σ, heap := h } r<br>in the application<br>&nbsp;&nbsp;And.intro hrex</code><br><br><code>And.intro</code> is there because <code>∃ s&#39;, Exec … ∧ …</code> is an <code>Exists</code> whose body is an <code>And</code>, and the flattened bracket fills both. The fix is one line, five lines earlier: <code>hu</code> is an equation between heaps and <code>subst</code> is what spends it.",
     variants:"Drop <code>hpres</code> and the theorem is false rather than open — Unit 24&rsquo;s <code>frame_needs_preserves</code> is the witness, and refuting the weakened rule from it takes three lines, which are in the first of the three folds at the foot of this page.<br><br>Drop <code>hlocal</code> and you cannot start move 3. After the second <code>obtain</code> the context holds exactly one run of <code>c</code>, namely <code>hex : Exec c { store := σ, heap := hP } s&#39;</code>, and the goal&rsquo;s existential is about a run starting at <code>hP.union hR</code>. Nothing else in scope produces one, and <code>hd</code> — the only other thing that mentions both heaps — is a disjointness, not a run.<br><br>Weaken <code>hlocal</code> to Unit 24&rsquo;s <code>HeapLocalWeak</code> and line 4 loses a name: the pattern becomes <code>obtain ⟨r, hrex, hrst, hrhp⟩</code>, four components rather than five. Everything through <code>subst</code> is unchanged, and then the <code>refine</code>&rsquo;s fifth slot has to become a hole. What stands under it is<br><br><code>⊢ s&#39;.heap.disjoint hR</code><br><br>with <code>hd : hP.disjoint hR</code> the only disjointness in the context and nothing at all relating <code>s&#39;.heap</code> to <code>hR</code>. That stranded goal is the reason <code>HeapLocal</code> has five components instead of four.<br><br>Reverse the conclusion to <code>Hoare (R ∗ P) c (R ∗ Q)</code> — the frame on the left of both stars — and the theorem is still true, at a price you can count. <code>hu</code> now reads <code>h = hR.union hP</code> while <code>hlocal</code> returns a run on <code>hP.union hR</code>, so the equation has to be turned round with <code>rw [union_comm hd] at hu</code> before <code>subst</code>, and the star&rsquo;s union slot, which was <code>hrhp</code> unmodified, becomes <code>rw [hrhp, union_comm hdEnd]</code> on a line of its own. The disjointness handed to <code>hlocal</code> and the star&rsquo;s disjointness slot each take a <code>disjoint_symm</code>. Ten lines for the same theorem, four appeals to lemmas about heaps where there were none, and every later application inherits the swapped order."
    },

    {t:'sec', s:'What the proof does not contain'},

    {t:'p', h:"Read the eight lines again and list what is absent. There is no <code>induction</code>, on the command or on anything else. There is no <code>cases</code> on <code>Exec</code>: the proof never asks which command <code>c</code> is, and would not know what to do with the answer. There is no <code>funext</code> and no lemma about heaps — the term <code>Heap.union hP hR</code> occurs once, inside the state literal handed to <code>hpres</code>, and is never something reasoned about. There is no lemma about <code>∗</code>: the connective is taken apart and put back together by the anonymous constructor, which is Unit 14&rsquo;s two mechanical moves and nothing more. And there is no appeal to determinism, to finiteness of heaps, or to anything at all about which commands the language has."},

    {t:'note', kind:'key', title:'The frame rule is not about this language',
     h:"Everything the proof uses about <code>Exec</code> is contained in the two hypotheses. Replace <code>Exec c</code> by an arbitrary relation <code>E</code> on states, restate <code>Hoare</code>, <code>HeapLocal</code> and <code>Preserves</code> over <code>E</code>, and the same eight lines go through character for character. That is the sense in which locality is the right condition: it is not a property Lean happens to be able to check for the eight constructors of <code>Cmd</code>, it is the exact hypothesis the frame rule needs, and any semantics that satisfies it — a different language, a different memory model, a nondeterministic one — gets the rule for free."},

    {t:'detail', title:'The same theorem about an arbitrary relation, compiled', tag:'aside', blocks:[
      {t:'p', h:"Three definitions with <code>Exec c</code> replaced by <code>E : State → State → Prop</code>, and the proof body copied without a character changed. The command has disappeared entirely — <code>frame_on</code> does not mention <code>Cmd</code>."},
      {t:'code', tag:'illustration',
       src:"def HoareOn (E : State → State → Prop) (P Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', E ⟨σ, h⟩ s' ∧ Q s'.store s'.heap\n\ndef LocalOn (E : State → State → Prop) : Prop :=\n  ∀ σ h hFrame s',\n    Heap.disjoint h hFrame →\n    E ⟨σ, h⟩ s' →\n    Heap.disjoint s'.heap hFrame ∧\n    ∃ r : State,\n      E ⟨σ, Heap.union h hFrame⟩ r ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame\n\ndef PreservesOn (E : State → State → Prop) (R : Assertion) : Prop :=\n  ∀ s s', E s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame\n\ntheorem frame_on {P Q R : Assertion} {E : State → State → Prop}\n    (hc : HoareOn E P Q) (hlocal : LocalOn E) (hpres : PreservesOn E R) :\n    HoareOn E (P ∗ R) (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  obtain ⟨s', hex, hq⟩ := hc σ hP hp\n  obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex\n  subst hu\n  refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩\n  · rw [hrst]; exact hq\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
       cap:"Compiled against this unit&rsquo;s context. What still appears is <code>Heap</code>, <code>State</code> and <code>∗</code> — the resource model. Unit 38 removes those too."}
    ]},

    {t:'p', h:"One more absence, and it is the one that pays for modularity. The proof never uses the initial disjointness <code>hd</code> for anything. It does not read it, case on it, or rewrite with it; it passes it to <code>hlocal</code> as an argument and forgets it. So the frame rule does not know that <code>P</code> and <code>R</code> describe separate memory — it knows only that whoever proved <code>c</code> local was told so. All the work of keeping the frame intact was done once, in Units 24 to 26, at the level of the semantics. Nothing about it recurs when the rule is used, which is what the rest of the course is about to rely on."},

    {t:'sec', s:'Spending it'},

    {t:'p', h:"A two-cell program. The heap holds a cell at <code>l</code> and a cell at <code>other</code>; the program writes a constant to <code>l</code>; afterwards the first cell holds the new value and the second is untouched. Unit 23 has the rule for the write on its own footprint, Unit 25 has locality for <code>write</code>, and Unit 24 has the fact that a points-to assertion says nothing about the store. Those three plus the frame rule are the whole specification."},

    {t:'ex',
     id:'m8-6',
     name:'write_with_frame',
     why:"Four lines against the twenty-six of <code>heapLocal_write</code>, and the contrast is the lesson: this is what verifying a program looks like once the semantic work is done. No fragment after this one cites <code>write_with_frame</code> itself — Unit 28 proves its own two-cell specification the same way, from the same four names — so what carries forward is the shape, not the theorem.",
     setup:"Two things to supply beyond the base triple: locality of <code>.write l (.const new)</code>, and the fact that <code>c</code> preserves <code>other ↦ w</code>. The second goes through <code>preserves_of_heapOnly</code>, whose first argument is the command and whose second is a proof of <code>HeapOnly</code>. Nothing in the solution mentions a heap.",
     goal:"theorem write_with_frame (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new)) ((l ↦ new) ∗ (other ↦ w)) := by",
     hints:[
       "Unfold the triple and read it. <code>Hoare P c Q</code> is: for every <code>σ</code> and <code>h</code> with <code>P σ h</code>, there is a final state <code>s&#39;</code> with a run of <code>c</code> from <code>⟨σ, h⟩</code> and <code>Q s&#39;.store s&#39;.heap</code>. Here <code>P</code> holds of a heap that cuts into exactly two cells, <code>l</code> holding <code>old</code> and <code>other</code> holding <code>w</code>; <code>Q</code> is the same cut with <code>old</code> replaced by <code>new</code>; the command mentions <code>l</code> and no other address. There is no hypothesis <code>l ≠ other</code>, and none is missing.",
       "One of the two cells is a frame: the command cannot reach it, so it comes out of the run exactly as it went in. Delete it from both ends of the goal and what remains is the write&rsquo;s specification on its own single cell, which you proved in Unit 23. The move you want is a rule that runs that argument in reverse — takes a triple and puts the same assertion on both of its ends — and such a rule asks three things: the triple, that the command is local, and that the command leaves the added assertion alone. Two of those three you have as theorems about this command; the third holds because a points-to assertion says nothing about the store, so nothing a command can do to the store disturbs it.",
       "<code>hoare_frame</code> is the rule. <code>hoare_write</code> for the base triple, <code>heapLocal_write</code> for the second hypothesis, and <code>preserves_of_heapOnly</code> applied to <code>heapOnly_pointsTo</code> for the third. All four are theorems from Units 23, 24 and 25, and the only tactics are <code>have</code> and <code>exact</code>.",
       "<code>have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) := hoare_write l (.const new) old</code>. That leaves the goal untouched and puts <code>base</code> in the context; the restatement is what makes the eta-expanded postcondition of <code>hoare_write</code> readable. Then one <code>exact hoare_frame base …</code> with the other two hypotheses."
     ],
     sol:"theorem write_with_frame (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new)) ((l ↦ new) ∗ (other ↦ w)) := by\n  have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=\n    hoare_write l (.const new) old\n  exact hoare_frame base (heapLocal_write l (.const new))\n    (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
     expl:"Two tactics. The first names the small-footprint triple in the form the frame rule wants to see it; the second lifts it. Four theorem names, and the word <code>Heap</code> does not occur in the proof.",
     walk:[
       {tac:'have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) := hoare_write l (.const new) old', h:"<code>hoare_write</code>&rsquo;s postcondition is written <code>fun σ h =&gt; (l ↦ (e.eval σ)) σ h</code>, because in general the value written depends on the store. Here <code>e</code> is <code>.const new</code>, so the evaluation reduces and the postcondition is <code>l ↦ new</code>. The <code>have</code> states that, and Lean accepts it by computation. It changes nothing in the goal; it changes what the next line reads like."},
       {tac:'exact hoare_frame base (heapLocal_write l (.const new)) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))', h:"Three arguments in the order the rule declares them. The second is Unit 25&rsquo;s theorem at this command. The third builds a <code>Preserves</code> out of a <code>HeapOnly</code>: <code>preserves_of_heapOnly</code> takes the command first and the <code>HeapOnly</code> proof second, and the command is inferrable from the goal, so it is written <code>_</code>."}
     ],
     deep:[
       {t:'trace', title:'Two tactics, two states',
        start:"l other : Loc\nold new w : Val\n⊢ Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)",
        steps:[
          {tac:'have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) := hoare_write l (.const new) old',
           state:"l other : Loc\nold new w : Val\nbase : Hoare (l ↦ old) (Cmd.write l (Atom.const new)) (l ↦ new)\n⊢ Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)",
           h:"One line added. Compare it with the goal: the same command, the same two assertions, with <code>∗ other ↦ w</code> removed from both ends. That difference is exactly what <code>hoare_frame</code> installs."},
          {tac:"exact hoare_frame base (heapLocal_write l (.const new)) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
           state:"No goals.",
           h:"The command in the goal and the command in <code>base</code> are the same term, so nothing has to be matched up; the rule&rsquo;s <code>R</code> is fixed by the goal&rsquo;s two stars, and the <code>_</code> is fixed by that."}
        ],
        done:'No goals.'}
     ],
     pitfall:"Writing <code>preserves_of_heapOnly (heapOnly_pointsTo other w)</code> without the leading <code>_</code>. <code>preserves_of_heapOnly</code>&rsquo;s first explicit argument is the <i>command</i>, and the error reads as though something were wrong with <code>heapOnly_pointsTo</code>:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;heapOnly_pointsTo other w<br>has type<br>&nbsp;&nbsp;HeapOnly (other ↦ w)<br>of sort `Prop` but is expected to have type<br>&nbsp;&nbsp;Cmd<br>of sort `Type` in the application<br>&nbsp;&nbsp;preserves_of_heapOnly (heapOnly_pointsTo other w)</code><br><br>Read the last two lines first: the application named there is the one that is wrong, and the argument is in the wrong <i>position</i>, not of the wrong kind.",
     variants:"The <code>have</code> is not required. <code>exact hoare_frame (hoare_write l (.const new) old) (heapLocal_write l (.const new)) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))</code> compiles on its own, because <code>(Atom.const new).eval σ</code> reduces to <code>new</code> and <code>exact</code> works up to that. The <code>have</code> buys a readable statement of what is being lifted, and nothing else.<br><br>Add <code>(hne : l ≠ other)</code> as a hypothesis and the proof is unchanged; Lean reports <code>Variable name `hne` is not explicitly referenced.</code> The disequality is not needed, and the rest of this section says where it lives instead.<br><br>Put the frame on the <i>left</i> — <code>Hoare ((other ↦ w) ∗ (l ↦ old)) (.write l (.const new)) ((other ↦ w) ∗ (l ↦ new))</code> — and the same <code>exact</code> stops type-checking, with the two triples printed one above the other:<br><br><code>has type<br>&nbsp;&nbsp;Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)<br>but is expected to have type<br>&nbsp;&nbsp;Hoare (other ↦ w ∗ l ↦ old) (Cmd.write l (Atom.const new)) (other ↦ w ∗ l ↦ new)</code><br><br>The frame rule appends its frame on the right and there is nothing inside it that will commute a star. The repair is one line — <code>hoare_consequence (star_comm _ _) framed (star_comm _ _)</code>, with <code>framed</code> the result of the <code>exact</code> above — and Unit 29 pays it whenever a program&rsquo;s cells arrive in an order the small rules did not choose."
    },

    {t:'p', h:"Here is the same specification without the frame rule, proved from the semantics the way Unit 23 had to prove <code>readAndFree_spec</code>, with no structural rule to hand."},

    {t:'cmp',
     left:{t:'With the frame rule', kind:'good',
           h:"Two tactics, four theorem names, no heap term anywhere, and no goal state longer than four lines.",
           src:"have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=\n  hoare_write l (.const new) old\nexact hoare_frame base (heapLocal_write l (.const new))\n  (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
           tag:'sketch'},
     right:{t:'From the semantics, as Unit 23 had to',
            h:"Seven tactics. It builds the final heap by hand, produces the <code>Exec.write</code> derivation itself, extracts <code>l ≠ other</code> from the disjointness of the two singletons and puts it back to rebuild the postcondition&rsquo;s star — and the equation it finishes on is <code>write_union_no_disjointness</code>, the same heap equation <code>heapLocal_write</code> proves inline rather than citing.",
            src:"theorem write_with_frame_by_hand (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new)) ((l ↦ new) ∗ (other ↦ w)) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  subst hp; subst hq; subst hu\n  have hne : l ≠ other := (singleton_disjoint_iff old w).mp hd\n  refine ⟨⟨σ, Heap.write (Heap.union (Heap.singleton l old) (Heap.singleton other w)) l new⟩,\n          Exec.write (union_of_some _ (singleton_same l old)),\n          Heap.singleton l new, Heap.singleton other w,\n          (singleton_disjoint_iff new w).mpr hne, ?_, rfl, rfl⟩\n  rw [write_union_no_disjointness, write_singleton]",
            tag:'illustration'}},

    {t:'p', h:"Seven tactics against two, and the count is not the comparison. The right-hand one is written against <i>this</i> frame: change <code>other ↦ w</code> to two cells and the bracket grows, the disjointness argument grows, and the final rewrite has to be redone. The left-hand one does not mention the frame at all."},

    {t:'p', h:"The right-hand proof extracts <code>l ≠ other</code> in its third line and the left-hand one never mentions it, which is the whole difference between this specification and the one a classical Hoare logic would write. There, the rule for a write in the presence of another cell carries <code>l ≠ other</code> as a side condition, and the side condition has to be discharged by whoever applies it. Here it is not a hypothesis, and it is not missing either. It is in the precondition: <code>(l ↦ old) ∗ (other ↦ w)</code> can only hold of a heap that cuts into two disjoint pieces, one of which is <code>Heap.singleton l old</code> and the other <code>Heap.singleton other w</code>, and two singletons are disjoint exactly when their addresses differ. Unit 17 proved that and called it <code>two_cells_distinct</code>."},

    {t:'code', tag:'illustration',
     cap:"The disequality, recovered from the precondition alone by a theorem you already have. Anyone who <i>supplies</i> the precondition has already supplied this; the specification does not have to ask for it.",
     src:"theorem ne_from_precondition (l other : Loc) (old w : Val) :\n    (l ↦ old) ∗ (other ↦ w) ⊢ fact (fun _ => l ≠ other) :=\n  two_cells_distinct l other old w"},

    {t:'sec', s:'The size of the frame'},

    {t:'p', h:"Nothing in <code>hoare_frame</code> looks at <code>R</code>, so nothing in <code>write_with_frame</code> depends on the frame being one cell. The only demand made of the frame is <code>Preserves c R</code>, and Unit 24&rsquo;s <code>preserves_of_heapOnly</code> discharges that for any <code>R</code> that does not mention the store — without inspecting the command, the run, or <code>R</code>&rsquo;s heap. So the general statement is available at once."},

    {t:'code', tag:'illustration',
     cap:"The same four names, with <code>other ↦ w</code> replaced by an arbitrary assertion about the heap. The proof body is character for character the one in <code>write_with_frame</code>, with <code>heapOnly_pointsTo other w</code> replaced by the hypothesis.",
     src:"theorem write_with_frame_any {R : Assertion} (hR : HeapOnly R)\n    (l : Loc) (old new : Val) :\n    Hoare ((l ↦ old) ∗ R) (.write l (.const new)) ((l ↦ new) ∗ R) := by\n  have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=\n    hoare_write l (.const new) old\n  exact hoare_frame base (heapLocal_write l (.const new))\n    (preserves_of_heapOnly _ hR)"},

    {t:'p', h:"To use it you need <code>HeapOnly R</code>, and Unit 24&rsquo;s <code>heapOnly_star</code> closes <code>HeapOnly</code> under <code>∗</code>. A frame of ten cells is therefore ten applications of <code>heapOnly_pointsTo</code> glued by nine of <code>heapOnly_star</code>, and the specification of the write across it is one line with no proof in it."},

    {t:'code', tag:'illustration',
     cap:"A ten-cell frame, and the write specified across it. The last theorem&rsquo;s proof is an application. Ten thousand cells would be the same application; the only thing that grows is the term establishing <code>HeapOnly</code>, and it grows in the frame&rsquo;s definition, not in any program proof.",
     src:"def tenCells (b : Loc) : Assertion :=\n  (b+1 ↦ 1) ∗ ((b+2 ↦ 2) ∗ ((b+3 ↦ 3) ∗ ((b+4 ↦ 4) ∗ ((b+5 ↦ 5) ∗\n  ((b+6 ↦ 6) ∗ ((b+7 ↦ 7) ∗ ((b+8 ↦ 8) ∗ ((b+9 ↦ 9) ∗ (b+10 ↦ 10)))))))))\n\ntheorem heapOnly_tenCells (b : Loc) : HeapOnly (tenCells b) :=\n  heapOnly_star (heapOnly_pointsTo _ _) (heapOnly_star (heapOnly_pointsTo _ _)\n   (heapOnly_star (heapOnly_pointsTo _ _) (heapOnly_star (heapOnly_pointsTo _ _)\n    (heapOnly_star (heapOnly_pointsTo _ _) (heapOnly_star (heapOnly_pointsTo _ _)\n     (heapOnly_star (heapOnly_pointsTo _ _) (heapOnly_star (heapOnly_pointsTo _ _)\n      (heapOnly_star (heapOnly_pointsTo _ _) (heapOnly_pointsTo _ _)))))))))\n\ntheorem write_with_ten_cell_frame (l b : Loc) (old new : Val) :\n    Hoare ((l ↦ old) ∗ tenCells b) (.write l (.const new)) ((l ↦ new) ∗ tenCells b) :=\n  write_with_frame_any (heapOnly_tenCells b) l old new"},

    {t:'p', h:"The proof of <code>write_with_frame_by_hand</code> has no counterpart here. It worked by producing the final heap explicitly and proving an equation about it, and neither is possible when <code>R</code>&rsquo;s heap is a variable: there is no term to write down and no equation to prove. The length of a verification stops tracking the size of the memory at exactly the point where the frame rule takes over, and that is the property the whole of Module 6 was for."},

    {t:'sec', s:'The same lift, a different rule'},

    {t:'p', h:"Deallocation. <code>hoare_free</code> ends in <code>emp</code>, because a small-footprint rule owns exactly the cell it frees and hands back nothing. Framed, that becomes <code>emp ∗ (other ↦ w)</code>, which is not the postcondition anyone wants to read. Unit 15&rsquo;s unit law is what removes it, and this is the first place in the course where it has a program proof to do it in."},

    {t:'ex',
     id:'x54',
     name:'free_with_frame',
     why:"Two rules, the same lift, and a postcondition that needs tidying. The tidying is <code>hoare_consequence</code> with <code>entails_refl</code> for the precondition and a real entailment for the postcondition — the exact shape Unit 29 uses five times over, and the reason its recipe has four moves rather than three. No later fragment cites <code>free_with_frame</code>; what it drills is the assembly.",
     setup:"Three steps rather than two: the base triple, the frame rule, and then a consequence to turn <code>emp ∗ (other ↦ w)</code> into <code>other ↦ w</code>. Naming the framed triple with a <code>have</code> keeps the last line short enough to read.",
     goal:"theorem free_with_frame (l other : Loc) (v w : Val) :\n    Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (other ↦ w) := by",
     hints:[
       "Unfolded, the goal says: for every <code>σ</code> and every heap that cuts into a cell at <code>l</code> holding <code>v</code> and a cell at <code>other</code> holding <code>w</code>, there is a run of <code>.free l</code> from there ending in a state whose heap is the single cell <code>other ↦ w</code> and nothing else. The precondition is a star; the postcondition is not. That asymmetry is the whole exercise.",
       "The cell at <code>other</code> is the frame, so the shape is the same lift as the write — but framing puts the added assertion on <i>both</i> ends of the triple, and the deallocation rule ends in <code>emp</code>, because a rule that owns exactly the cell it frees hands back an empty heap. So the lift cannot land on the goal: it lands on <code>emp ∗ (other ↦ w)</code>. Prove that triple with the postcondition it actually has, then weaken it. <code>emp ∗ (other ↦ w)</code> entails <code>other ↦ w</code> by the left unit law, which Unit 15 already proved, and weakening a postcondition is what the structural rule of Unit 22 is for.",
       "<code>hoare_free</code>, <code>heapLocal_free</code>, <code>preserves_of_heapOnly</code> with <code>heapOnly_pointsTo</code>, then <code>hoare_consequence</code>. Its three arguments are an entailment into the precondition, the triple, and an entailment out of the postcondition; the first is <code>entails_refl</code> because the precondition is not changing. The last is <code>star_emp_left</code>.",
       "<code>have base : Hoare (l ↦ v) (.free l) emp := hoare_free l v</code>, then a second <code>have framed : Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (emp ∗ (other ↦ w)) := hoare_frame base …</code>. That leaves the goal untouched, with two triples in the context, one of which differs from the goal only in its postcondition."
     ],
     sol:"theorem free_with_frame (l other : Loc) (v w : Val) :\n    Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (other ↦ w) := by\n  have base : Hoare (l ↦ v) (.free l) emp := hoare_free l v\n  have framed : Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (emp ∗ (other ↦ w)) :=\n    hoare_frame base (heapLocal_free l) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))\n  exact hoare_consequence (entails_refl _) framed (star_emp_left _)",
     expl:"Three tactics, one per rule. The middle one is <code>write_with_frame</code> with <code>free</code> in place of <code>write</code>; the last one exists only because a small-footprint rule leaves an <code>emp</code> behind, and a rule that leaves an <code>emp</code> behind is the price of owning exactly what you touch.",
     walk:[
       {tac:'have base : Hoare (l ↦ v) (.free l) emp := hoare_free l v', h:"The unframed triple, stated with its real postcondition. <code>emp</code> is not a placeholder for &ldquo;nothing to say&rdquo;; it is the assertion that the heap in hand is empty, which is what is left after you free the one cell you owned."},
       {tac:'have framed : Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (emp ∗ (other ↦ w)) := hoare_frame base (heapLocal_free l) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))', h:"The lift. Writing out the resulting statement is what makes the mismatch with the goal visible in one glance: the precondition already matches, and the postcondition is off by an <code>emp</code>."},
       {tac:'exact hoare_consequence (entails_refl _) framed (star_emp_left _)', h:"<code>hoare_consequence</code> strengthens the precondition and weakens the postcondition. Nothing is being asked of the precondition, so the first argument is the identity entailment; the third turns <code>emp ∗ (other ↦ w)</code> into <code>other ↦ w</code>. The underscore in <code>star_emp_left _</code> is the assertion <code>other ↦ w</code>, inferred from the goal."}
     ],
     deep:[
       {t:'trace', title:'free_with_frame, three states',
        start:"l other : Loc\nv w : Val\n⊢ Hoare (l ↦ v ∗ other ↦ w) (Cmd.free l) (other ↦ w)",
        steps:[
          {tac:'have base : Hoare (l ↦ v) (.free l) emp := hoare_free l v',
           state:"l other : Loc\nv w : Val\nbase : Hoare (l ↦ v) (Cmd.free l) emp\n⊢ Hoare (l ↦ v ∗ other ↦ w) (Cmd.free l) (other ↦ w)",
           h:"The small-footprint rule, in the context. Its postcondition and the goal&rsquo;s have nothing in common yet."},
          {tac:"have framed : Hoare ((l ↦ v) ∗ (other ↦ w)) (.free l) (emp ∗ (other ↦ w)) := hoare_frame base (heapLocal_free l) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
           state:"l other : Loc\nv w : Val\nbase : Hoare (l ↦ v) (Cmd.free l) emp\nframed : Hoare (l ↦ v ∗ other ↦ w) (Cmd.free l) (emp ∗ other ↦ w)\n⊢ Hoare (l ↦ v ∗ other ↦ w) (Cmd.free l) (other ↦ w)",
           h:"<code>framed</code> and the goal now agree on the precondition and the command and differ in one place. Reading those two lines against each other is how you know that what remains is a consequence step and which side of it is doing the work."},
          {tac:'exact hoare_consequence (entails_refl _) framed (star_emp_left _)',
           state:"No goals.",
           h:"Two entailments and a triple. The precondition entailment is the identity, which is what makes the shape recognisable: whenever you see <code>entails_refl</code> in the first slot, the whole step is about the postcondition."}
        ],
        done:'No goals.'},
       {t:'p', h:"Both <code>have</code>s can be inlined and the proof still compiles as one term. What is lost is the display above: without <code>framed</code> written out, the mismatch that motivates the last line never appears in the goal window, and the reader has to work out from the error message what the postcondition was."}
     ],
     pitfall:"Trying to finish with <code>hoare_frame</code> alone. The error is exact and easy to read once you expect it, and it names the postcondition the frame rule actually produced:<br><br><code>Type mismatch<br>&nbsp;&nbsp;hoare_frame base (heapLocal_free l) (preserves_of_heapOnly (Cmd.free l) (heapOnly_pointsTo other w))<br>has type<br>&nbsp;&nbsp;Hoare (l ↦ v ∗ other ↦ w) (Cmd.free l) (emp ∗ other ↦ w)<br>but is expected to have type<br>&nbsp;&nbsp;Hoare (l ↦ v ∗ other ↦ w) (Cmd.free l) (other ↦ w)</code><br><br>Note where the <code>_</code> went: Lean has filled it in as <code>Cmd.free l</code> in the report, which is a useful check that <code>preserves_of_heapOnly</code>&rsquo;s first argument is the command.",
     variants:"Reach for <code>star_emp_right</code> instead and the mismatch is immediate:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;star_emp_right ?m.18<br>has type<br>&nbsp;&nbsp;?m.18 ∗ emp ⊢ ?m.18<br>but is expected to have type<br>&nbsp;&nbsp;emp ∗ other ↦ w ⊢ other ↦ w</code><br><br>The metavariable is there because nothing has fixed the assertion yet: the <code>_</code> would have been solved <i>by</i> the slot, and the slot rejects the shape first. Which unit law you need is decided by where <code>hoare_free</code> put the <code>emp</code>, and it is on the left because the frame rule appends the frame on the right. Reverse the frame rule&rsquo;s conclusion to <code>R ∗ Q</code> and <code>star_emp_right</code> becomes the one that fits — at the cost, inside the rule&rsquo;s own proof, of two appeals to <code>union_comm</code> and two to <code>disjoint_symm</code>, and of a <code>star_comm</code> at every application whose cells are already in the right order.<br><br>Put the two entailments in the wrong slots — <code>hoare_consequence (star_emp_left _) framed (entails_refl _)</code> — and the report is worth reading, because it shows what <code>hoare_consequence</code> expects on the left:<br><br><code>&nbsp;&nbsp;star_emp_left ?m.17<br>has type<br>&nbsp;&nbsp;emp ∗ ?m.17 ⊢ ?m.17<br>but is expected to have type<br>&nbsp;&nbsp;l ↦ v ∗ other ↦ w ⊢ ?m.12</code><br><br>The first slot is an entailment <i>into</i> the triple&rsquo;s precondition, so its right-hand side is still open while its left-hand side is pinned by the goal — the opposite of the third slot, where the left is pinned and the right is open.<br><br>Replace <code>other ↦ w</code> throughout by an arbitrary <code>R</code> with <code>(hR : HeapOnly R)</code> and the proof is character for character the same, with <code>hR</code> in place of <code>heapOnly_pointsTo other w</code> — the deallocation counterpart of <code>write_with_frame_any</code>, one section up. If instead you drop the consequence step and change the <i>statement</i> to end in <code>emp ∗ (other ↦ w)</code>, the exercise becomes <code>write_with_frame</code> with a different rule and the unit law is never spent; Unit 29 shows what happens to a four-command proof when the <code>emp</code>s are left standing."
    },

    {t:'sec', s:'Where the rule stops'},

    {t:'p', h:"Of the two side conditions, <code>Preserves</code> is the cheap one. <code>Preserves c R</code> is discharged for free whenever <code>R</code> does not mention the store, in any language whatever, because <code>preserves_of_heapOnly</code> never inspects the run — it takes <code>R</code> at one store to <code>R</code> at another and the command is an argument it ignores. A frame that does mention the store can fail, and Unit 24&rsquo;s counterexample is exactly that. But no feature of the <i>language</i> can break it: in a language with a hundred commands <code>preserves_of_heapOnly</code> would still be the same one-line term."},

    {t:'p', h:"<code>HeapLocal</code> is where the fragility is, and there are three ways to lose it. A command that can observe memory it does not own — a test for whether an address is mapped, say — breaks the store equation <code>r.store = s&#39;.store</code>: run it on the small heap and it reports one thing, run it on the small heap plus a frame containing that address and it reports another. A command whose effect on memory depends on cells outside its footprint breaks the heap equation in the same way. And a command that <i>chooses</i> an address, rather than being told one, breaks it in a third way: on a bigger heap it must avoid more cells, so it may pick a different address, and then the final heap is not the small final heap with the frame beside it — it is not even the same shape."},

    {t:'note', kind:'warn', title:'Allocation is not in this language, and that is why the rule holds',
     h:"Every command in <code>Cmd</code> takes the addresses it uses as part of its syntax. Add a command that asks memory for a fresh cell and returns its address, and locality fails for the third reason above, so <code>hoare_frame</code> does not apply to it as stated and the theorem on this page says nothing about programs that allocate. Real separation logics recover the rule, and the recovery is not a repair to this proof: it is a change to what a run is allowed to return. Unit 38 takes that apart, along with the generalisation of everything here from heaps to an arbitrary partial commutative monoid — the structure Unit 10 built."},

    {t:'sec', s:'Three questions'},

    {t:'p', h:"You should be able to answer these without opening anything. The folds have the answers."},

    {t:'detail', title:'Which side condition failed in the store counterexample, and which in the heap one?', tag:'aside', blocks:[
      {t:'p', h:"The store counterexample is Unit 24&rsquo;s <code>frame_needs_preserves</code>: the triple <code>{x = 0} x := 1 {x = 1}</code> holds, and framing it with the assertion <code>x = 0</code> gives a triple that does not. The command is <code>.assign x (.const 1)</code>, which is local — <code>heapLocal_assign</code> proves it — so the hypothesis that fails is <code>Preserves</code>. The frame is a store fact and the command changes the store."},
      {t:'p', h:"The heap-side failure is Unit 25&rsquo;s, and it refutes no command: every command in the language satisfies <code>HeapLocal</code>. What it refutes is a <i>definition</i>. Delete the premise <code>Heap.disjoint h hFrame</code> and keep the rest, and the condition that remains is false for <code>free</code>, with a frame that owns the cell being freed. So the two counterexamples do different jobs: one shows a rule needs a hypothesis, the other shows a definition needs a premise."},
      {t:'p', h:"Only the first of them refutes the frame rule. Drop <code>Preserves</code> and Unit 24&rsquo;s theorem is a witness against what is left:"},
      {t:'code', tag:'illustration',
       cap:"The frame rule without <code>Preserves</code>, refuted from Unit 24&rsquo;s theorem in three lines. <code>heapLocal_assign</code> supplies the locality, so the only hypothesis missing from the quantified statement is the one that fails.",
       src:"theorem frame_without_preserves_is_false :\n    ¬ ∀ (P Q R : Assertion) (c : Cmd), Hoare P c Q → HeapLocal c → Hoare (P ∗ R) c (Q ∗ R) := by\n  intro hall\n  exact (frame_needs_preserves 0).2\n    (hall _ _ _ _ (frame_needs_preserves 0).1 (heapLocal_assign 0 (.const 1)))"},
      {t:'p', h:"There is no matching refutation for the other hypothesis, and there cannot be one here. Drop <code>HeapLocal</code> and the weakened rule is still <i>true</i> of this language, because every command in it is local; what is lost is the proof, since nothing left in scope produces a run on the big heap. That hypothesis earns its place not against the commands this language has but against the ones another language might add — the three listed under <i>Where the rule stops</i>."}
    ]},

    {t:'detail', title:'Why does HeapLocal carry a disjointness conjunct in its conclusion?', tag:'aside', blocks:[
      {t:'p', h:"Because the postcondition is a star, and a star&rsquo;s third slot is a disjointness proof about the two heaps you cut the final heap into. Those two heaps are <code>s&#39;.heap</code> and <code>hR</code>, so the slot wants <code>Heap.disjoint s&#39;.heap hR</code> — a statement about the heap the command <i>ended</i> on, which the initial disjointness does not give you and no lemma about <code>Heap.union</code> supplies. Something has to produce it, and the only thing that knows what the command did is the locality hypothesis. That is why Unit 24 could not close the proof without adding it, and why the added conjunct is about <code>s&#39;.heap</code> rather than about <code>h</code>."},
      {t:'p', h:"The four-component version is a true statement about every command in this language, and it is useless: nothing that consumes it can build a star. The conjunct also pays for itself a second time, in Unit 26 — to run <code>c₂</code> on the big heap at all, the sequencing proof must know the middle heap is disjoint from the frame."}
    ]},

    {t:'detail', title:'Give a command for which HeapLocal is false.', tag:'aside', blocks:[
      {t:'p', h:"There is none. Every constructor of <code>Cmd</code> is local — that is what Units 24 to 26 establish, and there are only eight of them. Any answer to this question is a command the language does not have, and the shortest one is Unit 24&rsquo;s: <code>x := allocated?(l)</code>, which sets <code>x</code> to 1 if <code>l</code> is mapped and 0 otherwise. Run it on a heap where <code>l</code> is unmapped and it sets <code>x</code> to 0; run it on that heap plus a frame that owns <code>l</code> — a legitimate frame, disjoint from the small heap — and it sets <code>x</code> to 1. The equation <code>r.store = s&#39;.store</code> is false, and it is the only clause that fails: the heaps agree."},
      {t:'p', h:"That is the shape of the answer to &ldquo;is this logic sound for my language&rdquo;. It is not a question about the proof on this page, which is eight lines and quantifies over commands. It is a question about whether each command you add can be proved local, one at a time, and the cost of adding one is exactly one such proof."}
    ]},

    {t:'dod', h:"You can state the frame rule, prove it, and say which of its eight lines does which of the five things the informal argument does. You can name the single decision in the proof — the cut of the final heap — and say what the other cut leaves you holding. You can say why <code>HeapLocal</code>&rsquo;s conclusion is oriented the way it is, and price the alternative. You can list what the proof does not use, and check the list by reproving the theorem about an arbitrary relation on states. You can specify a two-cell program in a four-line proof in which the word <code>Heap</code> does not occur, replace its frame by an arbitrary heap-only assertion without touching that proof, and say where the disequality between the two addresses lives. And you can name the three ways a new command could fail to be local, and the one that a language with allocation takes."},

    {t:'p', h:"The rule is proved. There is one debt outstanding, issued on the first page: the statement we could not write down then, and can now."}

  ]
});
