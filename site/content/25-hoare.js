registerChapter({
  id: 'hoare',
  num: '22',
  phase: 'Phase 4 · The program logic',
  title: 'Hoare triples',
  blurb: 'One definition joins the two halves of the course: a precondition, a command, a postcondition. Then the three rules that let you stop unfolding the semantics.',

  orient: {
    youWill: [
      'Read <code>Hoare P c Q</code> and name the three separate claims its single <code>∃ s\'</code> is making.',
      'Say why the implication you would write first is satisfied by a program that always faults, and exhibit one.',
      'State the difference between total and partial correctness exactly, and say which direction needs which hypothesis.',
      'Prove the rule of consequence, and read its variance off the shape of the definition rather than memorising it.',
      'Run one triple, take the final state it produces, and feed it to the next — and supply the assertion in the middle yourself.',
      'Say why an assertion that is a Lean function makes the assignment rule nearly a definition, and what an assertion that was a piece of syntax would have cost.',
      'Use <code>show</code> to replace a goal that displays as an opaque assertion applied to two projections with the one-line arithmetic it actually is.'
    ],
    needs: [
      'Unit 19: <code>Exec</code>, its ten constructors, and the decision that a fault is the <i>absence</i> of a derivation — <code>exec_load_stuck</code> is used on this page.',
      'Unit 12: <code>Assertion</code>, <code>⊢</code>, and that an entailment is applied to a store, a heap and a proof.',
      'Unit 18: <code>Cmd</code>, <code>State</code> and its two fields, <code>Store.set</code>, <code>Atom.eval</code>, <code>;;</code>.',
      'Units 13 and 17: <code>emp</code>, <code>↦</code>, <code>fact</code>.'
    ],
    payoff: 'Every theorem in the rest of this course is a <code>Hoare</code> triple or a lemma in the service of one. Not one of the four rules proved here mentions memory, which is why none of them runs past four lines — and why the next unit, where the rules do touch memory, is a different kind of problem.'
  },

  blocks: [

    /* ================================================ the first attempt === */

    {t:'p', h:'So write one down: a statement that mentions a command and an assertion in the same breath. It has to carry three things: the states the program may be started in, the command, and what holds when it stops. The first and third are assertions, the second is a <code>Cmd</code>, and the object you get is a three-place relation between them.'},

    {t:'p', h:'Here is the sentence you would write first. <i>If <code>P</code> holds of the initial store and heap, and running <code>c</code> from there reaches <code>s\'</code>, then <code>Q</code> holds of <code>s\'</code>.</i> Every word of it is already available.'},

    {t:'code', cap:'The first definition, and it is in the corpus under this name. The name gives away where this is going; the next four blocks are why it is called that.',
     src:"def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap"},

    {t:'p', h:'Three arguments and two arrows. <code>∀ σ h s\'</code> fixes an initial store, an initial heap and a candidate final state. <code>P σ h</code> says the precondition holds at the start. <code>Exec c ⟨σ, h⟩ s\'</code> is a derivation that the run gets from one to the other. The conclusion applies <code>Q</code> to <code>s\'.store</code> and <code>s\'.heap</code> rather than to <code>s\'</code>, because an <code>Assertion</code> takes a store and a heap as two arguments and a <code>State</code> is a structure holding one of each.'},

    {t:'p', h:'Now put that shape next to Unit 19\'s decision about faults. There is no rule of <code>Exec</code> whose conclusion is a run of <code>.load x l</code> from a heap in which <code>l</code> is unallocated. So for such a command <i>no</i> final state is related to the initial one, the second arrow never gets a premise, and the implication holds no matter what <code>Q</code> says.'},

    {t:'code', tag:'illustration', cap:'Compiled. Reading from the empty heap establishes falsity, for every variable and every address.',
     src:"example (x : Var) (l : Loc) : PartialHoare emp (.load x l) aFalse := by\n  intro σ h s' hp hex\n  subst hp\n  exact absurd hex (exec_load_stuck x l σ s')"},

    {t:'p', h:'Nothing in that proof is a trick. <code>emp</code> forces the heap to be <code>Heap.empty</code>, <code>subst</code> replaces it, and <code>exec_load_stuck</code> says the derivation cannot exist. The premise is impossible, so the conclusion is free. What is wrong is not the proof but the expectation: the statement was supposed to be about a program working.'},

    {t:'p', h:'Name it rather than repair it. What <code>PartialHoare</code> defines is <b>partial correctness</b>: <i>if</i> the command stops, and stops without going wrong, the postcondition holds. It is the right notion for a language in which the only way to fail is to run forever, and you have agreed to ignore that. Here the way to fail is to touch memory you do not own, which is the entire subject.'},

    /* ==================================================== the repair ====== */

    {t:'sec', s:'Demanding the run'},

    {t:'p', h:'Stop quantifying over final states and claim one instead.'},

    {t:'code', cap:'The definition the rest of the course is about.',
     src:"def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap"},

    {t:'anat', src:"def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap",
     parts:[
       {m:'∀ σ h', h:'A store and a heap, not a <code>State</code>; the state is assembled once, inside, as <code>⟨σ, h⟩</code>. Everything to the right of the arrow is a claim about the run that starts there.'},
       {m:'P σ h →', h:'The precondition is a hypothesis, so a triple says nothing at all about states where <code>P</code> fails. This is where ownership enters: a precondition of <code>l ↦ v</code> restricts the claim to heaps that are exactly that one cell, and a triple proved under it is silent about every other heap.'},
       {m:"∃ s'", h:'The one change from the first attempt, and the whole of it. The first version quantified over candidate final states and never claimed there was one; this version produces a state, so proving a triple means building a run rather than taking one apart.'},
       {m:"Exec c ⟨σ, h⟩ s'", h:'A derivation, in the sense of Unit 19: a finite tree built from the ten rules. Producing one is the obligation; the shape of the tree is what the proofs below construct by hand.'},
       {m:"Q s'.store s'.heap", h:'The postcondition, at the state the derivation reached — and the source of most of the display noise on this page. <code>s\'</code> is usually a state you have built by hand, and its two projections sit there unreduced until something asks them to reduce.'}
     ]},

    {t:'note', kind:'key', title:'One existential, three claims',
     h:'<code>∃ s\', Exec c ⟨σ, h⟩ s\' ∧ Q s\'.store s\'.heap</code> asserts all of the following, and every later proof has to discharge all three. <b>(1) No memory fault.</b> A derivation exists, and Unit 19 arranged that no derivation exists for a command that reads, writes or frees an address it does not hold. <b>(2) Termination.</b> A derivation is a finite tree; a run that never stops has no final state and therefore no tree. <b>(3) The postcondition.</b> <code>Q</code> holds at the state reached. Because all three are the same existential, none of them can be dropped by accident.'},

    {t:'p', h:'The same faulting program, against the new definition, is now refutable rather than provable.'},

    {t:'code', tag:'illustration', cap:'Compiled. <code>obtain</code> takes the existential apart and the derivation it produces is the impossible one.',
     src:"example (x : Var) (l : Loc) : ¬ Hoare emp (.load x l) aTrue := by\n  intro hc\n  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty rfl\n  exact absurd hex (exec_load_stuck x l (fun _ => 0) s')"},

    {t:'p', h:'That refutation is the whole content of the change, and the postcondition is where to look for it. <code>aTrue</code> is satisfied by every state, so nothing whatever is being asked of the answer — and the triple is still false, because safety and termination live in the quantifier and not in <code>Q</code>.'},

    {t:'cmp',
     left:{t:'Total correctness — <code>Hoare</code>', kind:'good',
       h:'<i>From every state satisfying <code>P</code>, the command reaches some final state, and <code>Q</code> holds there.</i> Proving one means <b>building</b> a derivation: you name the final state and you name the rule. Refuting one means showing no derivation exists.',
       src:"∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap"},
     right:{t:'Partial correctness — <code>PartialHoare</code>',
       h:'<i>Any final state the command reaches from a state satisfying <code>P</code> satisfies <code>Q</code>.</i> Proving one means <b>inverting</b> a derivation you are handed. A command that cannot reach any final state satisfies every such claim.',
       src:"∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap"}},

    {t:'p', h:'The two are not in competition and neither implies the other for free. To get from <code>Hoare P c Q</code> to <code>PartialHoare P c Q</code> you have to know that the state the existential produces is the <i>only</i> state the command can reach, which is <code>exec_deterministic</code> from Unit 20 and is where that theorem is finally spent. In the other direction there is nothing to spend: partial correctness says nothing about whether a run exists at all, and the load above is the counterexample. So the two differ exactly where a program can fail to produce a final state — by faulting, or by looping.'},

    {t:'p', h:'Every specification in the next six units carries a precondition that owns the cells its command touches, which closes off faulting. Loops are what is left over, and no rule in this course mentions one before Unit 36. So <code>PartialHoare</code> is defined here, beside the definition it is a foil for, and the first proof that uses it is in Unit 35 — where the two readings are set side by side and the implication between them is proved.'},

    {t:'detail', title:'A third candidate: say safety and partial correctness separately', open:false, blocks:[
      {t:'p', h:'Since the existential is doing two jobs, it is fair to ask whether they should be written as two conjuncts: the command is safe here, <i>and</i> whatever it reaches satisfies <code>Q</code>.'},
      {t:'code', tag:'illustration', cap:'The split version, compiled together with both implications below.',
       src:"def SafeAndPartial (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → (∃ s', Exec c ⟨σ, h⟩ s') ∧ (∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap)"},
      {t:'code', tag:'illustration', cap:'Both directions hold. The first is three lines and uses nothing; the second needs determinism, and that asymmetry is the reason to prefer the shorter definition.',
       src:"example (P : Assertion) (c : Cmd) (Q : Assertion) (hc : SafeAndPartial P c Q) : Hoare P c Q := by\n  intro σ h hp\n  obtain ⟨⟨s', hex⟩, hall⟩ := hc σ h hp\n  exact ⟨s', hex, hall s' hex⟩\n\nexample (P : Assertion) (c : Cmd) (Q : Assertion) (hc : Hoare P c Q) : SafeAndPartial P c Q := by\n  intro σ h hp\n  obtain ⟨s', hex, hq⟩ := hc σ h hp\n  refine ⟨⟨s', hex⟩, ?_⟩\n  intro s'' hex''\n  have := exec_deterministic hex hex''\n  exact this ▸ hq"},
      {t:'p', h:'So the split definition says the same thing about this language, and costs a universally quantified conjunct in every proof that ever consumes a triple. The one-existential form gives the consumer a state and a proof about it in one <code>obtain</code>. That is the trade, and it is the reason the definition is the short one — not that the split is wrong.'}
    ]},

    /* ================================================== consequence ======= */

    {t:'sec', s:'The rule that never looks at the command'},

    {t:'p', h:'Two of the three slots can be changed without knowing anything about <code>c</code>. Hand a triple a <i>stronger</i> precondition and it survives: fewer initial states means fewer obligations. Hand it a <i>weaker</i> postcondition and it survives too: you proved more than was asked. The two directions are opposite.'},

    {t:'p', h:'Unfolded, <code>Hoare P c Q</code> is a function. Give it a store, a heap and a proof of <code>P</code> there, and it gives back a final state together with a proof of <code>Q</code>. So <code>P</code> stands in an argument position and <code>Q</code> stands in a result position — and to build a function <code>P\' → Q\'</code> out of a function <code>P → Q</code> you compose on the left with <code>P\' → P</code> and on the right with <code>Q → Q\'</code>. The rule of consequence is that composition with a run of the program in the middle. Contravariant in the precondition, covariant in the postcondition, for the same reason a function type is.'},

    {t:'txt', cap:'The rule as it is usually drawn. Three premises above the line, one conclusion below; the command is untouched and unexamined.',
     src:"  P' ⊢ P        { P } c { Q }        Q ⊢ Q'\n  ─────────────────────────────────────────────\n                 { P' } c { Q' }"},

    {t:'note', kind:'warn', title:'The brackets you cannot have',
     h:'Those braces are the notation everyone uses, and Lean has a spare bracket pair, <code>⦃ ⦄</code>, that looks made for the job. It will not carry a command. Put the command slot at maximum precedence and the slot accepts an atom and nothing more, so a single <code>assign</code> — which is an application — is already refused. Lower the slot far enough to admit an application and the parse no longer stops at the closing bracket, because a <code>⦃</code> following a command is exactly how the notation you are defining begins, so the parser reads on and falls off the end of the line. The one spelling that works puts the command in ordinary parentheses, which is two bracket pairs to save one. So this course writes <code>Hoare P c Q</code>, and the round brackets around the slots in the theorems on this page, as in <code>Hoare (P) (c) (Q)</code>, are punctuation for the eye. One pair is not decoration: in <code>Hoare (P) ((c₁ ;; c₂)) (R)</code> the inner pair is required, because application binds tighter than <code>;;</code>.'},

    {t:'ex',
     id: 'm6-1',
     name: 'hoare_consequence',
     hard: false,
     why: 'This is the join between Module 3 and everything after it. Every entailment proved about <code>∗</code> becomes usable here, and only here — an entailment on its own says nothing about any program, and this rule is the one place a triple will accept one. It is cited six times in the verified Lean after this unit — once in Unit 27 and five times in Unit 29 — and every one of the six supplies <code>entails_refl _</code> for the precondition, so what is being changed is always the postcondition, most often by <code>star_comm</code> or <code>star_emp_left</code>. That is what &ldquo;Module 3 becomes usable here&rdquo; looks like in the Lean.',
     setup: 'Everything is in scope: <code>Hoare</code>, <code>Entails</code> and its notation <code>⊢</code>. Three tactics are enough, and the command never appears in the proof.',
     goal: "theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare (P) (c) (Q)) (hpost : Q ⊢ Q') : Hoare (P') (c) (Q') := by",
     hints: [
       'The goal is <code>Hoare P\' c Q\'</code>. Unfolded: for every store <code>σ</code> and heap <code>h</code> at which <code>P\'</code> holds, there is a state <code>s\'</code> such that <code>c</code> runs from <code>⟨σ, h⟩</code> to <code>s\'</code> and <code>Q\'</code> holds at <code>s\'</code>. You are handed the same claim with <code>P</code> and <code>Q</code> in place of <code>P\'</code> and <code>Q\'</code>, plus one entailment on each side.',
       'Take a store and a heap satisfying <code>P\'</code>. Push them through <code>hpre</code> and you have <code>P</code> there. Feed that to <code>hc</code>, which hands back a final state and a proof of <code>Q</code> at it. Push that through <code>hpost</code>. Nothing else happens; in particular the final state you return is the one <code>hc</code> chose, unchanged.',
       'You need <code>intro</code> to get at the store, the heap and the premise; <code>obtain</code> to take apart what <code>hc</code> gives you; and an anonymous constructor to build the answer. An entailment takes three arguments — a store, a heap, and a proof of its left-hand side.',
       'The first line is <code>intro σ h hp</code>. It leaves <code>hp : P\' σ h</code> in the context and the goal <code>⊢ ∃ s\', Exec c { store := σ, heap := h } s\' ∧ Q\' s\'.store s\'.heap</code>. The second line applies <code>hc</code> at <code>σ</code>, at <code>h</code>, and at <code>hpre σ h hp</code>.'
     ],
     sol: "theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare (P) (c) (Q)) (hpost : Q ⊢ Q') : Hoare (P') (c) (Q') := by\n  intro σ h hp\n  obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)\n  exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
     solNote: 'Three lines, and the command appears in exactly one of them, as a variable being carried from the hypothesis to the goal. If you climbed all four hints and are still stuck, open this without hesitation — the value here is the shape, and the shape is worth more than the struggle.',
     expl: 'The proof is composition. <code>hpre σ h hp</code> converts the premise you have into the premise <code>hc</code> wants; <code>hc</code> converts that into a state and a proof of <code>Q</code>; <code>hpost s\'.store s\'.heap hq</code> converts that proof into a proof of <code>Q\'</code>. The middle component, the derivation <code>hex</code>, travels from the <code>obtain</code> to the <code>exact</code> without being looked at, which is what "the rule never inspects the command" means concretely.',
     walk: [
       {tac:'intro σ h hp', h:'Three binders come off at once: two from the <code>∀</code> and one from the arrow, exactly as they do for an entailment. The goal is now the existential, at this particular store and heap.'},
       {tac:"obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)", h:'<code>hpre σ h hp : P σ h</code> is built and consumed in the same expression. <code>hc</code> applied to three arguments is a proof of the existential for <code>P</code> and <code>Q</code>, and <code>obtain</code> splits it into a witness and two components — three names for what is written as one nested pair, by the flattening of <code>⟨…⟩</code>.'},
       {tac:"exact ⟨s', hex, hpost s'.store s'.heap hq⟩", h:'The witness is reused unchanged, the derivation is reused unchanged, and only the third slot does any work: <code>hpost</code> is applied at the <i>final</i> state, not the initial one, because that is where <code>hq</code> lives.'}
     ],
     deep: [
       {t:'p', h:'Every goal state in this unit came out of Lean, mid-proof ones from <code>trace_state</code>, with the <code>file:line:column</code> prefix dropped. Where a state below shows fewer hypotheses than Lean printed, the ones left out are unchanged from the state above it and the step says so.'},
       {t:'trace', title:'hoare_consequence, three tactics',
        start:"P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\n⊢ Hoare P' c Q'",
        steps:[
          {tac:'intro σ h hp',
           state:"σ : Store\nh : Heap\nhp : P' σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q' s'.store s'.heap",
           h:'The five hypotheses above are unchanged and are not repeated here. Two things to see in the goal: <code>Hoare</code> unfolded without being asked, because <code>intro</code> looks through a definition to find a binder; and <code>⟨σ, h⟩</code> printed as <code>{ store := σ, heap := h }</code>, which is the same term in the notation Lean prefers for output.'},
          {tac:"obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)",
           state:"s' : State\nhex : Exec c { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q' s'.store s'.heap",
           h:'The goal has not moved. Three new hypotheses arrived, and the only difference between <code>hq</code> and what the goal wants is <code>Q</code> against <code>Q\'</code> — which is what the third premise is for.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The goal being unchanged across the second step is the point of the rule. Consequence does not advance the proof of the program; it changes the assertions on either side of a proof that is already finished.'}
     ],
     pitfall: 'Applying <code>hpost</code> at the wrong state. Writing <code>hpost σ h hq</code> instead of <code>hpost s\'.store s\'.heap hq</code> looks harmless — the store and the heap are right there — and Lean reports <code>Application type mismatch: The argument</code> <code>hq</code> <code>has type</code> <code>Q s\'.store s\'.heap</code> <code>but is expected to have type</code> <code>Q σ h</code>. The postcondition is a claim about the state you finished in, and an entailment has to be instantiated there. The sibling mistake is <code>hpre hp</code>, dropping the store and the heap; that one is reported against the <i>first</i> argument, saying <code>hp</code> has a type of sort <code>Prop</code> where a <code>Store</code> was expected.',
     variants: 'Reverse either entailment and the theorem is false. Take <code>P\' := aTrue</code>, <code>P := emp</code>, <code>c := .skip</code> and <code>Q = Q\' := emp</code>: the reversed premise <code>emp ⊢ aTrue</code> holds, the middle premise <code>Hoare emp .skip emp</code> holds because <code>skip</code> changes nothing, and the conclusion <code>Hoare aTrue .skip emp</code> is false. One cell refutes it. Apply the conclusion at any store and at <code>Heap.singleton 0 0</code>, which satisfies <code>aTrue</code>; <code>exec_deterministic hex Exec.skip</code> then pins the final state to the initial one, and what the postcondition is left claiming is <code>Heap.singleton 0 0 = Heap.empty</code>, refuted at address <code>0</code> by <code>singleton_same</code>. The postcondition side fails at the same heap with <code>Q := aTrue</code> and <code>Q\' := emp</code>, and the failure is in the same place: <code>skip</code> hands back the heap it was given, so no rule can make it empty. Dropping <code>hpre</code> altogether and keeping only <code>hpost</code> gives a weaker rule that is still true, and is exactly what supplying <code>entails_refl P</code> for the missing premise gives you — which is how all six of its later uses are written.'
    },

    {t:'p', h:'Nothing in that proof knew what an assertion was. That is what makes the rule the connection to Module 3: the entailments it consumes may be arbitrarily hard theorems about <code>∗</code>, and this rule accepts them without a word.'},

    {t:'code', tag:'illustration', cap:'Compiled. <code>star_comm</code> is Unit 15\'s theorem that <code>∗</code> is commutative, and it enters a statement about programs through the third premise of the rule. The command and its triple are hypotheses, because the rule does not care which they are; the first premise is the identity entailment, because the precondition needs no change.',
     src:"example (P Q : Assertion) (c : Cmd) (hc : Hoare (P ∗ Q) (c) (P ∗ Q)) :\n    Hoare (P ∗ Q) (c) (Q ∗ P) :=\n  hoare_consequence (entails_refl (P ∗ Q)) hc (star_comm P Q)"},

    /* ==================================================== skip and seq ==== */

    {t:'sec', s:'Two commands, two rules'},

    {t:'p', h:'<code>skip</code> changes nothing, so any assertion is its own postcondition. Reading the definition: given <code>σ</code>, <code>h</code> and a proof of <code>P σ h</code>, produce a final state — take <code>⟨σ, h⟩</code> — a derivation — take <code>Exec.skip</code> — and a proof of <code>P</code> there — take the proof you were handed. All three components are to hand, so the proof is a term with no tactic in it.'},

    {t:'p', h:'Sequencing is the first rule that has to run a program. If <code>c₁</code> takes you from <code>P</code> to <code>Q</code> and <code>c₂</code> takes you from <code>Q</code> to <code>R</code>, then <code>c₁ ;; c₂</code> takes you from <code>P</code> to <code>R</code>. The proof has to obtain a state from the first triple and hand it to the second, and then join the two derivations with <code>Exec.seq</code> — the constructor whose premises are exactly two runs meeting at a middle state.'},

    {t:'p', h:'The assertion <code>Q</code> in the middle is not determined by the statement being proved. It appears in both hypotheses and in neither the precondition nor the postcondition of the conclusion. In the theorem below that costs nothing, because <code>Q</code> is a variable and Lean is handed both hypotheses. It costs something the moment you want to <i>use</i> the rule on a concrete program, and that is the last exercise on this page.'},

    {t:'ex',
     id: 'm6-2',
     name: 'hoare_skip / hoare_seq',
     hard: false,
     why: 'Two proofs whose difference is the lesson. The first has nothing to discover and is written as a term; the second has to take a triple apart and rebuild one, and is written as a script. Every structural rule in the rest of the course is one shape or the other. <code>hoare_seq</code> is cited four times later: once in Unit 23, as a term whose two arguments are fully applied so that the middle assertion falls out of them, and three times in Unit 29, where two of the three have to supply it by hand — which is the last exercise on this page. <code>hoare_skip</code> is cited nowhere: it is here because the definition has to be exercised on the command that does nothing before it is exercised on one that does something.',
     setup: 'Prove both. <code>Exec.skip</code> and <code>Exec.seq</code> are the two constructors you need; <code>Exec.seq</code> takes a run of <code>c₁</code> and a run of <code>c₂</code> that begins where the first ended.',
     goal: "theorem hoare_skip (P : Assertion) : Hoare (P) (.skip) (P) :=\n  sorry\n\ntheorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by",
     hints: [
       'For <code>hoare_skip</code>: you must produce, from a store, a heap and a proof of <code>P</code> there, a state, a derivation, and a proof of <code>P</code> at that state. For <code>hoare_seq</code>: from a store, a heap and a proof of <code>P</code>, produce a final state of the whole sequence, a derivation for the whole sequence, and a proof of <code>R</code> at it. You are given both component triples.',
       'For <code>skip</code>, all three components are things you already hold: the state you started in, the rule that says <code>skip</code> goes from a state to itself, and the premise. For the sequence, run the first triple to get a middle state and a proof of <code>Q</code> there; run the second triple <i>starting from that middle state</i> to get a final state and a proof of <code>R</code>; join the two derivations.',
       '<code>hoare_skip</code> needs no tactics: write <code>fun σ h hp => …</code> and fill three slots with <code>⟨…⟩</code>, using <code>Exec.skip</code>. <code>hoare_seq</code> needs <code>intro</code>, two <code>obtain</code>s and one <code>exact</code>, with <code>Exec.seq</code> in the middle slot. The second triple is applied to a store and a heap, so give it the two <i>fields</i> of the middle state.',
       'For <code>hoare_skip</code> the whole proof is <code>fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩</code> — an outer three-slot bracket whose first slot is itself a two-slot bracket building the state. For <code>hoare_seq</code> the first line after <code>intro σ h hp</code> is <code>obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp</code>, which leaves the goal untouched and puts a middle state in the context.'
     ],
     sol: "theorem hoare_skip (P : Assertion) : Hoare (P) (.skip) (P) :=\n  fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩\n\ntheorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by\n  intro σ h hp\n  obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp\n  obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq\n  exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩",
     solNote: 'The first proof has no <code>by</code> in it because there is nothing to search for: the three components are named in the hypotheses and in the constructor list. The second cannot be written that way, because the middle state has to be extracted from a proof before it can be used, and extraction is what <code>obtain</code> does.',
     expl: 'Both proofs build the same three-slot answer; they differ in where the slots come from. In <code>hoare_skip</code> all three are in scope from the start. In <code>hoare_seq</code> the witness comes from the <i>second</i> triple, the derivation is assembled from two pieces, and the postcondition proof comes from the second triple as well — so nothing can be written down until both triples have been run, in order.',
     walk: [
       {tac:"fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩", h:'A lambda of three arguments, because <code>Hoare</code> is two <code>∀</code>s and an arrow. The body is a three-slot anonymous constructor: the state, the derivation, the postcondition proof. The inner <code>⟨σ, h⟩</code> builds a <code>State</code> from its two fields, and <code>Exec.skip</code> is the whole derivation because its conclusion has the same state on both sides.'},
       {tac:'intro σ h hp', h:'The tactic-mode version of the same three binders, for the sequence rule. The goal becomes the existential at this store and heap.'},
       {tac:"obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp", h:'Runs the first triple. The goal does not change; what changes is that a middle state <code>s₁</code>, a derivation into it, and a proof of <code>Q</code> at it are now in the context.'},
       {tac:"obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq", h:'Runs the second triple, starting from the middle state — which has to be given as its two fields, because a triple takes a store and a heap. This produces the final state of the whole sequence.'},
       {tac:"exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩", h:'The answer. <code>Exec.seq</code> wants a run of <code>c₁</code> ending where the run of <code>c₂</code> begins; <code>hex₁</code> ends at <code>s₁</code> and <code>hex₂</code> begins at <code>⟨s₁.store, s₁.heap⟩</code>. Those are the same state, and Lean accepts them as the same term without a rewrite, by the structure eta rule of Unit 18.'}
     ],
     deep: [
       {t:'trace', title:'hoare_seq, after the two obtains',
        start:"P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\n⊢ Hoare P (c₁ ;; c₂) R",
        steps:[
          {tac:'intro σ h hp',
           state:"σ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
           h:'The four hypotheses above are unchanged and are not repeated. The goal names the compound command; nothing has decomposed it, and nothing will — <code>Exec.seq</code> is applied at the end, not analysed at the start.'},
          {tac:"obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp",
           state:"s₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\nhq : Q s₁.store s₁.heap\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
           h:'Three new hypotheses, goal untouched. <code>s₁</code> is the middle state, and it exists only because the first triple was a total one: a partial-correctness hypothesis would have given nothing here.'},
          {tac:"obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq",
           state:"s₂ : State\nhex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂\nhr : R s₂.store s₂.heap\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
           h:'Look at <code>hex₂</code>\'s initial state: <code>{ store := s₁.store, heap := s₁.heap }</code>, not <code>s₁</code>. It was rebuilt out of the two arguments the triple was applied to. Structure eta is what makes it the same term as <code>s₁</code>, which is why the final line typechecks with no rewriting.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Six of those nine new hypotheses are discarded in the last line — every one but <code>s₂</code>, <code>hex₁</code>, <code>hex₂</code> and <code>hr</code>. That is normal for a rule that runs one thing and then another: the middle state is scaffolding, and the statement being proved never mentions it.'},
       {t:'p', h:'The second <code>obtain</code> is where the choice made on the first page of this unit is spent. It produces a middle state because <code>h₁</code> promises one; a partial-correctness hypothesis promises nothing, and the rule stated with one in that position is not a weaker true rule — it is a false one.'},
       {t:'code', tag:'illustration', cap:'Compiled. Sequencing with its first hypothesis weakened to partial correctness, refuted in six lines. <code>PartialHoare emp (.load 0 0) aTrue</code> is discharged by a function that ignores all five of its arguments — the derivation it demands can never be supplied — so the weakened rule would hand back a run of a command that cannot run.',
        src:"example :\n    ¬ ∀ (P Q R : Assertion) (c₁ c₂ : Cmd),\n        PartialHoare P c₁ Q → Hoare Q c₂ R → Hoare P (c₁ ;; c₂) R := by\n  intro hrule\n  have hbad : Hoare emp (.load 0 0 ;; .skip) aTrue :=\n    hrule emp aTrue aTrue (.load 0 0) .skip (fun _ _ _ _ _ => True.intro) (hoare_skip aTrue)\n  obtain ⟨s', hex, _⟩ := hbad (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | seq h₁ _ => exact absurd h₁ (exec_load_stuck 0 0 (fun _ => 0) _)"}
     ],
     pitfall: 'Applying the second triple to the middle state itself: <code>h₂ s₁ hq</code>. Lean answers <code>Application type mismatch: The argument</code> <code>s₁</code> <code>has type</code> <code>State</code> <code>but is expected to have type</code> <code>Store</code>. A triple is a statement about a store and a heap, in that order, and a <code>State</code> is not either of them; the two fields have to be projected out by hand. It is a mistake the surrounding text encourages: the goal, the hypothesis and the constructor all speak in <code>State</code>s, and only the definition of <code>Hoare</code> speaks in pairs.',
     variants: 'Swap the two derivations in the last line — <code>Exec.seq hex₂ hex₁</code> — and Lean reports a mismatch on the <i>first</i> argument, saying <code>hex₂</code> has type <code>Exec c₂ { store := s₁.store, heap := s₁.heap } s₂</code> where <code>Exec c₁ { store := σ, heap := h } ?m.47</code> was expected: the first premise of <code>Exec.seq</code> is pinned to the initial state by the goal, and the metavariable in the middle position is the middle state Lean is still willing to choose. Weaken either hypothesis to a <code>PartialHoare</code> and what you get is not an unprovable rule but a false one, and the two weakenings break at different lines. With <code>h₁</code> partial there is no middle state to <code>obtain</code>, so the proof stops at line two; the counterexample above is a faulting <code>load</code> in <code>c₁</code>, which satisfies partial correctness vacuously. With <code>h₂</code> partial the middle state still arrives and the proof stops at line three, holding a derivation for <code>c₁</code> and, for <code>c₂</code>, an implication whose premise is the derivation it was trying to build; the same three assertions refute it with the <code>load</code> moved into <code>c₂</code>. Both failures are the same fact from two sides: partial correctness never produces a run, and <code>Exec.seq</code> needs two.'
    },

    /* ================================================= assignment ========= */

    {t:'sec', s:'Assignment, read backwards'},

    {t:'p', h:'For the first rule about a command that changes something, ask the question in the direction the rule will be used. You want <code>Q</code> to hold after <code>x := e</code>. What has to hold before?'},

    {t:'p', h:'The answer on paper is <code>Q</code> with <code>e</code> written in for <code>x</code>.'},

    {t:'txt', cap:'The assignment axiom, as it is written on paper. It is read from the bottom up: to establish <code>Q</code> afterwards, establish the substituted assertion beforehand.',
     src:"  ────────────────────────────────\n     { Q[e/x] }  x := e  { Q }"},

    {t:'p', h:'Written that way it is a claim about <i>text</i>. <code>Q[e/x]</code> is a syntactic operation on the assertion <code>Q</code>: find the free occurrences of <code>x</code> and replace them. That presupposes assertions are pieces of syntax with free variables in them, which in this course they are not. An <code>Assertion</code> is <code>Store → Heap → Prop</code> — a Lean function. There is nothing to rewrite.'},

    {t:'p', h:'What <code>Q[e/x]</code> is <i>for</i>, however, is available directly. It is the assertion that holds at a store exactly when <code>Q</code> holds at the store you would get by putting the value of <code>e</code> into <code>x</code>. Say that.'},

    {t:'code', cap:'Substitution as an operation on assertions, defined by what it means rather than by what it looks like.',
     src:"def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ h => Q (Store.set σ x (e.eval σ)) h"},

    {t:'anat', src:"def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ h => Q (Store.set σ x (e.eval σ)) h",
     parts:[
       {m:'(x : Var)', h:'A variable of the programming language, which is a <code>Nat</code> — an index into the store. Not a Lean binder, and nothing here can capture it.'},
       {m:'(e : Atom)', h:'A program expression, the same syntax the <code>assign</code> constructor carries. Expressions are syntax; assertions are not, and the asymmetry is the whole design.'},
       {m:'fun σ h =>', h:'The result is an assertion, so it is a function of a store and a heap. This is what makes the definition semantic: it says when the new assertion <i>holds</i>, not what it looks like.'},
       {m:'Store.set σ x (e.eval σ)', h:'The store after the assignment, built with the operation Unit 18 gave you. <code>e.eval σ</code> is evaluated in the <i>old</i> store, which is what an assignment does, and it is the reason the definition is not <code>Q</code> composed with a store update and nothing more.'},
       {m:': Assertion', h:'The heap is passed through untouched. Assignment writes to the store, and the store is not a resource — the whole of the heap survives the command, which is why this rule can be proved without a single fact about memory.'}
     ]},

    {t:'p', h:'The decision that made that definition possible was taken in Unit 12, and it has a name: an assertion is a Lean predicate rather than a term of some syntax of assertions, which is a <b>shallow embedding</b>. The alternative is a <b>deep embedding</b>: an <code>inductive Assertion</code> with a constructor for each connective, a <code>def</code> performing capture-avoiding replacement over it, an interpretation function taking that syntax to <code>Store → Heap → Prop</code>, and then a theorem — the <i>substitution lemma</i> — saying that interpreting the substituted assertion at a store is the same as interpreting the original one at the updated store. That lemma is proved by induction over the syntax of assertions and it has a case for every connective. Here it is not a lemma at all: it is the definition, and it holds by <code>rfl</code>.'},

    {t:'p', h:'The bill for that convenience is real, and it is paid once, here. With assertions as functions you cannot do induction over an assertion, you cannot decide whether two assertions are equal, and you cannot write a program that transforms a specification. What you get instead is that any Lean predicate at all is an assertion, including recursively defined ones — which is what Unit 32 needs and no fixed syntax would have supplied.'},

    {t:'note', kind:'warn', title:'Two things called subst',
     h:'<code>subst</code> is also the name of a tactic, met in Unit 08, which eliminates a variable using an equation. The definition above shadows nothing: the tactic is still available, still called <code>subst</code>, and still works on the pages after this one. Nothing distinguishes them but position — one stands where a tactic goes and the other stands where a term goes. When you read <code>subst hp</code> it is the tactic; when you read <code>subst x e Q</code> it is the assertion transformer.'},

    {t:'ex',
     id: 'm6-3',
     name: 'hoare_assign',
     hard: false,
     why: 'The payoff of defining substitution semantically: the assignment axiom, which in a course with a syntax of assertions takes a substitution lemma and an induction, is here two tactics. It is also the first rule whose precondition is <i>computed</i> from its postcondition rather than supplied. Neither the theorem nor <code>subst</code> is cited much later — <code>subst</code> once, in Unit 31, where it is the exact answer to a question that unit poses about assignment, and <code>hoare_assign</code> not at all. What carries forward is the technique: a rule that runs backwards, and an assertion transformer defined by what it means.',
     setup: '<code>Exec.assign</code> is the constructor you need. Its conclusion is a run from <code>s</code> to <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code>, so it names the final state for you.',
     goal: "theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (subst x e Q) ((.assign x e)) (Q) := by",
     hints: [
       'The goal is: for every <code>σ</code> and <code>h</code> at which <code>subst x e Q</code> holds, there is a state that <code>.assign x e</code> reaches from <code>⟨σ, h⟩</code>, at which <code>Q</code> holds. Unfold the precondition and it says <code>Q (Store.set σ x (e.eval σ)) h</code> — which is <code>Q</code> holding at the state after the assignment.',
       'The state after the assignment is the state the command reaches. So the witness is forced, the derivation is one constructor, and the third component is the hypothesis you were handed, unchanged. Nothing has to be proved; three things have to be named.',
       '<code>intro</code> the three binders, then close with a single <code>exact</code> whose argument is a three-slot bracket. The middle slot is <code>Exec.assign</code>.',
       'The first line is <code>intro σ h hq</code>, leaving <code>hq : subst x e Q σ h</code> and the goal <code>⊢ ∃ s\', Exec (Cmd.assign x e) { store := σ, heap := h } s\' ∧ Q s\'.store s\'.heap</code>. The witness to supply is <code>⟨Store.set σ x (e.eval σ), h⟩</code>.'
     ],
     sol: "theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (subst x e Q) ((.assign x e)) (Q) := by\n  intro σ h hq\n  exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
     solNote: 'Two lines, and one of them is <code>intro</code>. The rule is nearly a tautology, and that is a fact about the choice made in <code>subst</code>, not about assignment.',
     expl: 'The third slot is where the design is spent. Lean has to accept <code>hq</code>, whose stated type is <code>subst x e Q σ h</code>, as a proof of <code>Q s\'.store s\'.heap</code> where <code>s\'</code> is the state supplied one slot earlier. Unfolding <code>subst</code> once turns the first into <code>Q (Store.set σ x (e.eval σ)) h</code>; projecting the second out of the state supplied gives the same thing. So the two types are definitionally equal and <code>exact</code> takes it. No rewriting happens and no lemma is cited.',
     walk: [
       {tac:'intro σ h hq', h:'Two <code>∀</code> binders and one arrow, as always. The goal becomes the existential at this store and heap, with the command displayed as <code>Cmd.assign x e</code> — the leading dot in the statement is an abbreviation for input, and Lean prints the full name.'},
       {tac:"exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩", h:'Three slots. The first names the final state, and it has to be exactly the state <code>Exec.assign</code> concludes with, or the second slot will not typecheck. The second is the constructor with no arguments — <code>assign</code> has no premises, because evaluating an expression cannot fail. The third is the premise, accepted at a different displayed type because the two are the same term after unfolding <code>subst</code>.'}
     ],
     deep: [
       {t:'trace', title:'hoare_assign, two tactics',
        start:"x : Var\ne : Atom\nQ : Assertion\n⊢ Hoare (subst x e Q) (Cmd.assign x e) Q",
        steps:[
          {tac:'intro σ h hq',
           state:"x : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\nhq : subst x e Q σ h\n⊢ ∃ s', Exec (Cmd.assign x e) { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
           h:'<code>hq</code> displays folded, as <code>subst x e Q σ h</code>. Lean will unfold it when it has to and not before, which is why the goal below never shows the substituted store.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The witness can be left to Lean. <code>exact ⟨_, Exec.assign, hq⟩</code> compiles as well, because <code>Exec.assign</code>\'s conclusion pins the state and unification reads it off; the version written out is preferred here because the state is the content of the rule and hiding it hides the rule.'},
       {t:'code', tag:'illustration', cap:'The precondition, at a concrete postcondition, opened by <code>show</code> and then discharged. Two layers come off at once: <code>subst</code>, and then the <code>fact</code> inside <code>Q</code>.',
        src:"example (x : Var) (σ : Store) (h : Heap) : subst x (.const 10) (fact (fun σ => σ x = 10)) σ h := by\n  show Store.set σ x 10 x = 10\n  simp [Store.set]"},
       {t:'p', h:'The heap binder in <code>subst</code> looks like plumbing you could economise on. Try to, and nothing is saved, which is the informative outcome. <code>Assertion</code> is <code>Store → Heap → Prop</code>, so <code>Q (Store.set σ x (e.eval σ))</code> already <i>is</i> a <code>Heap → Prop</code>: the shorter spelling is not a different definition, it is the same term with one fewer binder written down, and <code>rfl</code> says so.'},
       {t:'code', tag:'illustration', cap:'Compiled. The two spellings are equal by <code>rfl</code>, and the rule proves against the short one with the same two lines and the same witness.',
        src:"def substNoHeap (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ => Q (Store.set σ x (e.eval σ))\n\nexample (x : Var) (e : Atom) (Q : Assertion) : substNoHeap x e Q = subst x e Q := rfl\n\ntheorem hoare_assign_short (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (substNoHeap x e Q) ((.assign x e)) (Q) := by\n  intro σ h hq\n  exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩"}
     ],
     pitfall: 'Getting the witness wrong by writing the value into the wrong store. <code>e.eval σ</code> evaluates in the store <i>before</i> the assignment; writing <code>e.eval (Store.set σ x 0)</code>, or any other repaired store, gives a state that <code>Exec.assign</code> does not conclude with. Lean then reports <i>two</i> errors and neither one is about the state. The third slot fails, saying <code>hq</code> <code>has type</code> <code>subst x e Q σ h</code> <code>but is expected to have type</code> <code>Q { store := σ.set x (Atom.eval (σ.set x 0) e), heap := h }.store …</code>; and the second slot fails, saying <code>Exec.assign</code> concludes at a state whose store is <code>(State.store ?m.14).set ?m.15 (Atom.eval (State.store ?m.14) ?m.16)</code> where a store built with <code>Atom.eval (σ.set x 0) e</code> was wanted. Both messages are quoting your state back at you from the slots that had to accept it, and the slot that is wrong is the one neither of them names — read the two expected types against each other and the disagreement is in the argument to <code>Atom.eval</code>.',
     variants: 'Turn the rule around and state it forwards — <code>Hoare Q (.assign x e) (subst x e Q)</code> — and it is false. Take <code>Q := fact (fun σ => σ 0 = 0)</code>, <code>x := 0</code> and <code>e := .const 1</code>: the precondition holds at the store that is 0 everywhere, and the postcondition unfolds to <code>Store.set s\'.store 0 1 0 = 0</code>, whose left-hand side is 1. Restate it at that type with a <code>have</code>, let <code>simp [Store.set]</code> collapse the <code>if</code>, and the refutation is two lines. Dropping the heap argument from <code>subst</code>, on the other hand, changes nothing whatever — see below — for a reason that outlives this rule: nothing in <code>subst</code> ever takes the heap apart, so there is no thread to cut.'
    },

    /* ================================================= show in anger ====== */

    {t:'sec', s:'Making a goal readable'},

    {t:'p', h:'Every proof so far ended by handing back a hypothesis. The first proof that has to establish something about the final state runs into a display problem, and the fix is a tactic Unit 02 introduced as a convenience and which becomes load-bearing here.'},

    {t:'p', h:'The program is a single assignment of a constant, from the empty heap. The postcondition claims two things: variable <code>x</code> holds 10, and the heap is still empty. Written with the tools of Unit 12 and Unit 13 that is <code>aAnd (fact (fun σ => σ x = 10)) emp</code>. Supplying the state and the derivation, and the second conjunct — which is the precondition, unchanged — leaves one goal.'},

    {t:'state', cap:'After <code>intro σ h he</code> and <code>refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩</code>.',
     src:"x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) { store := σ.set x 10, heap := h }.store { store := σ.set x 10, heap := h }.heap"},

    {t:'p', h:'That goal is one short statement wearing two copies of a state it does not need. The plumbing is not accidental: the postcondition is applied to two projections, and the state those projections are taken from was written out by hand in the tactic above, so nothing has reduced it. If you cannot see the arithmetic in there, you cannot see whether the proof is going anywhere.'},

    {t:'p', h:'<code>show</code> replaces a goal with anything definitionally equal to it. Both projections reduce, and <code>fact φ σ h</code> is <code>φ σ</code> by definition, so the whole line is the same term as a single equation about the store.'},

    {t:'state', cap:'After <code>show Store.set σ x 10 x = 10</code>. Same four hypotheses, same proof obligation, one line of arithmetic. <code>σ.set x 10</code> is how Lean prints <code>Store.set σ x 10</code>.',
     src:"x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 10 x = 10"},

    {t:'p', h:'The tactic added a line to the proof and removed nothing from it, which is the point: you can type it and see the same thing. What is left is closed by <code>simp [Store.set]</code>, since <code>Store.set σ x 10 x</code> is an <code>if</code> whose condition is <code>x = x</code>.'},

    {t:'p', h:'The alternative is to skip the <code>show</code> and give <code>simp</code> enough names to chew through the whole display. It works, and it is instructive to see it half-work first.'},

    {t:'state', cap:'What <code>simp [Store.set]</code> leaves if the <code>show</code> is omitted — followed, in the same run, by a linter warning that <code>Store.set</code> was an unused simp argument.',
     src:"error: unsolved goals\nx : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) (σ.set x 10) h"},

    {t:'p', h:'<code>simp</code> reduced the two projections and then stopped, because <code>fact</code> is a plain definition and nothing told it to unfold one. It never reached a place where <code>Store.set</code> could fire, which is what the linter is reporting. Adding the missing name — <code>simp [fact, Store.set]</code> — closes the goal in one line. The cost is that the proof now names two definitions and states no goal, so anyone following it has to run Lean to find out what was being proved. The <code>show</code> costs one line and says it.'},

    {t:'ex',
     id: 'm6-4',
     name: 'assign_constant',
     hard: false,
     why: 'The first triple about a particular program rather than a rule schema, and the first proof in which <code>show</code> is doing work rather than decorating. From here to the end of the course, a goal that displays as an assertion applied to two projections is a goal you open with <code>show</code>, and the habit is cheaper to acquire on a two-line arithmetic fact than on a heap.',
     setup: 'The precondition is <code>emp</code> and the postcondition is a conjunction, so the answer has four slots rather than three — the anonymous constructor flattens, and the last two slots are the two conjuncts. The second conjunct is the precondition, unchanged, because assignment does not touch the heap.',
     goal: "theorem assign_constant (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by",
     hints: [
       'The goal says: from any store and any empty heap, running <code>x := 10</code> reaches a state at which two things hold — variable <code>x</code> holds 10, and the heap is empty. The heap half is the hypothesis you were given, so the work is the store half.',
       'The final state is <code>⟨Store.set σ x 10, h⟩</code>, and the derivation is one constructor. What is left is the arithmetic claim that looking up <code>x</code> in a store that has had 10 written to <code>x</code> gives 10.',
       'Build the answer with <code>refine</code>, leaving a hole for the store half and filling the heap half with the hypothesis. Then use <code>show</code> to state what the remaining goal is, and finish with <code>simp</code> naming <code>Store.set</code>.',
       'The line after <code>intro σ h he</code> is <code>refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩</code>. It leaves one goal, displayed as <code>fact</code> applied to two projections of the state you supplied.'
     ],
     sol: "theorem assign_constant (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  intro σ h he\n  refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩\n  show Store.set σ x 10 x = 10\n  simp [Store.set]",
     solNote: 'Four lines, of which one is a statement of what is being proved. If you climbed all four hints and are still stuck, open this: the shape — build the answer, leave a hole, name the hole, discharge it — is the shape of every concrete verification in this course.',
     expl: 'The four-slot bracket is a three-slot one whose last slot has been flattened: the postcondition is <code>aAnd A B</code>, which is a conjunction, so <code>⟨s\', hex, ha, hb⟩</code> and <code>⟨s\', hex, ⟨ha, hb⟩⟩</code> are the same term. Writing it flat means the heap conjunct can be discharged inline with <code>he</code> and only the store conjunct becomes a hole. The hole then displays unreadably, <code>show</code> restates it as the equation it definitionally is, and <code>simp [Store.set]</code> settles an <code>if</code> whose condition is <code>x = x</code>.',
     walk: [
       {tac:'intro σ h he', h:'Store, heap, and the proof that the heap is empty. <code>he</code> is kept, because the postcondition asks for the same fact back.'},
       {tac:"refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩", h:'Four slots filled at once, one of them a hole. The first names the state after the assignment; the second is the rule; the fourth is the heap conjunct, discharged by the hypothesis without a word. Only the store conjunct is left, as <code>?_</code>.'},
       {tac:'show Store.set σ x 10 x = 10', h:'Replaces a goal that reads <code>fact (fun σ => σ x = 10) { … }.store { … }.heap</code> with the equation it is definitionally equal to. Two things reduce here: the structure projections, and the application of <code>fact</code> to its argument.'},
       {tac:'simp [Store.set]', h:'Unfolds <code>Store.set</code> to the <code>if</code> it is, settles the condition <code>x = x</code>, and closes the goal.'}
     ],
     deep: [
       {t:'trace', title:'assign_constant, from the refine onwards',
        start:"x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign x (Atom.const 10)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 10) emp s'.store s'.heap",
        steps:[
          {tac:"refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩",
           state:"x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) { store := σ.set x 10, heap := h }.store { store := σ.set x 10, heap := h }.heap",
           h:'One goal out of four slots, because three of them were filled. The state built by hand is still displayed in full, twice, once under each projection — nothing has reduced it, because nothing has asked.'},
          {tac:'show Store.set σ x 10 x = 10',
           state:"x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 10 x = 10",
           h:'The same goal, restated. Lean accepted it because both projections reduce and <code>fact φ σ h</code> is <code>φ σ</code> by unfolding one definition.'}
        ],
        done:'No goals.'},
       {t:'p', h:'A three-slot bracket works too — <code>refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_⟩</code> — and leaves the whole conjunction as one goal, which then needs a <code>constructor</code> or a two-slot bracket of its own. The flat form is shorter and puts the trivial conjunct out of sight; the nested form makes the shape of the postcondition visible. Either is fine, and the second is the one to reach for when neither conjunct is trivial.'}
     ],
     pitfall: 'Reaching for <code>simp [Store.set]</code> without the <code>show</code>. It does not fail loudly — it reduces the projections, leaves <code>⊢ fact (fun σ => σ x = 10) (σ.set x 10) h</code>, and reports <code>unsolved goals</code> together with a linter warning that <code>Store.set</code> was an unused simp argument. The warning is the useful half: <code>simp</code> never got as far as anything <code>Store.set</code> could rewrite, because <code>fact</code> stopped it. Either name <code>fact</code> as well, or say what the goal is with <code>show</code> and let <code>simp</code> work on an equation.',
     variants: 'Change the postcondition\'s second conjunct from <code>emp</code> to <code>aTrue</code> and the proof still works with <code>he</code> replaced by <code>True.intro</code> — assignment leaves the heap alone, so anything true of it before is true of it after. Change the first conjunct to <code>fact (fun σ => σ x = 11)</code> and the <code>show</code> is <i>accepted</i>: <code>Store.set σ x 10 x = 11</code> really is definitionally the goal, because unfolding <code>fact</code> and the two projections has nothing to do with whether 10 and 11 are equal. It is <code>simp</code> that stops, having collapsed the <code>if</code> and reduced the equation to <code>⊢ False</code>. Replace the precondition <code>emp</code> by <code>aTrue</code>, though, and the theorem is false and the proof breaks at exactly the fourth slot: <code>he</code> now <code>has type</code> <code>aTrue σ h</code> <code>but is expected to have type</code> <code>emp { store := σ.set x 10, heap := h }.store { store := σ.set x 10, heap := h }.heap</code>. The postcondition still says the heap is empty and nothing says it any more — a one-cell heap satisfies <code>aTrue</code>, and the assignment hands it back unchanged, so the whole triple is refutable at <code>Heap.singleton 0 0</code>. The <code>emp</code> in the precondition is never inspected, but it is not decoration either: it is what pays for the <code>emp</code> in the postcondition.'
    },

    /* ================================================ the middle assertion */

    {t:'sec', s:'Choosing what holds in the middle'},

    {t:'p', h:'Two assignments in a row: put 3 into <code>x</code>, then copy <code>x</code> into <code>y</code>. The claim is that both variables end up holding 3, from the empty heap, with the heap still empty at the end. <code>hoare_seq</code> is the rule, and applying it exposes the one thing about the rule that its own proof hid.'},

    {t:'state', cap:'What <code>refine hoare_seq ?_ ?_</code> reports. The <code>?m</code> in the displayed application is the assertion Lean cannot find, and the two lines under <code>context:</code> are the goal it would like you to solve.',
     src:"error: don't know how to synthesize implicit argument `Q`\n  @hoare_seq emp ?m.12 (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp) (Cmd.assign x (Atom.const 3))\n    (Cmd.assign y (Atom.var x)) ?m.16 ?m.17\ncontext:\nx y : Var\n⊢ Assertion"},

    {t:'p', h:'<code>⊢ Assertion</code> is Lean asking for an assertion, and it is asking because nothing determines one. The precondition and the postcondition of the conclusion are fixed by the goal; the middle assertion appears only in the two premises, and both premises are holes. There is no unification problem to solve, and no amount of tactic cleverness will invent an answer.'},

    {t:'p', h:'This is the point at which verifying a program stops being mechanical. The intermediate assertion is a claim about what is true half way through, and choosing it is the mathematical content: it has to be weak enough to be provable from the first command and strong enough to prove the second. The rule cannot supply it because the rule does not know what the program is for.'},

    {t:'p', h:'Supplying it is one piece of syntax. Writing <code>hoare_seq (Q := A)</code> fills the implicit argument named <code>Q</code> with <code>A</code> and leaves the rest of the arguments to be inferred as usual; the name is the one in the theorem\'s binder list, so it is <code>Q</code> here because <code>hoare_seq</code> was declared with <code>{P Q R : Assertion}</code>.'},

    {t:'p', h:'One more thing about this program can be predicted before you prove it. Copying <code>x</code> into <code>y</code> looks like it needs <code>x</code> and <code>y</code> to be different variables: if they are the same, the second command overwrites the value the first one established. Write the hypothesis <code>x ≠ y</code> into the statement if you like. Then see whether the proof uses it.'},

    {t:'ex',
     id: 'm6-5',
     name: 'assign_twice',
     hard: false,
     why: 'The first verification where you choose the intermediate assertion, which is the act every later verification is made of. It is also the first place a hypothesis you were sure you needed turns out to be unnecessary, and the formalisation is what tells you — a side condition assumed on paper and refuted by a proof that never reaches for it.',
     setup: 'Use <code>hoare_seq</code> with its <code>Q</code> supplied by name. Each half is then an <code>assign_constant</code>-shaped proof. In the second half you will need the store fact from the precondition in a form <code>simp</code> can use, which is one <code>have</code>.',
     goal: "theorem assign_twice (x y : Var) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := by",
     hints: [
       'The goal is a triple about a two-command program: from the empty heap, running <code>x := 3</code> and then <code>y := x</code> ends in a state where <code>σ x = 3</code>, <code>σ y = 3</code>, and the heap is empty. You have <code>hoare_seq</code>, which needs an assertion for the middle of the program.',
       'After the first command, what is true? Variable <code>x</code> holds 3 and the heap is still empty. That is the middle assertion, and it is the postcondition of the first half and the precondition of the second. The first half is then the previous exercise with 3 for 10; the second half has a real hypothesis to spend, namely that <code>x</code> holds 3.',
       '<code>refine hoare_seq (Q := …) ?_ ?_</code> splits the goal into the two halves. Each half opens with <code>intro</code> and a four-slot <code>refine</code>, and each is finished by <code>show</code> and <code>simp</code>. In the second half, <code>obtain</code> the precondition\'s two conjuncts apart before using either.',
       'The first line is <code>refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_</code>. It leaves two goals, tagged <code>case refine_1</code> and <code>case refine_2</code>; the first is <code>Hoare emp (Cmd.assign x (Atom.const 3)) (aAnd (fact fun σ => σ x = 3) emp)</code>.'
     ],
     sol: "theorem assign_twice (x y : Var) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := by\n  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_\n  · intro σ h he\n    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 3 x = 3\n    simp [Store.set]\n  · intro σ h hpre\n    obtain ⟨hx, he⟩ := hpre\n    have hx' : σ x = 3 := hx\n    refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3\n    constructor\n    · show (if x = y then σ x else σ x) = 3\n      simp [hx']\n    · show (if y = y then σ x else σ y) = 3\n      simp [hx']",
     solNote: 'There is no <code>x ≠ y</code> anywhere in it, and the last two branches are where that shows: one of them is an <code>if</code> whose two arms are the same term.',
     expl: 'The first line is the only creative one. Everything after it is the previous exercise done twice, with one addition: the second half has a hypothesis about the store and has to get it into a shape <code>simp</code> will accept. <code>hx</code> is a proof of <code>fact (fun σ => σ x = 3) σ h</code>, which is definitionally the equation <code>σ x = 3</code> but does not display as one, and <code>simp</code> matches on what a hypothesis displays as. The <code>have</code> restates it at the type <code>simp</code> can read, and costs one line.',
     walk: [
       {tac:"refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_", h:'Splits the program at the semicolon. <code>(Q := …)</code> supplies the assertion that holds in the middle, which nothing else could have determined. Two goals remain, one per command.'},
       {tac:'· intro σ h he', h:'The first half. Store, heap, and the proof that the heap is empty.'},
       {tac:"refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩", h:'The state after <code>x := 3</code>, the rule, a hole for the store conjunct, and the heap conjunct discharged by the hypothesis.'},
       {tac:'show Store.set σ x 3 x = 3', h:'Restates the hole as the equation it is, stripping the two projections and the application of <code>fact</code>.'},
       {tac:'simp [Store.set]', h:'Closes it: the <code>if</code> condition is <code>x = x</code>.'},
       {tac:'· intro σ h hpre', h:'The second half. The precondition is now the middle assertion, so <code>hpre</code> carries two facts rather than one.'},
       {tac:'obtain ⟨hx, he⟩ := hpre', h:'Splits <code>aAnd</code> into its conjuncts: <code>hx</code> about the store, <code>he</code> about the heap. <code>aAnd</code> is a folded conjunction and <code>obtain</code> looks through the definition to find its two fields.'},
       {tac:"have hx' : σ x = 3 := hx", h:'Restates <code>hx</code> at a type that displays as an equation. Nothing is proved here — the term is <code>hx</code> unchanged — and the only difference is what the hypothesis looks like to a tactic that matches on syntax.'},
       {tac:"refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩", h:'The state after <code>y := x</code>. The value written is <code>σ x</code>, because <code>(Atom.var x).eval σ</code> reduces to it; the heap conjunct is again the hypothesis.'},
       {tac:'show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3', h:'The postcondition is a conjunction inside a <code>fact</code>, so opening it gives two equations about the same updated store. Both are about lookups in a store whose <code>y</code> entry has been overwritten.'},
       {tac:'constructor', h:'Splits the conjunction into two goals, <code>case refine_2.left</code> and <code>case refine_2.right</code>: one equation about looking up <code>x</code> in the updated store, one about looking up <code>y</code>. The context is the same in both, and it is the lookup that differs.'},
       {tac:'· show (if x = y then σ x else σ x) = 3', h:'The left conjunct, with <code>Store.set</code> unfolded by hand. The two arms of the <code>if</code> are the same term — this is the branch where the missing side condition would have been spent, and there is nothing to spend it on.'},
       {tac:"simp [hx']", h:'Collapses the <code>if</code>, whose arms agree, and rewrites with the store fact.'},
       {tac:'· show (if y = y then σ x else σ y) = 3', h:'The right conjunct. Here the condition is <code>y = y</code>, so the <code>if</code> takes the first arm and the goal becomes the same equation as the left conjunct.'},
       {tac:"simp [hx']", h:'Closes it the same way.'}
     ],
     deep: [
       {t:'trace', title:'assign_twice, the split and the second half',
        start:"x y : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 3) ;; Cmd.assign y (Atom.var x)) (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp)",
        steps:[
          {tac:"refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_",
           state:"case refine_1\nx y : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 3)) (aAnd (fact fun σ => σ x = 3) emp)\n\ncase refine_2\nx y : Var\n⊢ Hoare (aAnd (fact fun σ => σ x = 3) emp) (Cmd.assign y (Atom.var x)) (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp)",
           h:'Two goals, and the assertion you supplied appears three times across them: as the postcondition of the first and the precondition of the second. That triple appearance is the whole reason it cannot be inferred.'},
          {tac:'intro σ h hpre',
           state:"case refine_2\nx y : Var\nσ : Store\nh : Heap\nhpre : aAnd (fact fun σ => σ x = 3) emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
           h:'In the second branch. The precondition is now a conjunction of a store fact and a heap fact, folded under <code>aAnd</code>.'},
          {tac:'obtain ⟨hx, he⟩ := hpre',
           state:"case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
           h:'The conjunction splits, and <code>hx</code> arrives displaying as <code>fact (fun σ => σ x = 3) σ h</code> rather than as an equation. That display is the reason for the next line.'},
          {tac:"have hx' : σ x = 3 := hx",
           state:"case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
           h:'<code>hx</code> and <code>hx\'</code> are the same proof under two displayed types, and both are in the context at once. Nothing has been derived; a name has been given to a reading.'}
        ],
        done:'Two more shows, a constructor and two simps.'},
       {t:'p', h:'Leaving out the <code>have</code> and writing <code>simp [hx]</code> in the two branches gets further than you might expect and then stops. <code>simp</code> collapses both <code>if</code>s, leaving <code>⊢ σ x = 3</code> in each branch — and reports <code>hx</code> as an <i>unused</i> simp argument, because a hypothesis of type <code>fact (fun σ => σ x = 3) σ h</code> is not something it can read as a rewrite rule. Both goals are then closable by <code>exact hx</code>, since the type it cannot rewrite with is the type it needs. Either repair works; the <code>have</code> is preferred because it names the reading once instead of twice.'}
     ],
     pitfall: 'Writing <code>refine hoare_seq ?_ ?_</code> and hoping. Lean reports <code>don\'t know how to synthesize implicit argument</code> <code>Q</code> and prints <code>⊢ Assertion</code> as the context — it is asking you for the middle assertion, not complaining about a mistake. The second, quieter version of the same mistake is choosing a middle assertion that is true but too weak, and it does not announce itself either. <code>emp</code> alone is true after <code>x := 3</code>, and taking <code>Q := emp</code> makes <code>case refine_1</code> <i>shorter</i> — three slots and no hole, since nothing is claimed about the store. Then <code>case refine_2</code> arrives at <code>⊢ σ.set y (σ x) x = 3 ∧ σ.set y (σ x) y = 3</code> with a context of <code>x y : Var</code>, <code>σ : Store</code>, <code>h : Heap</code> and <code>he : emp σ h</code>, and there is nothing to do: <code>σ</code> is arbitrary and no hypothesis mentions <code>σ x</code>. A middle assertion is too weak exactly when the second branch reaches a goal about a store that the context has stopped describing.',
     variants: 'Add <code>(hne : x ≠ y)</code> to the statement and everything still compiles, with a warning: <code>Variable name `hne` is not explicitly referenced.</code> The theorem is genuinely true without it, and the degenerate case is the reason — with <code>x</code> and <code>y</code> the same variable the program is <code>x := 3; x := x</code>, which copies the value onto itself, so <code>assign_twice x x</code> is a real instance and compiles. That is visible in the proof at exactly one line, <code>show (if x = y then σ x else σ x) = 3</code>, where the two arms of the <code>if</code> are the same term. Change the second command to <code>.assign y (.const 4)</code>, with the postcondition changed to <code>σ x = 3 ∧ σ y = 4</code>, and the side condition becomes load-bearing at that same line and no other: the <code>if</code> is now <code>if x = y then 4 else σ x</code>, whose arms differ, and closing it takes <code>simp [hne, hx\']</code> where <code>simp [hx\']</code> sufficed. Without <code>hne</code> that statement is false — at <code>x = y</code> the program is <code>x := 3; x := 4</code>, the postcondition claims <code>σ x = 3 ∧ σ x = 4</code>, and rewriting the first conjunct into the second gives <code>3 = 4</code>.'
    },

    {t:'code', tag:'illustration', cap:'Both compiled. The first reports the unused-binder warning and nothing else; the second is the degenerate instance, at one variable used twice.',
     src:"example (x y : Var) (hne : x ≠ y) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := assign_twice x y\n\nexample (x : Var) : Hoare emp (.assign x (.const 3) ;; .assign x (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ x = 3)) emp) := assign_twice x x"},

    {t:'p', h:'A side condition that everyone writes down, that the informal argument appears to need, and that the proof never asks for. It is not a deep fact — the reason is one line of the proof — but it is the kind of thing an informal argument gets wrong in the same direction every time, by assuming a disjointness it has not checked it needs. The rest of this course is about a disjointness that is genuinely needed, and about the machinery for saying exactly how much of it.'},

    {t:'dod', h:'You can state a Hoare triple and say what each part of it claims; you can say why the implication form is satisfied by a program that always faults, and produce the program; you can prove the rule of consequence and predict its variance from the shape of the definition; you can run one triple into another and supply the assertion in the middle by name; and you can take a goal that displays as an assertion applied to two projections and turn it into something you can read.'},

    {t:'p', h:'Three structural rules and one axiom, and none of them touches the heap. Consequence never inspects the state at all; <code>skip</code> hands it back; sequencing passes it along; and assignment carries it from precondition to postcondition without looking at a single address. The moment a rule does, the question Unit 07 answered becomes operational: <i>how much</i> memory does the rule mention?'}

  ]
});
