registerChapter({
  id: 'aliasing-closed',
  num: '28',
  phase: 'Phase 5 · Locality and the frame rule',
  title: 'The opening question, closed',
  blurb: 'The statement left unproved on the first page, refuted; the same specification with ∗ in place of ∧, proved by framing in four lines; and a list of what the two proofs between them settle.',

  orient: {
    youWill: [
      'Read the statement left unproved on the first page and say, in one sentence, what it claims.',
      'Refute it: choose the instance, choose the heap, and read the contradiction off the memory the command produced.',
      'Give a second refutation of the same statement that never looks at the run, and say what each of the two denies.',
      'Show that the repair Unit 00 proposed is not enough, with a counterexample containing no aliasing at all.',
      'State the classical rule with the two things it has to add before it is true, and prove it.',
      'Prove the same specification with <code>∗</code> in place of <code>aAnd</code>, in four lines, with no hypothesis at all.',
      'Say where the disequality went, and name the theorem that recovers it from the precondition.',
      'List what the course has established, and the three things it has not.'
    ],
    needs: [
      'Unit 07: <code>ptsAtLeast</code>, and what the loose reading of &ldquo;<code>l</code> holds <code>v</code>&rdquo; claims.',
      'Unit 19 and Unit 22: <code>Exec</code> and inversion by <code>cases</code>; <code>Hoare</code> as an existential over final states.',
      'Unit 23: <code>hoare_write</code>. Unit 24: <code>preserves_of_heapOnly</code>, <code>heapOnly_pointsTo</code>. Unit 25: <code>heapLocal_write</code>. Unit 27: <code>hoare_frame</code>.',
      'Unit 17: <code>two_cells_distinct</code>. Unit 05: <code>singleton_same</code>, <code>write_same</code>, <code>write_other</code>.'
    ],
    payoff: 'This is where the frame rule stops being the subject and becomes a tool. The four-line proof on this page is the shape every later verification in the course has — prove the specification on the cells the command touches, then frame the rest on — and Unit 29 turns those two steps into a fixed sequence of four.'
  },

  blocks: [

    /* ====================================================== the debt ==== */

    {t:'p', h:"Here it is. It was unreadable when it was written down, on purpose, and every word of it has since been defined: <code>ptsAtLeast</code> is Unit 07&rsquo;s loose reading of <i>address <code>l</code> holds <code>v</code></i>; <code>aAnd</code> is Unit 12&rsquo;s pointwise conjunction; <code>.write</code> and <code>.const</code> are constructors from Unit 18; <code>Hoare</code> is Unit 22&rsquo;s triple. Nothing in it is new. What is new is that you can read it, and refute it."},

    {t:'anat', tag:'verified',
     src:"theorem classical_conjunction_rule_is_false :\n    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),\n        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))\n              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b)))",
     parts:[
       {m:'¬', h:"To deny the rule is to turn any proof of it into a proof of <code>False</code>. That is the shape Unit 00&rsquo;s <code>x02</code> had, at a single heap. Here the thing being denied is quantified, so a proof of it is a function and the first move is to apply it."},
       {m:'∀ (l₁ l₂ : Loc) (a b : Val)', h:"Two addresses and two values, universally quantified — the part <code>x02</code> could not touch, because there was no way to say <i>for every pair of addresses</i> about a rule that did not exist. Refuting a <code>∀</code> costs one instance, and choosing it is the only decision in the proof."},
       {m:'ptsAtLeast l₁ a', h:"The precondition, in the loose reading: the heap maps <code>l₁</code> to <code>a</code>, and says nothing about the rest of memory. That is what a classical assertion is — a fact that happens to be true of the memory in hand, held alongside everyone else&rsquo;s facts about the same memory."},
       {m:'.write l₂ (.const b)', h:"Write the literal <code>b</code> into address <code>l₂</code>. Nothing in the statement relates <code>l₂</code> to <code>l₁</code>."},
       {m:'aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b)', h:"The postcondition: carry the precondition across unchanged, and add what the write made true. Both conjuncts are evaluated at the whole final heap, which is what <code>aAnd</code> does — it hands the same store and the same heap to both sides."}
     ]},

    {t:'p', h:"As a rule about programs it is the rule from the first page with the program variables replaced by the addresses they held: <code>[x]</code> became <code>l₁</code>, <code>[y]</code> became <code>l₂</code>. Nothing was lost in the translation, because the aliasing on that page was two variables holding one address, and here it is two addresses being equal."},

    {t:'p', h:"A proof begins by assuming the rule, and what is assumed is a function. Hand it two addresses and two values and it returns a triple; a triple is itself a function, since <code>Hoare P c Q</code> unfolds to <code>∀ σ h, P σ h → ∃ s&#39;, Exec c ⟨σ, h⟩ s&#39; ∧ Q s&#39;.store s&#39;.heap</code>. So hand it a store, a heap, and a proof that the precondition holds there, and three things come back: a final state, a run of the command reaching it, and the postcondition at that state. Everything after that is bookkeeping on what came back."},

    /* ================================================ choosing the instance ==== */

    {t:'h3', s:'Choosing the instance'},

    {t:'p', h:"Four things have to be chosen, and each is forced by what has to go wrong. <b>The two addresses must be equal</b>, since the rule is sound whenever they differ and there is nothing to catch; take both to be 0. <b>The two values must differ</b>, since writing 3 over 3 leaves a memory in which 0 holds 3 twice and the postcondition is satisfied; take 3 and 5."},

    {t:'p', h:"<b>The heap must satisfy the precondition</b>, which under the loose reading means it maps 0 to 3 and may do anything elsewhere. <code>Heap.singleton 0 3</code> is the smallest such heap, and the proof that it satisfies <code>ptsAtLeast 0 3</code> is one lookup law, <code>singleton_same 0 3</code>. That the precondition is discharged by a single equation is what the loose reading <i>is</i>: <code>ptsAtLeast l a</code> unfolds to <code>h l = some a</code> and asks for nothing else. <b>The store is never consulted</b> — no assertion here mentions a program variable — so <code>fun _ => 0</code> will do."},

    /* ---------------------------------------------------------------- x55 --- */

    {t:'ex',
     id:'x55',
     name:'classical_conjunction_rule_is_false',
     hard:true,

     why:"This is the theorem the course was built to reach. Unit 00 asserted that the rule is false and refuted one postcondition about one heap; that refutation was a fact about <code>Option</code>, and it left the quantified statement standing. What you prove here is the statement itself, inside the logic, against the real semantics, with every ingredient — the heap, the lookup laws, the execution relation, the triple — proved by you on the way. Nothing downstream cites it. Its value is that it is the answer to the question the course opened with, and it is now a theorem rather than a claim.",

     setup:"The editor holds the statement and a <code>sorry</code>. Everything you need is in scope: <code>Heap.singleton</code> and <code>Heap.write</code> from Unit 05 with their lookup laws, <code>Exec</code> from Unit 19, and <code>Hoare</code> from Unit 22. The instance is yours to choose.",

     goal:"theorem classical_conjunction_rule_is_false :\n    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),\n        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))\n              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))) := by\n  sorry",

     hints:[
       "The goal is <code>¬ P</code>, and <code>¬ P</code> is <code>P → False</code>. So what is being asked for is a function from a proof of the rule to a proof of <code>False</code>. Unfold what <code>P</code> promises. It quantifies over two addresses and two values; for each choice it asserts a <code>Hoare</code> triple; and <code>Hoare P c Q</code> is <code>∀ σ h, P σ h → ∃ s&#39;, Exec c ⟨σ, h⟩ s&#39; ∧ Q s&#39;.store s&#39;.heap</code>. Stacked up: for every <code>l₁</code>, <code>l₂</code>, <code>a</code>, <code>b</code>, every store and every heap in which <code>l₁</code> holds <code>a</code>, there is a state that <code>write l₂ b</code> reaches from there, and in that one state <code>l₁</code> holds <code>a</code> and <code>l₂</code> holds <code>b</code>.",
       "The shape, in mathematics, with no Lean. Choose both addresses to be the same address, and the two values to be different. Choose a starting memory in which that address holds the first value. Apply the rule to all of this: it promises a final memory in which the command has run, and in which that one address holds the first value and also holds the second. Compute the final memory — it is the starting one with the second value written in — and look up the address. The promise is that a function takes two different values at one argument.",
       "Six moves and two lemmas, in this order. <code>intro</code> to assume the rule; <code>obtain</code> to take apart what comes back when the rule is applied — a final state, a run, and both conjuncts; <code>cases</code> on the run, because until the run is inverted the final state is an opaque <code>s&#39;</code> and its heap cannot be computed; <code>have</code>, to restate the surviving conjunct as an equation between concrete heaps; <code>rw … at</code> on that, with <code>write_same</code>, to evaluate the lookup; and <code>exact absurd</code> to finish. The second lemma is <code>singleton_same</code>, and it discharges the precondition when the rule is applied.",
       "Start with <code>intro hall</code>, which leaves <code>⊢ False</code> with the rule named <code>hall</code>. Then the instance, in one application: <code>hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)</code> — the four quantified arguments, then the store, the heap, and the proof that the heap satisfies <code>ptsAtLeast 0 3</code>. Put <code>obtain ⟨s&#39;, hex, h3, h5⟩ :=</code> in front of it. You are then holding a final state, a run of <code>write 0 5</code> from the singleton heap to it, and both conjuncts of the postcondition at it."
     ],

     sol:"theorem classical_conjunction_rule_is_false :\n    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),\n        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))\n              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))) := by\n  intro hall\n  obtain ⟨s', hex, h3, h5⟩ :=\n    hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)\n  cases hex with\n  | write hl =>\n      have e3 : Heap.write (Heap.singleton 0 3) 0 5 0 = some 3 := h3\n      rw [write_same] at e3\n      exact absurd e3 (by simp)",

     solNote:"Eight lines, of which two are the choice of instance and two are the header of a case analysis with one case. If you climbed all four hints and are still short of it, open this and read the walk: the step that is genuinely hard to invent is the <code>have</code>, which restates <code>h3</code> as an equation between concrete heaps so that a rewrite has something to bite on.",

     expl:"The rule promises a final state in which both conjuncts hold. Inverting the run tells you which state that is — <code>Exec</code> has exactly one rule whose conclusion is a run of <code>.write</code>, and that conclusion names the final state — so the two conjuncts become claims about <code>Heap.write (Heap.singleton 0 3) 0 5</code>. The second is true. The first says that a heap into which 5 has been written at 0 still holds 3 there, and <code>write_same</code> says otherwise.",

     walk:[
       {tac:'intro hall',
        h:"Turns the goal <code>¬ P</code> into <code>False</code> and puts <code>P</code> in the context under the name <code>hall</code>. From here the work is forwards: build a contradiction out of a hypothesis, rather than construct anything."},
       {tac:"obtain ⟨s', hex, h3, h5⟩ := hall 0 0 3 5 …",
        h:"Two things at once. The application <code>hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)</code> instantiates the quantifiers and then runs straight through the folded <code>Hoare</code>: the last three arguments are the store, the heap and the proof of the precondition. What comes back is <code>∃ s&#39;, Exec … s&#39; ∧ aAnd … s&#39;.store s&#39;.heap</code>, and <code>obtain</code> takes it apart into four names — the existential witness, the run, and the two conjuncts, since the pattern flattens through both the <code>∧</code> and the folded <code>aAnd</code>."},
       {tac:'cases hex with',
        h:"Inversion on the run. Until this line <code>s&#39;</code> is an opaque state and <code>h3</code> and <code>h5</code> are claims about a heap nobody can compute. <code>Exec</code> has one rule whose conclusion is a run of <code>.write</code>, so there is one case, and taking it replaces <code>s&#39;</code> everywhere by the state that rule names."},
       {tac:'| write hl =>',
        h:"The single case. <code>hl</code> is <code>Exec.write</code>&rsquo;s premise — that 0 was already mapped in the starting heap — and this proof never uses it; <code>| write _ =&gt;</code> compiles equally well. What the line is for is the substitution it performs on <code>h3</code> and <code>h5</code>, both of which are now stated at <code>Heap.write (Heap.singleton 0 3) 0 5</code>, written out as projections of the starting state."},
       {tac:'have e3 : Heap.write (Heap.singleton 0 3) 0 5 0 = some 3 := h3',
        h:"A definitional restatement, and the only inventive line. <code>h3</code> is <code>ptsAtLeast 0 3</code> applied to the final store and the final heap, and both of those are written as projections out of a structure literal — ten lines of display for a claim that is one equation. Writing that equation down and offering <code>h3</code> as its proof is accepted because the two are the same term, and it replaces the display with something <code>rw</code> can match."},
       {tac:'rw [write_same] at e3',
        h:"Evaluates the lookup inside <code>e3</code>. <code>write_same</code> says <code>Heap.write h l v l = some v</code>; the goal fixes <code>h</code>, <code>l</code> and <code>v</code>, so no arguments are needed, and <code>e3</code> becomes <code>some 5 = some 3</code>."},
       {tac:'exact absurd e3 (by simp)',
        h:"<code>absurd</code> takes a proof and a proof of its negation and returns anything. <code>simp</code> supplies the negation, from the distinctness of two values under <code>some</code>. The goal was <code>False</code>, so anything is what was wanted."}
     ],

     deep:[
       {t:'trace', title:'classical_conjunction_rule_is_false, tactic by tactic',
        start:'⊢ ¬∀ (l₁ l₂ : Loc) (a b : Val),\n      Hoare (ptsAtLeast l₁ a) (Cmd.write l₂ (Atom.const b)) (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))',
        steps:[
          {tac:'intro hall',
           state:'hall :\n  ∀ (l₁ l₂ : Loc) (a b : Val),\n    Hoare (ptsAtLeast l₁ a) (Cmd.write l₂ (Atom.const b)) (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))\n⊢ False',
           h:"The hypothesis prints over three lines and never changes again, so it is omitted from the states below; nothing else is elided from them. Line-and-column prefixes are dropped throughout, and every display here is <code>trace_state</code> output."},
          {tac:"obtain ⟨s', hex, h3, h5⟩ := hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)",
           state:"s' : State\nhex : Exec (Cmd.write 0 (Atom.const 5)) { store := fun x => 0, heap := Heap.singleton 0 3 } s'\nh3 : ptsAtLeast 0 3 s'.store s'.heap\nh5 : ptsAtLeast 0 5 s'.store s'.heap\n⊢ False",
           h:"The four things the instance handed back. Both conjuncts are stated at the same <code>s&#39;</code>, which is the whole of what is wrong with the rule — but <code>s&#39;</code> is a variable, so no lookup can be computed yet."},
          {tac:'cases hex with | write hl =>',
           state:"case write\nold✝ : Val\nhl : { store := fun x => 0, heap := Heap.singleton 0 3 }.heap 0 = some old✝\n⊢ False",
           h:"<code>h3</code> and <code>h5</code> are omitted here: each now runs to ten printed lines, because <code>s&#39;</code> has been replaced by the structure literal <code>Exec.write</code>&rsquo;s conclusion names, unreduced, twice over. The fold below has both in full. This is the state the <code>have</code> exists to escape."},
          {tac:'have e3 : Heap.write (Heap.singleton 0 3) 0 5 0 = some 3 := h3',
           state:'e3 : (Heap.singleton 0 3).write 0 5 0 = some 3\n⊢ False',
           h:"Same omission. <code>e3</code> is <code>h3</code> with the display collapsed: the projections have gone, <code>Atom.eval σ (Atom.const 5)</code> has become <code>5</code>, and what is left is one equation between concrete heaps. Lean prints it with dot notation because <code>Heap.write</code>&rsquo;s first explicit argument is a <code>Heap</code>."},
          {tac:'rw [write_same] at e3',
           state:'e3 : some 5 = some 3\n⊢ False',
           h:"The lookup is gone and what remains is two distinct values under <code>some</code>."}
        ],
        done:'No goals.'},

       {t:'detail', title:'The state after cases, in full', tag:'aside', blocks:[
         {t:'p', h:"Twenty-seven lines, of which the goal is one. The two hypotheses that matter are <code>h3</code> and <code>h5</code>, and each of them says one thing in ten lines because Lean has substituted <code>Exec.write</code>&rsquo;s conclusion — a structure literal built out of projections of another structure literal — and has no reason to reduce it."},
         {t:'state', cap:'<code>trace_state</code> immediately after the <code>| write hl =></code> line, line-and-column prefixes dropped, nothing else removed.',
          src:"case write\nhall :\n  ∀ (l₁ l₂ : Loc) (a b : Val),\n    Hoare (ptsAtLeast l₁ a) (Cmd.write l₂ (Atom.const b)) (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))\nold✝ : Val\nhl : { store := fun x => 0, heap := Heap.singleton 0 3 }.heap 0 = some old✝\nh3 :\n  ptsAtLeast 0 3\n    { store := { store := fun x => 0, heap := Heap.singleton 0 3 }.store,\n        heap :=\n          { store := fun x => 0, heap := Heap.singleton 0 3 }.heap.write 0\n            (Atom.eval { store := fun x => 0, heap := Heap.singleton 0 3 }.store (Atom.const 5)) }.store\n    { store := { store := fun x => 0, heap := Heap.singleton 0 3 }.store,\n        heap :=\n          { store := fun x => 0, heap := Heap.singleton 0 3 }.heap.write 0\n            (Atom.eval { store := fun x => 0, heap := Heap.singleton 0 3 }.store (Atom.const 5)) }.heap\nh5 :\n  ptsAtLeast 0 5\n    { store := { store := fun x => 0, heap := Heap.singleton 0 3 }.store,\n        heap :=\n          { store := fun x => 0, heap := Heap.singleton 0 3 }.heap.write 0\n            (Atom.eval { store := fun x => 0, heap := Heap.singleton 0 3 }.store (Atom.const 5)) }.store\n    { store := { store := fun x => 0, heap := Heap.singleton 0 3 }.store,\n        heap :=\n          { store := fun x => 0, heap := Heap.singleton 0 3 }.heap.write 0\n            (Atom.eval { store := fun x => 0, heap := Heap.singleton 0 3 }.store (Atom.const 5)) }.heap\n⊢ False"},
         {t:'p', h:"The two hypotheses differ in one character, at the front. The <code>have</code> reads through all of it, because a definitional restatement compares terms rather than displays."}
       ]}
     ],

     pitfall:"Supplying a heap that does not satisfy the precondition. <code>Heap.empty</code> is the tempting choice — it is the simplest heap there is — and the application is then rejected at the third argument, because <code>singleton_same 0 3</code> proves a fact about a different heap:<br><br><code>error: Application type mismatch: The argument<br>&nbsp;&nbsp;singleton_same 0 3<br>has type<br>&nbsp;&nbsp;Heap.singleton 0 3 0 = some 3<br>but is expected to have type<br>&nbsp;&nbsp;ptsAtLeast 0 3 (fun x => 0) Heap.empty</code><br><br>Read the last line as the bill: whatever heap you hand over, you owe a proof that it holds 3 at 0, and the empty heap cannot pay. The second common stall is skipping <code>cases hex</code> and reaching straight for <code>simp [ptsAtLeast] at h3</code>. That does unfold the assertion, leaving <code>h3 : s&#39;.heap 0 = some 3</code> — and then stops, with <code>error: unsolved goals</code>, because <code>s&#39;</code> is a variable and nothing can be computed about it. The final state has to be extracted from the run before any lookup means anything.<br><br>The third is the one the <code>have</code> exists to prevent. With <code>cases hex</code> done, <code>h3</code> is a claim about exactly the right heap, so <code>rw [write_same] at h3</code> looks like the next move. It fails:<br><br><code>error: Tactic `rewrite` failed: Did not find an occurrence of the pattern<br>&nbsp;&nbsp;Heap.write ?h ?l ?v ?l<br>in the target expression<br>&nbsp;&nbsp;ptsAtLeast 0 3<br>&nbsp;&nbsp;&nbsp;&nbsp;{ store := { store := fun x =&gt; 0, heap := Heap.singleton 0 3 }.store, …</code><br><br>The pattern is a write <i>applied to an address</i>: <code>Heap.write ?h ?l ?v</code> followed by <code>?l</code> again. No such application is in <code>h3</code>. The head of <code>h3</code> is <code>ptsAtLeast</code>, and the lookup only appears once <code>ptsAtLeast</code> is unfolded — which <code>rw</code> will not do, because it matches the term as written rather than up to definitions. The <code>have</code> is precisely the step that does the unfolding, and against <code>e3</code> the identical rewrite fires.",

     variants:"<b>Same value in both conjuncts.</b> Instantiate at <code>a = b</code> and there is no counterexample to find, because the instance is true — the write makes the address hold the value the precondition already claimed for it, so both conjuncts hold and the triple is provable in three lines:<br><br><code>theorem same_value_is_no_counterexample (l : Loc) (a : Val) :<br>&nbsp;&nbsp;&nbsp;&nbsp;Hoare (ptsAtLeast l a) (.write l (.const a))<br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(aAnd (ptsAtLeast l a) (ptsAtLeast l a)) := by<br>&nbsp;&nbsp;intro σ h ha<br>&nbsp;&nbsp;refine ⟨⟨σ, Heap.write h l a⟩, Exec.write ha, ?_, ?_⟩ &lt;;&gt;<br>&nbsp;&nbsp;&nbsp;&nbsp;exact write_same h l a</code><br><br>So the disagreement of the two values is load-bearing and the aliasing alone is not. <b>Distinct addresses.</b> Instantiate at <code>l₁ ≠ l₂</code> and the rule is still false, for a reason that has nothing to do with aliasing — the main line below has the counterexample. <b>Drop the negation.</b> The statement without <code>¬</code> is the rule itself, and no proof exists; the closest true statement is the repaired rule further down the page, which needs two additions before it holds."
    },

    /* ============================================ what the proof used ==== */

    {t:'p', h:"<code>h5</code> is never used. It is true — the write did make 0 hold 5 — and it is the conjunct that is <i>not</i> the problem. What the write broke is the conjunct the rule carried across for free, and that asymmetry is the content of the counterexample: the rule&rsquo;s mistake is not what it concluded about <code>l₂</code>, it is what it preserved about <code>l₁</code>."},

    {t:'p', h:"There is a second refutation, and it never looks at the run. <code>h3</code> and <code>h5</code> are two claims about the same final heap at the same address, so they contradict each other whatever the command did:"},

    {t:'code', tag:'illustration',
     cap:'The same theorem, refuted without inverting the run. The run is discarded; the state it produced is not.',
     src:"theorem refuted_at_the_postcondition :\n    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),\n        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))\n              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))) := by\n  intro hall\n  obtain ⟨s', _, h3, h5⟩ :=\n    hall 0 0 3 5 (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)\n  have e3 : s'.heap 0 = some 3 := h3\n  have e5 : s'.heap 0 = some 5 := h5\n  rw [e3] at e5\n  exact absurd e5 (by simp)"},

    {t:'p', h:"Two proofs of one theorem, denying different things. This one says the postcondition is unsatisfiable: no state anywhere makes it true, so every triple that ends in it and has a precondition some heap satisfies is false. That is Unit 00&rsquo;s <code>x02</code> with the quantifiers restored. The shipped proof says something narrower and more useful — it exhibits the memory the command actually produced and points at the conjunct that failed in it. Only the second tells you what to repair."},

    /* ================================================ the repair ==== */

    {t:'h3', s:'The repair from the first page'},

    {t:'p', h:"Unit 00&rsquo;s repair was a hypothesis: require that the two addresses differ. Written in front of the quantified statement, it does not save the rule."},

    {t:'code', tag:'illustration',
     cap:'The rule with the disequality assumed, and a counterexample to it in which the two addresses are 0 and 1.',
     src:"theorem distinct_addresses_do_not_save_it :\n    ¬ (∀ (l₁ l₂ : Loc) (a b : Val), l₁ ≠ l₂ →\n        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))\n              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))) := by\n  intro hall\n  obtain ⟨s', hex, _⟩ :=\n    hall 0 1 3 5 (by simp) (fun _ => 0) (Heap.singleton 0 3) (singleton_same 0 3)\n  cases hex with\n  | write hl => exact absurd hl (by simp [Heap.singleton])"},

    {t:'p', h:"There is no aliasing in that counterexample. The starting heap holds 3 at address 0 and nothing at address 1, and the command cannot run: <code>Exec.write</code> fires only from a state in which the address being written is already mapped. <code>Hoare</code> promises a final state, so a command with nowhere to go refutes the triple before any postcondition is examined. Inverting the run leaves its premise standing as a hypothesis — the starting heap is <code>some</code> at 1 — and the singleton heap is <code>none</code> there."},

    {t:'p', h:"That is a defect of the rule, not of the model. On paper, <code>{[x] = 3} [y] := 5 {…}</code> is written with both cells tacitly assumed to exist, and the precondition mentions one of them. Writing the rule in a language whose triples must produce a final state makes the omission visible: the honest classical rule needs two additions, not the one Unit 00 proposed."},

    {t:'code', tag:'illustration',
     cap:'The classical rule, repaired. Seven lines of proof, and two additions to the statement: the disequality, and an existential whose only job is to say that the cell being written is there at all.',
     src:"theorem classical_rule_repaired (l₁ l₂ : Loc) (a b : Val) (hne : l₁ ≠ l₂) :\n    Hoare (aAnd (ptsAtLeast l₁ a) (aExists (fun old => ptsAtLeast l₂ old)))\n          (.write l₂ (.const b))\n          (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b)) := by\n  intro σ h ⟨ha, old, hold⟩\n  refine ⟨⟨σ, Heap.write h l₂ b⟩, Exec.write hold, ?_, ?_⟩\n  · show Heap.write h l₂ b l₁ = some a\n    rw [write_other h l₂ l₁ b hne]\n    exact ha\n  · show Heap.write h l₂ b l₂ = some b\n    exact write_same h l₂ b"},

    {t:'p', h:"The rule is now sound, and its two halves are the two lookup laws of Unit 05: <code>write_other</code> carries the fact about <code>l₁</code> across, and that is the line where the disequality is spent; <code>write_same</code> supplies the fact about <code>l₂</code>. The existential in the precondition does nothing in the postcondition and nothing in the program. It is there because a rule that writes to an address has to guarantee the address is there, and this precondition is the only place it can say so."},

    {t:'detail', title:'The two holes, and what <code>show</code> does to them', tag:'aside', blocks:[
      {t:'p', h:"The <code>intro</code> line takes the store, the heap, and then three names out of a two-conjunct precondition: <code>ha</code> from the left, then <code>old</code> and <code>hold</code> from the existential on the right, which flattens exactly as the postcondition did in <code>x55</code>. What is left is the goal below. <code>refine</code> then hands over the final state and the run, and leaves the two conjuncts of the postcondition as holes."},
      {t:'trace', title:'The first branch of <code>classical_rule_repaired</code>',
       start:"⊢ ∃ s',\n    Exec (Cmd.write l₂ (Atom.const b)) { store := σ, heap := h } s' ∧\n      aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b) s'.store s'.heap",
       steps:[
         {tac:'refine ⟨⟨σ, Heap.write h l₂ b⟩, Exec.write hold, ?_, ?_⟩',
          state:'case refine_1\n⊢ ptsAtLeast l₁ a { store := σ, heap := h.write l₂ b }.store { store := σ, heap := h.write l₂ b }.heap',
          h:"The first hole. The second is the same display with <code>ptsAtLeast l₂ b</code> in front. Hypotheses are dropped from the displays here and nothing else is; these are <code>trace_state</code> output with the line-and-column prefix removed. Naming the final state is the whole of the decision — the postcondition has to be checked at the heap the command produced, and <code>Exec.write</code>&rsquo;s conclusion says which heap that is."},
         {tac:'show Heap.write h l₂ b l₁ = some a',
          state:'case refine_1\n⊢ h.write l₂ b l₁ = some a',
          h:"The same goal, displayed differently: <code>ptsAtLeast</code> is unfolded and the projections are gone, so <code>write_other</code> has a term to match against. Without the <code>show</code> the rewrite fails, for the reason <code>x55</code>&rsquo;s third pitfall gives."}
       ]}
    ]},

    {t:'p', h:"Unit 00 priced the disequality and the price has not changed. What this rule adds is the shape of the trouble. Its precondition describes memory it shares with everybody, so every fact it wants to carry forward needs its own permit — a hypothesis for the cell it does not touch, an existential for the cell it does — and the connective joining them, <code>aAnd</code>, supplies neither. Carrying <code>k</code> facts across costs <code>k</code> permits, written into the statement of the rule before anyone knows what the facts are."},

    /* ====================================== the separating version ==== */

    {t:'sec', s:'The same specification, with ∗'},

    {t:'p', h:"Two substitutions. <code>ptsAtLeast</code> becomes <code>↦</code>, which is Unit 07&rsquo;s question answered by Unit 13: the assertion stops being a fact about shared memory and becomes a claim to own exactly one cell. <code>aAnd</code> becomes <code>∗</code>, which is Unit 14: the conjunction stops handing the whole heap to both sides and starts dividing it between them."},

    {t:'code', tag:'verified',
     cap:'The separating replacement. The written value is a literal 5, which keeps this a specification of one concrete command rather than a rule schema; nothing in the proof depends on that.',
     src:"theorem separated_write_ok (l₁ l₂ : Loc) (a b : Val) :\n    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a))"},

    {t:'p', h:"There are no hypotheses. Both of the ones the repaired classical rule needed are consequences of the precondition. The command runs, because <code>l₂ ↦ b</code> says the left piece of memory <i>is</i> <code>Heap.singleton l₂ b</code>, so <code>l₂</code> is mapped in it and therefore in the union. And the two addresses differ, because the disjointness of two one-cell heaps is exactly that — which is Unit 17&rsquo;s theorem, and it applies to this precondition with nothing in between:"},

    {t:'code', tag:'illustration',
     cap:'<code>two_cells_distinct</code>, instantiated at the precondition of the theorem above. The proof is the theorem.',
     src:"theorem the_side_condition_is_in_the_precondition (l₁ l₂ : Loc) (a b : Val) :\n    (l₂ ↦ b) ∗ (l₁ ↦ a) ⊢ fact (fun _ => l₂ ≠ l₁) :=\n  two_cells_distinct l₂ l₁ b a"},

    {t:'p', h:"The disequality has not left the mathematics. It has moved from the hypotheses of the rule into the precondition of the specification, where it is derived rather than assumed — and where a caller who supplies the precondition has already supplied it, without being asked and without knowing it was wanted."},

    /* ---------------------------------------------------------------- x56 --- */

    {t:'ex',
     id:'x56',
     name:'separated_write_ok',

     why:"The contrast is the lesson, and this side of it is meant to be short. You have just spent eight lines refuting a rule; the same specification, written with <code>∗</code>, is four lines and every one of them names a theorem you have already proved. What it buys beyond the contrast is the shape: prove the specification on the cells the command touches, then frame everything else on. Every verification in the rest of the course has that shape, and Unit 29 turns it into a fixed sequence of four moves.",

     setup:"Nothing new is in scope. <code>hoare_write</code> is Unit 23, <code>hoare_frame</code> is Unit 27, and its two side hypotheses are discharged by <code>heapLocal_write</code> from Unit 25 and by <code>preserves_of_heapOnly</code> with <code>heapOnly_pointsTo</code> from Unit 24. No heap appears in the finished proof.",

     goal:"theorem separated_write_ok (l₁ l₂ : Loc) (a b : Val) :\n    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a)) := by\n  sorry",

     hints:[
       "Read the goal as a claim about two cells. The precondition <code>(l₂ ↦ b) ∗ (l₁ ↦ a)</code> owns exactly two: <code>l₂</code> holding <code>b</code> and <code>l₁</code> holding <code>a</code>, in disjoint pieces of memory. The postcondition owns exactly the same two, with <code>l₂</code> now holding 5. Between them stands one command, which names <code>l₂</code> and does not name <code>l₁</code> — and <code>l₁ ↦ a</code> is character for character the same on both sides of the triple.",
       "An assertion that is untouched on both sides of a triple is a frame, and there is a rule for lifting a specification over a frame. So the argument is in two steps: state the specification of this command on the memory it actually touches — the single cell <code>l₂</code> — and then lift it. The lifting needs two facts about the command that are nothing to do with this specification: that it is local, and that it leaves the frame alone.",
       "The small specification is <code>hoare_write</code>. The lifting is <code>hoare_frame</code>, whose three arguments are that specification, a proof of <code>HeapLocal</code> for this command, and a proof of <code>Preserves</code> for this frame. <code>heapLocal_write</code> gives the first. For the second, <code>preserves_of_heapOnly</code> reduces <code>Preserves</code> to <code>HeapOnly</code>, and <code>heapOnly_pointsTo</code> discharges that.",
       "Name the small specification first: <code>have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) := hoare_write l₂ (.const 5) b</code>. The goal is unchanged by it. The type you wrote is not the one <code>hoare_write</code> prints — its postcondition is <code>fun σ h => (l₂ ↦ Atom.eval σ (Atom.const 5)) σ h</code> — and Lean accepts the restatement because evaluating a constant gives 5 and the two are the same term. What remains is one <code>exact</code> applying <code>hoare_frame</code> to <code>base</code> and the two facts about the command."
     ],

     sol:"theorem separated_write_ok (l₁ l₂ : Loc) (a b : Val) :\n    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a)) := by\n  have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) :=\n    hoare_write l₂ (.const 5) b\n  exact hoare_frame base (heapLocal_write l₂ (.const 5))\n    (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))",

     solNote:"The <code>have</code> is not required: the one-<code>exact</code> form, with <code>hoare_write l₂ (.const 5) b</code> written in place of <code>base</code>, compiles. It is written out because it is the renormalisation step — the point where the postcondition <code>hoare_write</code> states is restated in the form the frame rule&rsquo;s conclusion will show — and hiding it inside an application is how a four-line proof becomes unreadable at four commands.",

     expl:"The frame rule takes a specification of the cell the command touches and returns the same specification beside anything else, provided the command is local and leaves that anything else alone. Here the anything else is one cell, the locality is Unit 25&rsquo;s theorem about <code>write</code>, and the preservation is free because the frame does not mention the store. The frame <code>R</code> is never written down: it is determined by matching <code>hoare_frame</code>&rsquo;s conclusion <code>Hoare (P ∗ R) c (Q ∗ R)</code> against the goal.",

     walk:[
       {tac:'have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) := hoare_write l₂ (.const 5) b',
        h:"Leaves the goal untouched and adds one hypothesis: the specification of this command on the one cell it writes. The three arguments to <code>hoare_write</code> are the address, the expression being written, and the value that was there before. The stated type differs from the printed type of <code>hoare_write</code> in two respects — <code>Atom.eval σ (Atom.const 5)</code> has been computed to <code>5</code>, and the eta-expanded postcondition has been contracted — and neither is a change of term, so the ascription is accepted."},
       {tac:'exact hoare_frame base (heapLocal_write l₂ (.const 5)) (preserves_of_heapOnly _ (heapOnly_pointsTo l₁ a))',
        h:"Closes the goal. <code>hoare_frame</code>&rsquo;s first argument is the specification being lifted; its conclusion is <code>Hoare (P ∗ R) c (Q ∗ R)</code>, and unifying that with the goal fixes <code>R</code> to be <code>l₁ ↦ a</code>. The second argument is locality, which is a fact about the command alone. The third is <code>Preserves</code>, which is a fact about the command <i>and</i> this frame; <code>preserves_of_heapOnly</code> discharges it for any frame that does not read the store, and <code>heapOnly_pointsTo</code> says <code>↦</code> is such a frame. The <code>_</code> is the command, fixed by the expected type."}
     ],

     deep:[
       {t:'trace', title:'separated_write_ok, tactic by tactic',
        start:'l₁ l₂ : Loc\na b : Val\n⊢ Hoare (l₂ ↦ b ∗ l₁ ↦ a) (Cmd.write l₂ (Atom.const 5)) (l₂ ↦ 5 ∗ l₁ ↦ a)',
        steps:[
          {tac:'have base : Hoare (l₂ ↦ b) (.write l₂ (.const 5)) (l₂ ↦ 5) := hoare_write l₂ (.const 5) b',
           state:'l₁ l₂ : Loc\na b : Val\nbase : Hoare (l₂ ↦ b) (Cmd.write l₂ (Atom.const 5)) (l₂ ↦ 5)\n⊢ Hoare (l₂ ↦ b ∗ l₁ ↦ a) (Cmd.write l₂ (Atom.const 5)) (l₂ ↦ 5 ∗ l₁ ↦ a)',
           h:"One line added, goal identical. The difference between <code>base</code> and the goal is <code>∗ l₁ ↦ a</code> on both sides, and that difference is exactly what the frame rule closes. Displays are <code>trace_state</code> output with the line-and-column prefix dropped."}
        ],
        done:'No goals.'},

       {t:'p', h:"What the proof does not contain is the point. No heap, no <code>Heap.union</code>, no <code>Heap.disjoint</code>, no <code>Exec</code>, no lookup, and no mention of the fact that <code>l₁</code> and <code>l₂</code> are different addresses. The disequality is used — a heap satisfying the precondition splits into two disjoint cells, which forces it — but it is used inside <code>hoare_frame</code>&rsquo;s proof and inside <code>heapLocal_write</code>&rsquo;s, both of which were finished before this page began."},

       {t:'p', h:"The theorem is also an instance of one you have already proved. Unit 27&rsquo;s <code>write_with_frame</code> is the same statement with the written value left as a variable too, so the whole proof can be replaced by an application:"},

       {t:'code', tag:'illustration',
        cap:'The same theorem, in one term. What is proved is identical; what is shown is less.',
        src:"theorem separated_write_one_line (l₁ l₂ : Loc) (a b : Val) :\n    Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a)) (.write l₂ (.const 5)) ((l₂ ↦ 5) ∗ (l₁ ↦ a)) :=\n  write_with_frame l₂ l₁ b 5 a"},

       {t:'p', h:"That is worth knowing and is not the version to keep, because the four-line proof is the one whose steps generalise. Unit 29 applies exactly those steps to commands for which no <code>write_with_frame</code> has been proved in advance."}
     ],

     pitfall:"Getting <code>hoare_write</code>&rsquo;s third argument wrong. It is the value the cell held <i>before</i> the write, and the two values in sight are <code>b</code> and 5, so <code>hoare_write l₂ (.const 5) 5</code> is an easy slip. It is a well-formed term — it specifies writing 5 over 5 — and the ascription on <code>base</code> is what catches it:<br><br><code>error: Type mismatch<br>&nbsp;&nbsp;hoare_write l₂ (Atom.const 5) 5<br>has type<br>&nbsp;&nbsp;Hoare (l₂ ↦ 5) (Cmd.write l₂ (Atom.const 5)) fun σ h =&gt; (l₂ ↦ Atom.eval σ (Atom.const 5)) σ h<br>but is expected to have type<br>&nbsp;&nbsp;Hoare (l₂ ↦ b) (Cmd.write l₂ (Atom.const 5)) (l₂ ↦ 5)</code><br><br>The <i>pre</i>conditions are where the two disagree — <code>l₂ ↦ 5</code> against <code>l₂ ↦ b</code> — which is the tell that the argument named the wrong end of the write. The message&rsquo;s other half earns a second reading: it is the only place on this page where <code>hoare_write</code>&rsquo;s postcondition appears as Lean stores it, eta-expanded with <code>Atom.eval</code> uncomputed, and replacing that display with <code>l₂ ↦ 5</code> is the whole job of the <code>have</code>.<br><br>The second is handing <code>heapOnly_pointsTo l₁ a</code> straight to <code>hoare_frame</code>, without <code>preserves_of_heapOnly</code>. The two conditions are about different things — one is a property of an assertion, the other a property of a command paired with an assertion — and the message says so:<br><br><code>error: Application type mismatch: The argument<br>&nbsp;&nbsp;heapOnly_pointsTo l₁ a<br>has type<br>&nbsp;&nbsp;HeapOnly (l₁ ↦ a)<br>but is expected to have type<br>&nbsp;&nbsp;Preserves (Cmd.write l₂ (Atom.const 5)) (l₁ ↦ a)</code><br><br>The bridge between them is one implication, and it is one-way. Unit 24&rsquo;s <code>not_heapOnly_pure</code> exhibits an assertion that is not heap-only, and <code>write</code> preserves it anyway, because <code>write</code> does not touch the store:<br><br><code>theorem preserves_without_heapOnly (l : Loc) (e : Atom) (φ : Store → Prop) :<br>&nbsp;&nbsp;&nbsp;&nbsp;Preserves (.write l e) (pure φ) := by<br>&nbsp;&nbsp;intro s s' hex hFrame hr<br>&nbsp;&nbsp;cases hex<br>&nbsp;&nbsp;exact hr</code>",

     variants:"<b>Swap the two conjuncts.</b> State it as <code>(l₁ ↦ a) ∗ (l₂ ↦ b)</code> before and <code>(l₁ ↦ a) ∗ (l₂ ↦ 5)</code> after, and the same proof is rejected: <code>hoare_frame</code> puts the frame on the <i>right</i>, so what it produces is the star the other way round.<br><br><code>error: Type mismatch<br>…<br>has type<br>&nbsp;&nbsp;Hoare (l₂ ↦ b ∗ l₁ ↦ a) (Cmd.write l₂ (Atom.const 5)) (l₂ ↦ 5 ∗ l₁ ↦ a)<br>but is expected to have type<br>&nbsp;&nbsp;Hoare (l₁ ↦ a ∗ l₂ ↦ b) (Cmd.write l₂ (Atom.const 5)) (l₁ ↦ a ∗ l₂ ↦ 5)</code><br><br>The repair is <code>hoare_consequence</code> with <code>star_comm</code> on each side, and the cost of that repair is why Unit 29 has a name for that kind of reshaping and a lemma to shorten it with. <b>Take the two addresses to be equal.</b> The theorem still holds, and says nothing: <code>star_same_loc_absurd</code> shows that no state satisfies its precondition, so the triple is vacuous.<br><br><code>theorem no_heap_satisfies_the_aliased_precondition<br>&nbsp;&nbsp;&nbsp;&nbsp;(l : Loc) (a b : Val) (σ : Store) (h : Heap) :<br>&nbsp;&nbsp;&nbsp;&nbsp;¬ ((l ↦ b) ∗ (l ↦ a)) σ h :=<br>&nbsp;&nbsp;fun hp => star_same_loc_absurd l b a σ h hp</code><br><br>That is what it means for the side condition to live in the precondition. The classical rule had to exclude the aliased case by hypothesis, and could not do so without naming both addresses; this one excludes it by having no instances there. <b>Drop the locality argument</b> and there is no proof: <code>hoare_frame</code> has three explicit hypotheses and Lean will report the missing one rather than guess it."
    },

    /* ================================================== the comparison ==== */

    {t:'p', h:"Both theorems are now on the page, and they are the same specification of the same command under two readings of what an assertion is. Both ask the caller for the same two cells. Set them beside each other and count what else: eight lines against four, two additions against none, and — in the second — no heap, no run, and no mention anywhere of the fact that the two addresses are different."},

    {t:'cmp',
     left:{t:'The classical rule', kind:'bad',
           h:"Assertions are facts about a memory everybody shares, joined by <code>aAnd</code>. Stated as written, it is <b>false</b>, refuted in eight lines. Made true, it needs <b>two things the statement does not say</b>: that the two addresses differ, as a hypothesis of the rule, and that <code>l₂</code> is allocated, as an existential bolted onto the precondition — because <code>ptsAtLeast</code> cannot say a cell is there without also saying what is in it. Neither is about what the command does. The conclusion alone, re-broken to fit the column:",
           tag:'sketch',
           src:"Hoare (aAnd (ptsAtLeast l₁ a)\n             (aExists (fun old => ptsAtLeast l₂ old)))\n      (.write l₂ (.const b))\n      (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b))"},
     right:{t:'The separating rule', kind:'good',
            h:"Assertions own memory, and <code>∗</code> divides it. Stated as written it is <b>true</b>, proved in four lines, and it adds <b>nothing</b>. The existence of the written cell is what <code>l₂ ↦ b</code> says. The disequality is what the disjointness inside <code>∗</code> says, recoverable as a proposition by <code>two_cells_distinct</code>. Neither has to be stated, because supplying the precondition supplies both. The conclusion alone, in the same layout:",
            tag:'sketch',
            src:"Hoare ((l₂ ↦ b) ∗ (l₁ ↦ a))\n      (.write l₂ (.const 5))\n      ((l₂ ↦ 5) ∗ (l₁ ↦ a))"}},

    {t:'note', kind:'key', title:'The difference, in one sentence',
     h:"The classical rule can be repaired one cell at a time, as it was above, but not in general — the side condition it needs is about the cells its caller happens to be holding, and a rule fixed at two conjuncts has no vocabulary for those; the separating rule needs no side condition at all, because supplying its precondition supplies every disequality the proof uses."},

    /* =============================================== the ledger ==== */

    {t:'sec', s:'What is settled'},

    {t:'p', h:"The two theorems above are the ends of one chain, and every link in it was proved rather than assumed. The middle column is where each link was made."},

    {t:'tbl', cap:'Unit numbers are the badge numbers in the sidebar.',
     head:['What had to be true', 'Where it was settled'],
     rows:[
       ['Memory is an object that can be split into disjoint pieces and rejoined, and the splitting has the algebra of a partial commutative monoid', 'Units 05&ndash;11'],
       ['An assertion can claim to <i>own</i> memory rather than to describe it: <code>↦</code>', 'Unit 13'],
       ['A conjunction can divide memory between its conjuncts, and it has no projection and no duplication: <code>∗</code>', 'Unit 14'],
       ['There is a language with commands that read, write and free, and a semantics saying what running one does', 'Units 18&ndash;19'],
       ['A triple says what it says, and the rules that do not touch memory follow from the definition', 'Unit 22'],
       ['Each memory rule mentions only the cells its command touches', 'Unit 23'],
       ['Every command in the language is local: what it does inside a bigger heap is what it does inside a small one, with the rest carried along', 'Units 24&ndash;26'],
       ['A command correct on the memory it owns is correct inside any larger heap: <code>hoare_frame</code>', 'Unit 27'],
       ['The rule from the first page is false, and its separating replacement is true and needs no side condition', 'this unit']
     ]},

    {t:'note', kind:'warn', title:'Three things this course does not do',
     h:"<b>No command creates a cell.</b> Every heap here is given, and the language has no way to obtain a fresh address. That is not a detail: a command that produces a new address has to choose one, and whether it can be proved local depends on how the choice is constrained — the one place in this development where the frame rule is genuinely at risk. Unit 38 takes it up. <b>Nothing runs concurrently.</b> The semantics is a relation between a starting state and a finishing one, and two commands sharing memory are outside it. Unit 38 sketches the generalisation and names what licenses it: the algebra of memory established in Unit 10, which holds of permissions and tokens as well as of cells, so the connective and its laws survive the change of resource. <b>Addresses are literals.</b> <code>load</code>, <code>write</code> and <code>free</code> take a <code>Loc</code> written into the program text, not an expression, so no program here can follow a pointer. Unit 18 stated the decision and priced it; Unit 38 gives the one-line syntax change that removes it and shows that no theorem in the course inspects how an address was obtained."},

    {t:'dod', h:"You can read the statement left unproved on the first page and say what it claims, refute it by choosing an instance and reading the contradiction off the memory the command produced, and give a second refutation that never inverts the run — saying which of the two denies what. You can show that the disequality repair is not enough, exhibit a counterexample to it containing no aliasing at all, state the classical rule with both of the additions it needs and prove it. You can prove the same specification with <code>∗</code> in four lines and no additions at all, say where each of the two went, and name the theorem that recovers the disequality from the precondition. And you can list the chain of results the two proofs stand on, and the three things this development does not cover."},

    {t:'p', h:"The logic is sound and its central rule is proved. It is not yet a <i>method</i>: every verification so far has been two commands long, and each needed hand-chosen intermediate assertions and a chain of renormalisation. Making that routine is the next module."}

  ]
});
