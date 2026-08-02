registerChapter({
  id: 'interpreter',
  num: '21',
  phase: 'Phase 3 · Programs and their semantics',
  title: 'LAB — an interpreter, proved to agree',
  blurb: 'Optional, and off the critical path. A fuelled interpreter for the language, proved sound and complete against the relation, so that the semantics can be run instead of only reasoned about.',

  orient: {
    youWill: [
      'Say why an interpreter for a language with loops cannot recurse on the command, and how one extra argument restores termination.',
      'Read <code>run n c s = none</code> correctly: it says <i>no answer within this budget</i>, and it does not say the program faulted.',
      'Run a program with <code>#eval</code>, read the answer back, and close the corresponding theorem with <code>rfl</code>.',
      'Induct on the fuel rather than on the command, and say what <code>intro n</code> alone buys that <code>intro n c s s\' h</code> destroys.',
      'Choose between <code>simp [run]</code> and <code>simp only [run]</code> by a rule you can state, and name the three branches where the two differ.',
      'Read a hypothesis that displays as an unreduced <code>match</code> and recognise it as definitionally the equation you wanted.',
      'Prove monotonicity in the fuel, lift it to <code>≤</code> by inducting on a <i>proof</i> of <code>n ≤ m</code>, and reconcile two fuel bounds with <code>max</code>.',
      'Say what completeness does not give you, and exhibit a program for which no fuel is enough.'
    ],
    needs: [
      'Unit 20: <code>induction</code> on a number and on a derivation, and reading the induction hypothesis off the goal.',
      'Unit 19: <code>Exec</code> and its ten constructors, and <code>cases h : e with</code> in its saved-equation form.',
      'Unit 18: <code>Cmd</code>, <code>State</code>, <code>Store.set</code>, <code>Atom.eval</code>, <code>BExpr.eval</code>, <code>;;</code>, and the shrinking condition Lean checks for a recursive <code>def</code>.'
    ],
    payoff: 'Honestly: nothing later in the course depends on a line of it. What you get is a semantics you can execute — so a specification you doubt can be tested before it is proved — and one technique that appears nowhere else here: <code>induction</code> run over a proof of <code>n ≤ m</code>, which is the only inductive proposition in this course that the course did not declare.'
  },

  blocks: [

    /* ============================================== the relation is mute === */

    {t:'p', h:'Offer an answer and ask whether it agrees. Here is a program to ask about: cell 3 holds 7, variable 0 is where the program puts what it reads, and the two commands read the cell and write back one more than they found.'},

    {t:'code', cap:'A two-command program and a state to run it from. Both are ordinary definitions — <code>demoProg</code> is a value of type <code>Cmd</code>, built with the constructors of Unit 18, and <code>demoStart</code> is a pair of a store and a heap.',
     src:'def demoProg : Cmd := .load 0 3 ;; .write 3 (.plus (.var 0) (.const 1))\n\ndef demoStart : State := ⟨fun _ => 0, Heap.singleton 3 7⟩'},

    {t:'p', h:'<code>Exec demoProg demoStart s\'</code> is a proposition, one for each candidate <code>s\'</code>. Lean evaluates propositions when it can find a procedure that decides them, so the direct question is worth putting to it.'},

    {t:'code', tag:'sketch', cap:'This does not compile. The answer is the point.',
     src:'#eval Exec demoProg demoStart demoStart'},

    {t:'state', cap:'Lean\'s reply, minus a trailing <code>Hint:</code> line offering to turn on diagnostics. The position prefix on every message quoted in this unit is dropped, and every mid-proof goal state below came from <code>trace_state</code>. Where a state shows fewer hypotheses than Lean printed, the missing ones are unchanged from the state above it and the step says which; nothing shown is ever altered. All three conventions are stated once, here.',
     src:'failed to synthesize\n  Decidable (Exec demoProg demoStart demoStart)'},

    {t:'p', h:'No procedure is attached, and none can be read off the declaration. An inductive relation says what a derivation <i>is</i>; it does not say how to find one. The two <code>loop</code> rules are where that bites: <code>loopTrue</code> concludes a run of <code>.loop b c</code> from a run of <code>.loop b c</code>, so a search that works backwards through the rules may keep finding the same subgoal, and nothing in the declaration promises it stops.'},

    {t:'p', h:'The procedure has to be built separately and then connected. This unit builds <code>run</code>, a function that takes a budget and either returns a final state or gives up, and proves two theorems about it: every answer <code>run</code> gives is backed by a derivation, and every derivation is an answer <code>run</code> gives for a large enough budget. Together they say that the relation and the function pick out the same partial function from states to states — which is what makes it honest to test one and believe the other.'},

    {t:'note', kind:'warn', title:'This unit is optional',
     h:'Nothing after it uses <code>run</code>, <code>run_sound</code>, <code>run_mono</code>, <code>run_le</code> or <code>run_complete</code>. The Hoare logic of Unit 22 is built on <code>Exec</code>, the frame rule of Unit 27 is proved from <code>Exec</code>, and neither mentions an interpreter. A reader who goes to Unit 22 from here owes nothing. Four things are introduced below and used nowhere else in the course — <code>simpa … using</code>, <code>induction</code> on a proof of <code>≤</code>, <code>max</code>, and the two <code>Nat.le_max_*</code> lemmas — so skipping them costs you nothing on any later page either.'},

    /* ========================================================== the fuel === */

    {t:'sec', s:'A budget'},

    {t:'p', h:'Unit 19 wrote this interpreter as a function of the command and Lean refused it. The refusal was specific: the loop clause has to call itself at <i>the same command</i>, because running <code>.loop b c</code> once more is part of what running <code>.loop b c</code> means. No subterm of the input shrinks, so there is nothing to point Lean at.'},

    {t:'p', h:'The obvious repair is to supply the missing argument by hand: find a quantity that decreases and tell Lean, with <code>termination_by</code>, to measure the recursion by that. Nothing you offer can work, and the obstacle is not Lean. Every <code>def</code> Lean accepts is something that runs, so a total <code>Cmd → State → Option State</code> agreeing with <code>Exec</code> would be a procedure that takes any program and any input and reports, in finite time, whether that program halts — <code>some</code> for yes, <code>none</code> for no. The store holds unbounded natural numbers and the language has a loop, which between them are enough to encode any computation at all, so that procedure would decide the halting problem; nothing decides the halting problem. What is wrong is what is being asked for, not how the definition was written. The language does have programs that never stop, and one is built at the end of this unit.'},

    {t:'p', h:'What is available instead is to change the function being defined. Add an argument that has nothing to do with the program, whose only job is to be smaller at every recursive call, and let the function say <i>I ran out</i> when it hits zero. That argument is the <b>fuel</b>. Structural recursion on it is immediate: every clause below either does not recurse or recurses at <code>n</code> having matched <code>n + 1</code>.'},

    {t:'code', cap:'The interpreter. Eight command clauses and one for exhausted fuel.',
     src:'def run : Nat → Cmd → State → Option State\n  | 0,     _,            _ => none\n  | _ + 1, .skip,        s => some s\n  | _ + 1, .assign x e,  s => some ⟨Store.set s.store x (e.eval s.store), s.heap⟩\n  | _ + 1, .load x l,    s =>\n      match s.heap l with\n      | some v => some ⟨Store.set s.store x v, s.heap⟩\n      | none   => none\n  | _ + 1, .write l e,   s =>\n      match s.heap l with\n      | some _ => some ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩\n      | none   => none\n  | _ + 1, .free l,      s =>\n      match s.heap l with\n      | some _ => some ⟨s.store, Heap.erase s.heap l⟩\n      | none   => none\n  | n + 1, .seq c₁ c₂,   s =>\n      match run n c₁ s with\n      | some s\' => run n c₂ s\'\n      | none    => none\n  | n + 1, .ite b c₁ c₂, s =>\n      match b.eval s.store with\n      | true  => run n c₁ s\n      | false => run n c₂ s\n  | n + 1, .loop b c,   s =>\n      match b.eval s.store with\n      | true  =>\n          match run n c s with\n          | some s\' => run n (.loop b c) s\'\n          | none    => none\n      | false => some s'},

    {t:'anat', src:'def run : Nat → Cmd → State → Option State\n  | 0,     _,            _ => none\n  | _ + 1, .skip,        s => some s\n  | _ + 1, .assign x e,  s => some ⟨Store.set s.store x (e.eval s.store), s.heap⟩\n  | _ + 1, .load x l,    s =>\n      match s.heap l with\n      | some v => some ⟨Store.set s.store x v, s.heap⟩\n      | none   => none\n  | _ + 1, .write l e,   s =>\n      match s.heap l with\n      | some _ => some ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩\n      | none   => none\n  | _ + 1, .free l,      s =>\n      match s.heap l with\n      | some _ => some ⟨s.store, Heap.erase s.heap l⟩\n      | none   => none\n  | n + 1, .seq c₁ c₂,   s =>\n      match run n c₁ s with\n      | some s\' => run n c₂ s\'\n      | none    => none\n  | n + 1, .ite b c₁ c₂, s =>\n      match b.eval s.store with\n      | true  => run n c₁ s\n      | false => run n c₂ s\n  | n + 1, .loop b c,   s =>\n      match b.eval s.store with\n      | true  =>\n          match run n c s with\n          | some s\' => run n (.loop b c) s\'\n          | none    => none\n      | false => some s',
     parts:[
       {m:'Nat → Cmd → State → Option State', h:'Nothing forces the fuel into first place: Lean hunts for a shrinking argument across all of them and would find it wherever it sat. It is a choice, and it pays twice. Every clause then lines up with a fuel pattern on the left, which is what makes the next two rows readable — and every theorem below can be stated with the fuel quantified first, which is what lets their proofs introduce it alone.'},
       {m:'| 0,     _,            _ => none', h:'Out of fuel. The command and the state are not consulted, so both are <code>_</code>. This clause is the whole reason the definition is accepted, and it is also the reason the answer type is <code>Option State</code>: the function has to be allowed to decline.'},
       {m:'| _ + 1, .skip,        s => some s', h:'The fuel is matched only to establish that it is not zero, and never used, so it is <code>_ + 1</code> rather than <code>n + 1</code>. Five clauses look like this — the five commands that finish without running another command.'},
       {m:'| n + 1, .seq c₁ c₂,   s =>', h:'Here the fuel is named, because the clause spends it. <b>Both</b> halves are run at <code>n</code>, not one after the other out of a shared pot: fuel is a bound on the depth of the recursion, not a count of the steps taken. That is the choice which makes <code>max</code> rather than <code>+</code> the right way to combine two budgets later on.'},
       {m:'match run n c₁ s with', h:'The first half may decline, and then the whole sequence declines. This <code>match</code> is what a reader coming from a language with exceptions would write as a check-and-propagate, and it is why the <code>seq</code> case of every proof below opens by splitting on the result of the inner run.'},
       {m:'match s.heap l with', h:'The memory operations consult the heap and fail when the cell is absent, exactly as the corresponding <code>Exec</code> rules require a premise <code>s.heap l = some v</code>. A <code>match</code> on a variable does not reduce, so this expression will sit in a hypothesis unevaluated until something tells Lean what <code>s.heap l</code> is.'},
       {m:'run n (.loop b c) s\'', h:'The recursive call at the same command — the clause Lean would not accept without the fuel. It is at <code>n</code> while the clause matched <code>n + 1</code>, and that is all Lean needs.'},
       {m:'| false => some s', h:'A loop whose guard is false is finished. One unit is still needed to reach the clause, so <code>run 0 (.loop b c) s</code> is <code>none</code> however the guard evaluates, but nothing recursive is spent. Pairing this with <code>Exec.loopFalse</code> is the reason the guard is taken apart with <code>match … | true | false</code> and not with <code>if</code>.'}
     ]},

    {t:'p', h:'<code>none</code> now carries two entirely different messages, and the function does not distinguish them.'},

    {t:'code', tag:'illustration', cap:'Three <code>none</code>s. The first two are a healthy program that has not been given enough to work with; the third is a program reading a cell that was never allocated, and no budget will change it. All three close by <code>rfl</code>, because the fuel and the program are concrete and everything reduces.',
     src:'example : run 0 demoProg demoStart = none := by rfl\nexample : run 1 demoProg demoStart = none := by rfl\nexample : run 100 (Cmd.load 0 5) demoStart = none := by rfl'},

    {t:'p', h:'So <code>run n c s = none</code> is a statement about <code>n</code> at least as much as about <code>c</code>. It cannot be turned into a claim that the program faults, and the interpreter has no way to report a fault that a reader could trust. Every theorem below therefore has <code>run n c s = some s\'</code> as its hypothesis or its conclusion: the informative half of the answer is the half that says <i>yes, and here it is</i>.'},

    {t:'detail', title:'Why the guards are taken apart with <code>match</code> and not with <code>if</code>', tag:'aside', open:false, blocks:[
      {t:'p', h:'<code>b.eval s.store</code> is a <code>Bool</code>, and Lean does accept <code>if</code> on a <code>Bool</code>. The variant interpreter with the two guard clauses rewritten was written out in full and compiled, and so were the <code>ite</code> and <code>loop</code> cases of the soundness proof under it. Nothing breaks. The reason to prefer <code>match</code> is what the two forms put on the screen.'},
      {t:'code', tag:'sketch', cap:'The two clauses that change. The other seven are identical, and the whole 27-line variant compiles.',
       src:'  | n + 1, .ite b c₁ c₂, s => if b.eval s.store then runIf n c₁ s else runIf n c₂ s\n  | n + 1, .loop b c,   s =>\n      if b.eval s.store then\n        match runIf n c s with\n        | some s\' => runIf n (.loop b c) s\'\n        | none    => none\n      else some s'},
      {t:'p', h:'<code>if</code> wants a proposition and a way to decide it. Handed a <code>Bool</code>, Lean inserts the coercion that turns <code>b</code> into the proposition <code>b = true</code> and looks up the instance that decides it. So an equation the program never wrote appears in the program, and it is still there when a proof takes the guard apart.'},
      {t:'state', cap:'After <code>simp only [runIf] at h</code>, and then again after <code>cases hb : b.eval s.store with | true =&gt; rw [hb] at h</code>. Re-derived here; Edition 1 quoted a goal state for a declaration that is not in this repository, and where the two disagree this one wins.',
       src:'h : (if BExpr.eval s.store b = true then runIf n c₁ s else runIf n c₂ s) = some s\'\n\nh : (if true = true then runIf n c₁ s else runIf n c₂ s) = some s\''},
      {t:'p', h:'<code>if true = true then _ else _</code> does reduce — the instance that decides <code>true = true</code> computes — so <code>exact ih c₁ s s\' h</code> closes the branch under either spelling. What the <code>match</code> form buys is a one-for-one correspondence: <code>Bool</code> has two constructors, <code>Exec</code> has two rules for <code>.ite</code>, and the interpreter has two clauses. Writing <code>if</code> hides that behind an instance, and a reader comparing the interpreter with the relation line by line has one more thing to see through.'}
    ]},

    /* ==================================================== running it ====== */

    {t:'sec', s:'Running a program'},

    {t:'p', h:'Nothing says how much fuel <code>demoProg</code> needs. Choosing it is a matter of trying, which is a thing you can now do, because <code>run</code> is a function and <code>#eval</code> evaluates functions.'},

    {t:'code', tag:'illustration', cap:'The state itself cannot be printed — a heap is a function, and functions have no display — so the questions are put to its parts. <code>o.isSome</code> is <code>true</code> exactly when <code>o</code> is a <code>some</code>; <code>o.map f</code> applies <code>f</code> underneath a <code>some</code> and leaves a <code>none</code> alone, which is how the third line asks for two numbers out of a run that might not have happened.',
     src:'#eval (run 1 demoProg demoStart).isSome\n#eval (run 2 demoProg demoStart).isSome\n#eval (run 6 demoProg demoStart).map (fun s => (s.store 0, s.heap 3))'},

    {t:'state', cap:'Three lines of output. One unit of fuel is not enough for two commands; two units are; and by six the answer has settled — variable 0 holds the 7 that was read, and cell 3 holds 8.',
     src:'false\ntrue\nsome (7, some 8)'},

    {t:'p', h:'That last line is a claim about a closed term, so it is a claim <code>rfl</code> can settle. Turning it into a theorem is the first exercise, and the shortest one in this unit by a wide margin.'},

    {t:'ex',
     id: 'x47',
     name: 'run_example',
     hard: false,
     why: 'Everything else on this page is about trusting the interpreter. This is about using it. Two earlier exercises closed by <code>rfl</code> because a definition computes — <code>double 3 = 6</code> in Unit 02, a compound expression in Unit 18 — and this is the first where the thing that computes is a whole run of a program, heap included, with no hypothesis and no case split anywhere in it. The habit it builds — try the program before proving anything about it — is worth having wherever a specification is in doubt, and this is the only page in the course that can offer it, because <code>run</code> is not carried forward.',
     setup: 'The fuel is yours to choose. The <code>#eval</code> above says what the answer is; write it as a state and let Lean check the whole run.',
     goal: 'example : run 6 demoProg demoStart\n    = some ⟨Store.set demoStart.store 0 7, Heap.write demoStart.heap 3 8⟩ := by',
     hints: [
       'The goal is an equation between two values of type <code>Option State</code>. On the left, <code>run</code> applied to three closed terms. On the right, <code>some</code> applied to a state built from <code>demoStart</code>: its store with variable 0 set to 7, its heap with cell 3 set to 8. Nothing is quantified and nothing is hypothetical.',
       'Both sides are terms with no variables in them, so both sides compute. An equation between two things that compute to the same value needs no argument at all — it needs the observation that they do.',
       'The tactic is <code>rfl</code>. For this goal you do not have to tell it what to unfold: it looks through <code>run</code>, <code>demoProg</code> and <code>demoStart</code> on its own, so nothing like <code>simp [run]</code> or <code>simp [demoProg]</code> is needed in front of it.',
       'Write <code>:= by rfl</code> on the statement\'s last line, or <code>rfl</code> on the line after <code>:= by</code>. Either leaves no goals. If it does not, the tactic is not the problem: two closed terms genuinely failed to match, and the only movable parts are the fuel and the right-hand side.'
     ],
     sol: 'example : run 6 demoProg demoStart\n    = some ⟨Store.set demoStart.store 0 7, Heap.write demoStart.heap 3 8⟩ := by rfl',
     solNote: 'Six is not the smallest fuel that works; two is. Any budget from two upwards gives the same answer, and the theorem that says so is <code>run_mono</code>, three sections down. Until it is proved, the fact that <code>run 6</code> and <code>run 2</code> agree here is an observation about one program.',
     expl: 'The interpreter, the program, the starting state and the fuel are all closed terms, so <code>run 6 demoProg demoStart</code> is a term Lean can evaluate to a normal form by unfolding definitions and reducing <code>match</code>es. So is the right-hand side. They reduce to the same thing, and <code>rfl</code> is the tactic that checks exactly that.',
     walk: [
       {tac:'rfl', h:'Asked Lean to check that the two sides are definitionally equal. It unfolded <code>run</code>, <code>demoProg</code>, <code>demoStart</code>, <code>Cmd.seq</code>\'s clause, then the <code>load</code> clause against <code>Heap.singleton 3 7</code> at 3, then the <code>write</code> clause against the resulting store, evaluated <code>Atom.plus (.var 0) (.const 1)</code> to 8, and compared the two records field by field. No goals remained.'}
     ],
     deep: [
       {t:'trace', title:'One step, and what it faced',
        start:'⊢ run 6 demoProg demoStart = some { store := demoStart.store.set 0 7, heap := demoStart.heap.write 3 8 }',
        steps:[
          {tac:'rfl',
           state:'No goals.',
           h:'The anonymous constructor <code>⟨_, _⟩</code> in the statement is displayed back as <code>{ store := …, heap := … }</code>, which is how Lean prints a structure literal. The two spellings are the same term.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Six reductions of the fuel are available and two are used. Nothing in the statement records that, which is what makes fuel a bound and not a measurement: two different fuels that both suffice give the same answer, and neither is the answer.'}
     ],
     pitfall: 'Getting the arithmetic wrong — writing <code>Heap.write demoStart.heap 3 7</code>, on the grounds that 7 is what the cell held. The program adds one. What makes this worth naming is the error message: <code>Tactic `rfl` failed: The left-hand side run 6 demoProg demoStart is not definitionally equal to the right-hand side some { store := demoStart.store.set 0 7, heap := demoStart.heap.write 3 7 }</code>. That is the same message you get if you keep the 8 and ask for <code>run 1</code> instead of <code>run 6</code> — a wrong answer and an insufficient budget are reported identically, because in both cases two closed terms failed to match. The <code>#eval</code> above tells the two apart; <code>rfl</code> cannot.',
     variants: 'Replace <code>demoStart</code> by a state whose heap is a variable and the exercise stops being an exercise. Unfolding <code>run 6 demoProg s</code> gets as far as <code>match (match s.heap 3 with | some v =&gt; some { store := s.store.set 0 v, heap := s.heap } | none =&gt; none) with | some s\' =&gt; … | none =&gt; none</code> and stops: the innermost scrutinee is <code>s.heap 3</code>, an application of a variable, so that <code>match</code> is stuck and the outer one is waiting on it. <code>rfl</code> then refuses whatever you claim the answer is. That is not a defect in <code>rfl</code>; it is the difference between running a program and proving something about all runs of it, and it is why the rest of this unit is not one-line proofs. Replace the program by one containing a loop and <code>rfl</code> still works, provided the fuel covers every turn. Counting down from 2 — <code>Cmd.loop (.not (.equals (.var 0) (.const 0))) (.assign 0 (.minus (.var 0) (.const 1)))</code>, started from a store holding 2 at variable 0 — needs 3: one unit for each of the two turns that run the body, and one for the turn that finds the guard false. Its answer is two nested <code>Store.set</code>s; <code>run 2</code> of it is <code>none</code>; <code>run 7</code> of it is the same answer as <code>run 3</code>. All four claims were compiled.'
    },

    /* ============================================= soundness, in full ====== */

    {t:'sec', s:'The interpreter never lies'},

    {t:'p', h:'The first of the two theorems is soundness: if <code>run</code> hands back a state, there is a derivation to match. It is the direction that makes a test meaningful, because it says a green tick from the interpreter is evidence about the semantics rather than about the interpreter.'},

    {t:'code', cap:'The statement. Every variable is bound in front, including the fuel, and the reason for that is the next paragraph.',
     src:'theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\' := by'},

    {t:'p', h:'What to induct on. Not the command: the loop clause of <code>run</code> calls itself at the same command, so an induction hypothesis about the parts of <code>.loop b c</code> would not reach the recursive call. The fuel is the argument that shrinks, so the fuel is what to induct on — and then the command is taken apart with <code>cases</code> inside each branch, which is a case split rather than an induction and needs nothing to shrink.'},

    {t:'p', h:'That decides the first line of the proof. <code>intro n</code>, and nothing else. Everything after the fuel stays in the goal, so that the induction hypothesis quantifies over it.'},

    {t:'code', src:'  intro n\n  induction n with'},

    {t:'p', h:'Introducing the command and the state as well before inducting is the natural thing to type and it is fatal. Lean will still run the induction — hypotheses that mention <code>n</code> are reverted automatically — but the hypothesis it produces is fixed at the command and the states you introduced. The two forms differ in exactly one line of the context.'},

    {t:'cmp',
     left:{t:'After <code>intro n</code>, then <code>induction n</code>', kind:'good',
           h:'Quantified over every command and every pair of states, so it can be applied to <code>c₁</code>, to <code>c₂</code>, and at the intermediate state that the <code>seq</code> clause produces.',
           tag:'sketch',
           src:'ih : ∀ (c : Cmd) (s s\' : State),\n  run n c s = some s\' → Exec c s s\''},
     right:{t:'After <code>intro n c s s\' h</code>, then <code>induction n</code>', kind:'bad',
            h:'Fixed at the very command and states the goal is about. In the <code>seq</code> branch the goal is about <code>c₁ ;; c₂</code> and the hypothesis is about <code>c₁ ;; c₂</code>, so it says nothing about either half and the branch cannot be closed.',
            tag:'sketch',
            src:'ih : run n (c₁ ;; c₂) s = some s\' →\n  Exec (c₁ ;; c₂) s s\''},
     cap:'One line of context from each, extracted from the <code>seq</code> branch. Both are real; the fold below carries the two contexts entire.'},

    {t:'detail', title:'Both contexts in full, as Lean prints them', tag:'aside', open:false, blocks:[
      {t:'p', h:'The right-hand column above is the branch reached by <code>intro n c s s\' h</code>, <code>induction n with</code>, <code>| succ n ih =&gt;</code>, <code>cases c with</code>, <code>| seq c₁ c₂ =&gt;</code>, <code>simp only [run] at h</code>. The hypothesis <code>h</code> was reverted by <code>induction</code> because it mentions <code>n</code>, which is why it reappears as the antecedent of <code>ih</code>.'},
      {t:'state', src:'case succ.seq\ns s\' : State\nn : Nat\nc₁ c₂ : Cmd\nih : run n (c₁ ;; c₂) s = some s\' → Exec (c₁ ;; c₂) s s\'\nh :\n  (match run n c₁ s with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\n⊢ Exec (c₁ ;; c₂) s s\''},
      {t:'p', h:'The same branch of the real proof, where only the fuel was introduced. <code>ih</code> is now a statement about every command, and <code>c₁ ;; c₂</code> in the goal came from <code>cases c</code> rather than from a binder the reader chose.'},
      {t:'state', src:'case succ.seq\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nc₁ c₂ : Cmd\nh :\n  (match run n c₁ s with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\n⊢ Exec (c₁ ;; c₂) s s\''}
    ]},

    {t:'p', h:'Unit 20 called this generalising the induction hypothesis and did it with the word <code>generalizing</code>, on variables that were already introduced. Here the same effect is had by not introducing them, which is available because the statement was written with the fuel first.'},

    {t:'h3', s:'Nine branches, three shapes'},

    {t:'p', h:'The <code>zero</code> branch plus eight commands. They divide by what the corresponding clause of <code>run</code> returns, and the division decides both the tactic that opens the branch and whether the induction hypothesis is used at all.'},

    {t:'tbl', head:['branch', 'what the clause of <code>run</code> gives', 'how the branch opens', '<code>ih</code>?'],
     rows:[
       ['<code>zero</code>', '<code>none</code>, against a hypothesis saying <code>some s\'</code>', '<code>simp [run] at h</code>, which closes it', 'no'],
       ['<code>skip</code>, <code>assign</code>', 'a state, outright', '<code>simp [run] at h</code>, then build the rule', 'no'],
       ['<code>load</code>, <code>write</code>, <code>free</code>', 'a <code>match</code> on <code>s.heap l</code>', '<code>simp only [run] at h</code>, then <code>cases hl : s.heap l with</code>', 'no'],
       ['<code>seq</code>', 'a <code>match</code> on an inner run', '<code>simp only [run] at h</code>, then <code>cases hr : run n c₁ s with</code>', 'twice'],
       ['<code>ite</code>, <code>loop</code>', 'a <code>match</code> on the guard', '<code>simp only [run] at h</code>, then <code>cases hb : b.eval s.store with</code>', 'once or twice']
     ],
     cap:'The three shapes are the three groups of rows: answers outright, waits on the heap, waits on a sub-computation. Six of the nine branches never consult <code>ih</code> — the <code>zero</code> branch and five of the eight commands — which is why the worked example below can be lifted out of the proof and stated on its own.'},

    {t:'p', h:'The third column contains a choice made three times one way and six times the other, so it deserves a rule rather than a habit. <code>simp only [run] at h</code> rewrites <code>h</code> with the equations that define <code>run</code> and stops. <code>simp [run] at h</code> does that and then carries on with everything <code>simp</code> knows by default — including that <code>some a = some b</code> is <code>a = b</code>, and that <code>none = some b</code> is impossible.'},

    {t:'p', h:'So the two differ exactly where the default set has something to say, and that is exactly the three branches whose clause of <code>run</code> answers without a <code>match</code>. In the other six the clause leaves a <code>match</code> on a term <code>simp</code> cannot evaluate, both forms produce the same hypothesis, and <code>simp only</code> is written because the smaller claim is the true one. All nine branches were run both ways to check that.'},

    {t:'tbl', head:['branch', 'after <code>simp only [run] at h</code>', 'after <code>simp [run] at h</code>'],
     rows:[
       ['<code>zero</code>', '<code>h : none = some s\'</code>, goal still open', 'no goals: a false hypothesis proves anything'],
       ['<code>skip</code>', '<code>h : some s = some s\'</code>', '<code>h : s = s\'</code>'],
       ['<code>assign</code>', '<code>h : some { store := …, heap := … } = some s\'</code>', '<code>h : { store := …, heap := … } = s\'</code>'],
       ['the other six', 'a stuck <code>match</code>', 'the same stuck <code>match</code>']
     ],
     cap:'The only shapes on which the two tactics differ. The <code>assign</code> row is abbreviated in both columns by the same amount; the record is <code>{ store := s.store.set x (Atom.eval s.store e), heap := s.heap }</code>.'},

    {t:'p', h:'The equations that <code>simp only [run]</code> fires are generated when <code>run</code> is declared, one per clause, and they can be looked at.'},

    {t:'code', tag:'illustration', cap:'The fourth clause, as a theorem.',
     src:'#check @run.eq_4'},

    {t:'state', src:'run.eq_4 : ∀ (x : State) (n : Nat) (x_3 : Var) (l : Loc),\n  run n.succ (Cmd.load x_3 l) x =\n    match x.heap l with\n    | some v => some { store := x.store.set x_3 v, heap := x.heap }\n    | none => none'},

    {t:'p', h:'The right-hand side is a <code>match</code> with a variable scrutinee, so rewriting with this equation cannot make progress past it. Everything after it in the <code>load</code> branch is about supplying that scrutinee.'},

    {t:'h3', s:'Worked: the load branch'},

    {t:'p', h:'This is the branch to do in full, because the three memory operations share its shape and because it is where the display and the mathematics come apart. It uses nothing from the induction, so it can be stated on its own with the fuel as an ordinary variable, and the proof below is character for character the branch inside <code>run_sound</code>.'},

    {t:'code', tag:'illustration', cap:'The load branch, lifted out. Compiled on its own against everything the course has at this point.',
     src:'example (n : Nat) (x : Var) (l : Loc) (s s\' : State)\n    (h : run (n + 1) (Cmd.load x l) s = some s\') : Exec (Cmd.load x l) s s\' := by\n  simp only [run] at h\n  cases hl : s.heap l with\n  | none   => rw [hl] at h; simp at h\n  | some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl'},

    {t:'trace', title:'The load branch, tactic by tactic',
     start:'n : Nat\nx : Var\nl : Loc\ns s\' : State\nh : run (n + 1) (Cmd.load x l) s = some s\'\n⊢ Exec (Cmd.load x l) s s\'',
     steps:[
       {tac:'simp only [run] at h',
        state:'h :\n  (match s.heap l with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s\'\n⊢ Exec (Cmd.load x l) s s\'',
        h:'Every state from here on drops the four unchanged lines <code>n : Nat</code>, <code>x : Var</code>, <code>l : Loc</code>, <code>s s\' : State</code>, which sit above each of them, and shows the rest as Lean printed it. The clause has been substituted and the <code>match</code> is stuck, because <code>s.heap l</code> is an application of a variable. The plausible next move is <code>simp at h</code>, hoping to squeeze an equation out of it. That makes no progress: <code>simp</code> has nothing to say about a <code>match</code> whose scrutinee it cannot evaluate either.'},
       {tac:'cases hl : s.heap l with',
        state:'case none\nhl : s.heap l = none\n⊢ Exec (Cmd.load x l) s s\'\n\ncase some\nv : Val\nhl : s.heap l = some v\n⊢ Exec (Cmd.load x l) s s\'',
        h:'Two goals, shown one after the other with a blank line between them, and <code>h</code> dropped from both because it is untouched. Each carries the equation that says which branch it is. The split also substitutes into the <b>goal</b> wherever the goal mentions <code>s.heap l</code>, which here it does not — that substitution costs nothing in this branch and is what does the work in <code>run_mono</code> later. Hypotheses are never substituted into, which is why the next line exists. Written <code>cases s.heap l with</code>, without the <code>hl :</code>, this tactic accomplishes nothing whatever: <code>h</code> is untouched, the goal is untouched, and you get two identical goals differing only in a spare <code>v</code>.'},
       {tac:'rw [hl] at h  (the some branch)',
        state:'h :\n  (match some v with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s\'\n⊢ Exec (Cmd.load x l) s s\'',
        h:'The scrutinee is now a constructor, so the <code>match</code> is no longer stuck. The display has not caught up — Lean prints the term as written, not as reduced — but this hypothesis <i>is</i> <code>some { store := s.store.set x v, heap := s.heap } = some s\'</code>, and anything that wants the latter will accept it.'},
       {tac:'simp at h',
        state:'hl : s.heap l = some v\nh : { store := s.store.set x v, heap := s.heap } = s\'\n⊢ Exec (Cmd.load x l) s s\'',
        h:'Two jobs in one tactic: reduce the <code>match</code>, and strip the <code>some</code> from both sides. Neither needs <code>run</code>, which is why the lemma list is empty here.'},
       {tac:'rw [← h]',
        state:'⊢ Exec (Cmd.load x l) s { store := s.store.set x v, heap := s.heap }',
        h:'Rewriting right to left replaces <code>s\'</code> in the goal by the record. The goal is now the exact conclusion of <code>Exec.load</code>, with nothing left to unify. Rewriting the other way — <code>rw [h]</code> — has nothing to act on, since the record does not occur in the goal.'},
       {tac:'exact .load hl',
        state:'No goals.',
        h:'<code>Exec.load</code> takes one premise, a proof that the cell holds a value, and <code>hl</code> is that proof. The leading dot resolves the name against the expected type, which is headed by <code>Exec</code>.'}
     ],
     done:'No goals.'},

    {t:'p', h:'The <code>none</code> branch is two tactics for a different reason. After <code>rw [hl] at h</code> the hypothesis reads <code>(match none with | some v =&gt; … | none =&gt; none) = some s\'</code>, whose left side reduces to <code>none</code>; <code>simp at h</code> reduces it, sees <code>none = some s\'</code>, and closes the goal from the contradiction. The interpreter declining and the relation having no derivation are the same fact, and this is the line where they meet.'},

    {t:'detail', title:'Handing the unreduced <code>match</code> straight to a lemma', tag:'aside', open:false, blocks:[
      {t:'p', h:'The step after <code>rw [hl] at h</code> is where a reader most often stalls, because the hypothesis looks nothing like what is wanted. The display is the only obstacle. <code>Option.some.inj</code> takes a proof of <code>some a = some b</code> and returns a proof of <code>a = b</code>, and it accepts <code>h</code> as it stands, with the <code>match</code> unreduced and no simplification in between.'},
      {t:'code', tag:'illustration', cap:'Both compile. The first names the equation and rewrites with it; the second transports the derivation along it with <code>▸</code> and never mentions a goal state at all.',
       src:'example (n : Nat) (x : Var) (l : Loc) (s s\' : State)\n    (h : run (n + 1) (Cmd.load x l) s = some s\') : Exec (Cmd.load x l) s s\' := by\n  simp only [run] at h\n  cases hl : s.heap l with\n  | none   => rw [hl] at h; simp at h\n  | some v =>\n      rw [hl] at h\n      have heq : (⟨Store.set s.store x v, s.heap⟩ : State) = s\' := Option.some.inj h\n      rw [← heq]\n      exact .load hl\n\nexample (n : Nat) (x : Var) (l : Loc) (s s\' : State)\n    (h : run (n + 1) (Cmd.load x l) s = some s\') : Exec (Cmd.load x l) s s\' := by\n  simp only [run] at h\n  cases hl : s.heap l with\n  | none   => rw [hl] at h; simp at h\n  | some v => rw [hl] at h; exact Option.some.inj h ▸ Exec.load hl'},
      {t:'p', h:'The corpus proof uses <code>simp at h</code> because one tactic covers both the <code>none</code> branch and the <code>some</code> branch and the whole thing fits on a line. The version above is what to reach for when <code>simp</code> normalises something you needed left alone.'}
    ]},

    {t:'p', h:'The remaining branches are the same moves in different arrangements. <code>write</code> and <code>free</code> are the load branch with a different rule at the end; <code>seq</code>, <code>ite</code> and <code>loop</code> split on their own scrutinee and then apply <code>ih</code> once or twice.'},

    {t:'ex',
     id: 'm5-3',
     name: 'run_sound',
     hard: true,
     why: 'This is the theorem that makes the interpreter evidence rather than decoration, and it is the largest single proof in Module 4 — nine branches, six of them with a case split nested inside the induction branch, and one of those with a second split nested inside that. The technique it drills is definitional reduction: three times over, a hypothesis will display as something you did not ask for and be, underneath, exactly what you need.',
     setup: 'The fuel is introduced alone, then inducted on; inside the <code>succ</code> branch the command is taken apart with <code>cases c with</code>. Three of the nine branches — <code>zero</code>, <code>skip</code>, <code>assign</code> — are one line each, five are four lines each, and the <code>loop</code> branch is thirteen, because it is the only one that splits twice. Nothing is needed that is not on this page.',
     goal: 'theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\' := by',
     hints: [
       'The goal is a statement about every fuel, every command and every pair of states: if running <code>c</code> from <code>s</code> with budget <code>n</code> returns <code>s\'</code>, then <code>c</code> relates <code>s</code> to <code>s\'</code>. The hypothesis is an equation between two values of type <code>Option State</code>; the conclusion is a derivation you have to build.',
       'The recursion in <code>run</code> is on the fuel, so the induction is on the fuel. With zero fuel the hypothesis is false and the branch is free. With <code>n + 1</code>, the answer depends on which command it is, so split on the command: eight branches, nine counting the zero one. Only the three commands that run another command need the induction hypothesis, so in six of the nine it plays no part.',
       '<code>intro n</code> and then <code>induction n with</code>, followed inside the <code>succ</code> branch by <code>intro c s s\' h</code> and <code>cases c with</code>. In the six branches whose clause of <code>run</code> is a <code>match</code>, <code>simp only [run] at h</code> and then <code>cases</code> in its saved-equation form on whatever the <code>match</code> is looking at.',
       'The first three lines are <code>intro n</code>, <code>induction n with</code>, <code>| zero =&gt; intro c s s\' h; simp [run] at h</code>. That leaves the <code>succ</code> branch with <code>ih</code> quantified over every command and every pair of states, and the whole rest of the proof inside it.'
     ],
     sol: 'theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\' := by\n  intro n\n  induction n with\n  | zero => intro c s s\' h; simp [run] at h\n  | succ n ih =>\n    intro c s s\' h\n    cases c with\n    | skip => simp [run] at h; rw [← h]; exact .skip\n    | assign x e => simp [run] at h; rw [← h]; exact .assign\n    | load x l =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl\n    | write l e =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl\n    | free l =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl\n    | seq c₁ c₂ =>\n        simp only [run] at h\n        cases hr : run n c₁ s with\n        | none    => rw [hr] at h; simp at h\n        | some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s\' h)\n    | ite b c₁ c₂ =>\n        simp only [run] at h\n        cases hb : b.eval s.store with\n        | true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s\' h)\n        | false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s\' h)\n    | loop b c =>\n        simp only [run] at h\n        cases hb : b.eval s.store with\n        | false =>\n            rw [hb] at h\n            have hs : s = s\' := Option.some.inj h\n            subst hs\n            exact .loopFalse hb\n        | true  =>\n            rw [hb] at h\n            cases hr : run n c s with\n            | none    => rw [hr] at h; simp at h\n            | some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s\' h)',
     solNote: 'Long, and repetitive on purpose: the three memory branches are one proof written three times, and the two halves of the <code>ite</code> branch are one proof written twice. If you wrote it once and copied it, that is what the corpus did too.',
     expl: 'Induction on the fuel, with everything after the fuel left in the goal so that the hypothesis is quantified over it; then an eight-way split on the command. Six of the nine branches finish without <code>ih</code>. The three that use it apply it to a smaller command at the same fuel, which is legitimate because <code>ih</code> is about every command — the recursion in <code>run</code> went down in fuel, not in command, and the induction follows the recursion.',
     walk: [
       {tac:'intro n', h:'Introduced the fuel and nothing else, leaving <code>∀ c s s\', run n c s = some s\' → Exec c s s\'</code> as the goal, so that this whole statement is what the induction hypothesis will be.'},
       {tac:'induction n with', h:'Two branches. Nothing in the context mentions <code>n</code> yet, so nothing is reverted and the goal in each branch is the quantified statement.'},
       {tac:'| zero => intro c s s\' h; simp [run] at h', h:'With zero fuel the first clause gives <code>none</code>, so <code>h</code> becomes <code>none = some s\'</code>. The default simp set recognises that as impossible and closes the goal — no rewriting of the target was needed, and no derivation was built.'},
       {tac:'| succ n ih =>', h:'<code>ih</code> arrives as <code>∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'</code>. Everything below is inside this branch.'},
       {tac:'intro c s s\' h', h:'Now the command and the states are introduced — after the induction, so the hypothesis was already generalised over them.'},
       {tac:'cases c with', h:'Eight branches, one per constructor of <code>Cmd</code>. This is a case split, not an induction; nothing needs to shrink and no hypothesis is produced.'},
       {tac:'| skip => simp [run] at h; rw [← h]; exact .skip', h:'The clause returns <code>some s</code>, so <code>simp [run] at h</code> leaves <code>h : s = s\'</code>. <code>rw [← h]</code> puts <code>s</code> where <code>s\'</code> was in the goal, and <code>Exec.skip</code> concludes a run from a state to itself.'},
       {tac:'| assign x e => …', h:'The same three moves. The clause returns a state built with <code>Store.set</code>, and <code>Exec.assign</code> concludes exactly that state, so after the rewrite the two sides match with no argument to supply.'},
       {tac:'| load x l =>', h:'Opened the first of the three memory branches. Nothing in it uses <code>ih</code>, which is why it can be lifted out and worked in isolation, as it was above.'},
       {tac:'simp only [run] at h', h:'Substituted the <code>load</code> clause into <code>h</code>, leaving a <code>match</code> on <code>s.heap l</code> that cannot reduce because the scrutinee is an application of a variable.'},
       {tac:'cases hl : s.heap l with', h:'Split on the lookup, saving the equation as <code>hl</code>. Without the <code>hl :</code> the tactic accomplishes nothing at all.'},
       {tac:'| none   => rw [hl] at h; simp at h', h:'The rewrite makes the <code>match</code> reduce to <code>none</code>, so <code>h</code> becomes <code>none = some s\'</code> and <code>simp</code> closes the goal from the contradiction. No derivation is built, because none exists.'},
       {tac:'| some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl', h:'The rewrite resolves the <code>match</code>; <code>simp at h</code> reduces it and strips the <code>some</code>; <code>rw [← h]</code> replaces <code>s\'</code> in the goal by the record the clause produced; <code>Exec.load</code> takes <code>hl</code> as its premise.'},
       {tac:'| write l e =>', h:'The same five lines with <code>Exec.write</code> at the end. The <code>write</code> clause of <code>run</code> matches <code>| some _</code>, discarding the old value where <code>load</code> kept it; the premise of <code>Exec.write</code> still wants a value, and <code>hl</code> supplies it because the case split named one.'},
       {tac:'| free l =>', h:'The same five lines with <code>Exec.free</code>. Three branches, one proof — if you wrote the first and copied it twice, changing one name each time, that is exactly right.'},
       {tac:'| seq c₁ c₂ =>', h:'The first branch where the induction hypothesis is needed, and the first whose scrutinee is a run rather than a lookup.'},
       {tac:'simp only [run] at h', h:'Left the hypothesis as a <code>match</code> on <code>run n c₁ s</code>. The fuel inside is <code>n</code>, one below the <code>n + 1</code> the branch is about, which is what makes <code>ih</code> applicable.'},
       {tac:'cases hr : run n c₁ s with', h:'Split on whether the first half returned a state, saving the equation as <code>hr</code>. That equation is both what resolves the <code>match</code> and what <code>ih</code> will be applied to.'},
       {tac:'| none    => rw [hr] at h; simp at h', h:'If the first half gave nothing, the whole sequence gave nothing, and the hypothesis is contradictory. Same two tactics as the <code>none</code> branch of <code>load</code>.'},
       {tac:'| some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s\' h)', h:'After the rewrite, <code>h</code> is <code>run n c₂ s₁ = some s\'</code> — definitionally, through the reduced <code>match</code>, with no simplification needed. <code>ih</code> is applied twice, once per half, at the same fuel and at the intermediate state <code>s₁</code>; this is where a hypothesis fixed at one command would have failed.'},
       {tac:'| ite b c₁ c₂ => simp only [run] at h', h:'Left a <code>match</code> on the guard <code>b.eval s.store</code>, which is a <code>Bool</code> Lean cannot evaluate without knowing the store.'},
       {tac:'cases hb : b.eval s.store with', h:'Split on the guard, saving the equation. <code>Bool</code> has two constructors, so two branches — matching the two <code>Exec</code> rules for <code>.ite</code>.'},
       {tac:'| true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s\' h)', h:'The rewrite makes the <code>match</code> reduce to <code>run n c₁ s</code>, and <code>hb</code> is used a second time as the premise <code>Exec.iteTrue</code> demands. One equation, two jobs.'},
       {tac:'| false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s\' h)', h:'The mirror image, with the other branch of the conditional and the other rule.'},
       {tac:'| loop b c => simp only [run] at h', h:'The last branch, and the only one with a case split nested inside a case split.'},
       {tac:'cases hb : b.eval s.store with', h:'Split on the guard again. The <code>false</code> side finishes the loop; the <code>true</code> side runs the body and then the loop again.'},
       {tac:'| false => rw [hb] at h', h:'The clause returns <code>some s</code>, so after the rewrite <code>h</code> is <code>some s = some s\'</code> under a reduced <code>match</code>. The state has to be moved by hand from here.'},
       {tac:'have hs : s = s\' := Option.some.inj h', h:'Stripped the constructor. <code>Option.some.inj</code> accepts <code>h</code> in its unreduced form, so nothing had to be simplified first.'},
       {tac:'subst hs', h:'Replaced <code>s\'</code> by <code>s</code> throughout, so the goal became <code>Exec (.loop b c) s s</code> — the shape <code>Exec.loopFalse</code> concludes.'},
       {tac:'exact .loopFalse hb', h:'One premise, the guard equation, already in hand.'},
       {tac:'| true  => rw [hb] at h', h:'Reduced the outer <code>match</code> to the inner one, which is a <code>match</code> on <code>run n c s</code> — the body\'s run.'},
       {tac:'cases hr : run n c s with', h:'Split on the body\'s run, exactly as the <code>seq</code> branch split on the first half\'s.'},
       {tac:'| none    => rw [hr] at h; simp at h', h:'A body that does not finish inside the budget makes the whole loop return <code>none</code>, contradicting <code>h</code>.'},
       {tac:'| some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s\' h)', h:'Two applications of <code>ih</code> again, and the second is at <code>.loop b c</code> — the same command the branch is about. Legitimate, because <code>ih</code> is about every command at fuel <code>n</code>, and the recursive call in <code>run</code> was at <code>n</code>. The command is left as <code>_</code> because the expected type determines it.'}
     ],
     deep: [
       {t:'trace', title:'The seq branch, where the induction hypothesis is spent — the unchanged lines <code>case succ.seq</code>, <code>n : Nat</code>, <code>s s\' : State</code>, <code>c₁ c₂ : Cmd</code> are dropped from every state below, and <code>ih</code> from every state after the first',
        start:'ih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\nh : run (n + 1) (c₁ ;; c₂) s = some s\'\n⊢ Exec (c₁ ;; c₂) s s\'',
        steps:[
          {tac:'simp only [run] at h',
           state:'h :\n  (match run n c₁ s with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\n⊢ Exec (c₁ ;; c₂) s s\'',
           h:'The bound <code>s\'</code> inside the <code>match</code> is not the <code>s\'</code> of the goal; Lean prints the pattern variable under the name the definition gave it. Reading them as the same variable is the fastest way to get lost in this branch.'},
          {tac:'cases hr : run n c₁ s with',
           state:'case succ.seq.some\nh :\n  (match run n c₁ s with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\ns₁ : State\nhr : run n c₁ s = some s₁\n⊢ Exec (c₁ ;; c₂) s s\'',
           h:'The equation is saved; the hypothesis has not moved yet, because <code>cases</code> splits the goal, not <code>h</code>.'},
          {tac:'rw [hr] at h',
           state:'s₁ : State\nh :\n  (match some s₁ with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\nhr : run n c₁ s = some s₁\n⊢ Exec (c₁ ;; c₂) s s\'',
           h:'Now the scrutinee is a constructor and the whole hypothesis is, definitionally, <code>run n c₂ s₁ = some s\'</code>. Nothing further is done to it; <code>exact</code> takes it in this shape.'},
          {tac:'exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s\' h)',
           state:'No goals.',
           h:'<code>Exec.seq</code> wants two derivations meeting at a middle state. <code>ih c₁ s s₁ hr</code> supplies the first, <code>ih c₂ s₁ s\' h</code> the second, and the middle state <code>s₁</code> came out of the case split rather than being chosen.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Compare the fuel arithmetic with the command arithmetic. Both halves of the sequence are run at <code>n</code> while the whole sequence is at <code>n + 1</code>, so one unit of fuel pays for one level of nesting, however wide. The proof never mentions that; it only ever applies <code>ih</code>, which is at <code>n</code>, to things the clause also ran at <code>n</code>.'}
     ],
     pitfall: 'Writing <code>cases s.heap l with</code> instead of <code>cases hl : s.heap l with</code>. Lean accepts it and it accomplishes nothing: in the <code>none</code> goal <code>h</code> still reads <code>(match s.heap l with | some v =&gt; some { store := s.store.set x v, heap := s.heap } | none =&gt; none) = some s\'</code>, scrutinee and all, and the two goals differ only in a spare <code>v : Val</code>. The failure surfaces on the next line, twice, as <code>Unknown identifier `hl`</code> — a name error rather than anything about <code>cases</code>, which is why it reads like a typo. The saved-equation form is what connects the split to the rest of the context, and this proof needs it seven times: once each in <code>load</code>, <code>write</code>, <code>free</code>, <code>seq</code> and <code>ite</code>, and twice in <code>loop</code>.',
     variants: 'Drop <code>Option.some.inj</code> from the <code>loopFalse</code> branch and write <code>simp at h</code> followed by <code>subst h</code> instead: it compiles, because <code>simp</code> reduces the <code>match</code> and strips the constructor in one move. Keep <code>Option.some.inj</code> but drop the <code>subst</code> and the goal stays <code>Exec (.loop b c) s s\'</code> with <code>hs : s = s\'</code> sitting unused; <code>exact .loopFalse hb</code> is then rejected with <code>Type mismatch: Exec.loopFalse hb has type Exec (Cmd.loop b ?m.491) s s but is expected to have type Exec (Cmd.loop b c) s s\'</code> — the numeral is an internal counter and will read differently in your file, but the shape does not: a metavariable where the loop body should be, and <code>s s</code> where the goal wants <code>s s\'</code>. Reverse the theorem — <code>Exec c s s\' → run n c s = some s\'</code>, for a fixed <code>n</code> — and it is false at every <code>n</code>: take <code>n = 0</code> and <code>c = .skip</code>, where <code>Exec .skip s s</code> holds by its own rule and <code>run 0 .skip s</code> is <code>none</code> by <code>rfl</code>. Repairing that statement is what <code>run_complete</code> does, and the repair is an existential quantifier over the fuel.'
    },

    /* ============================================ monotonicity, ≤, max ==== */

    {t:'sec', s:'More fuel never hurts'},

    {t:'p', h:'Completeness runs the other way: a derivation exists, so produce a fuel that computes it.'},

    {t:'code', cap:'The second theorem. The fuel is existentially quantified, which is the only shape the statement can have — nothing bounds it in advance, so the proof has to choose one, rule of <code>Exec</code> by rule of <code>Exec</code>.',
     src:'theorem run_complete {c : Cmd} {s s\' : State} (h : Exec c s s\') :\n    ∃ n, run n c s = some s\' := by'},

    {t:'p', h:'The two-premise rules are where that bites. <code>Exec.seq</code> gives a derivation for each half, induction gives a fuel for each half, and the <code>seq</code> clause of <code>run</code> demands one fuel for both. Reconciling two budgets into one needs a theorem saying a budget can be raised.'},

    {t:'code', cap:'One more unit of fuel changes no answer that was already there. Stated in the same shape as soundness, and proved by the same induction.',
     src:'theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s\' : State),\n    run n c s = some s\' → run (n + 1) c s = some s\' := by'},

    {t:'p', h:'Five of its branches are a single tactic, and it is one this course has not used. <code>simpa [run] using h</code> means: simplify <code>h</code>, simplify the goal, and then close the goal with the simplified <code>h</code>. It exists because writing that out is three lines for one idea.'},

    {t:'code', tag:'illustration', cap:'The <code>skip</code> branch of <code>run_mono</code>, unpacked. <code>simpa [run] using h</code> is these two lines.',
     src:'example (n : Nat) (s s\' : State)\n    (h : run (n + 1) Cmd.skip s = some s\') : run (n + 1 + 1) Cmd.skip s = some s\' := by\n  simp [run] at h ⊢\n  exact h'},

    {t:'state', cap:'What the first line leaves. <code>⊢</code> in a location list names the goal, so <code>at h ⊢</code> says <i>in that hypothesis and in the goal</i>; without it, <code>simp</code> touches the goal only.',
     src:'n : Nat\ns s\' : State\nh : s = s\'\n⊢ s = s\''},

    {t:'p', h:'The three branches with sub-runs cannot use it, because there the goal and the hypothesis are <code>match</code>es at different fuels and no amount of simplification brings them together. They open with <code>simp only [run] at h ⊢</code> and then rewrite the goal\'s inner run using <code>ih</code>, which is what turns <code>run n c₁ s</code> into <code>run (n + 1) c₁ s</code> underneath.'},

    {t:'h3', s:'From one step to any number'},

    {t:'p', h:'<code>run_mono</code> raises a budget by one. What is wanted is raising it to anything larger, and the statement of that mentions <code>≤</code>. In Lean <code>n ≤ m</code> is not an abbreviation for an arithmetic fact; it is an inductively defined proposition, with two constructors, in exactly the sense Unit 19 introduced.'},

    {t:'code', tag:'illustration', src:'#print Nat.le'},

    {t:'state', cap:'One parameter, two rules: every number is at most itself, and if <code>n ≤ m</code> then <code>n ≤ m + 1</code>. A proof of <code>n ≤ m</code> is therefore a stack of <code>step</code>s on top of one <code>refl</code>, and its height is <code>m - n</code>.',
     src:'protected inductive Nat.le : Nat → Nat → Prop\nnumber of parameters: 1\nconstructors:\nNat.le.refl : ∀ {n : Nat}, n.le n\nNat.le.step : ∀ {n m : Nat}, n.le m → n.le m.succ'},

    {t:'p', h:'So a proof of <code>n ≤ m</code> is a derivation, and derivations can be inducted over — which is the tactic of Unit 20 applied to something that is not a run. The induction walks down the stack of <code>step</code>s, applying <code>run_mono</code> once per rung.'},

    {t:'code', src:'theorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s\' : State}\n    (h : run n c s = some s\') : run m c s = some s\' := by\n  induction hle with\n  | refl => exact h\n  | step _ ih => exact run_mono _ _ _ _ ih'},

    {t:'trace', title:'run_le, both branches',
     start:'n m : Nat\nhle : n ≤ m\nc : Cmd\ns s\' : State\nh : run n c s = some s\'\n⊢ run m c s = some s\'',
     steps:[
       {tac:'induction hle with',
        state:'case refl\nn m : Nat\nc : Cmd\ns s\' : State\nh : run n c s = some s\'\n⊢ run n c s = some s\'',
        h:'In the <code>refl</code> branch the two numbers are the same one, so the goal is the hypothesis. <code>m</code> is still in the context because it was a variable of the statement; the goal no longer mentions it.'},
       {tac:'| refl => exact h',
        state:'case step\nn m : Nat\nc : Cmd\ns s\' : State\nh : run n c s = some s\'\nm✝ : Nat\na✝ : n.le m✝\nih : run m✝ c s = some s\'\n⊢ run m✝.succ c s = some s\'',
        h:'The <code>step</code> branch. <code>ih</code> is the theorem at the smaller bound, and the goal is the theorem one higher. The two daggered names are the intermediate number and the sub-proof, neither of which is used.'},
       {tac:'| step _ ih => exact run_mono _ _ _ _ ih',
        state:'No goals.',
        h:'<code>run_mono</code> at <code>m✝</code> takes the answer at <code>m✝</code> to the answer at <code>m✝ + 1</code>, and <code>m✝.succ</code> is <code>m✝ + 1</code>. Its four explicit arguments are all determined by <code>ih</code> and the goal, so all four are <code>_</code>.'}
     ],
     done:'No goals.'},

    {t:'p', h:'Three lines, and the only new thing in them is what is being inducted over. The hypothesis <code>h</code> is untouched throughout; the work is entirely in walking the proof of the inequality apart.'},

    {t:'h3', s:'Two budgets into one'},

    {t:'p', h:'With <code>run_le</code> available, the <code>seq</code> case of completeness is three tactics. The two fuels coming out of the two induction hypotheses are raised to a common value, and that value is <code>max</code> of them.'},

    {t:'code', tag:'illustration', cap:'The step that reconciles two budgets, extracted from the <code>seq</code> case of <code>run_complete</code> and compiled on its own.',
     src:'example {c₁ c₂ : Cmd} {s sMid s\' : State} {n₁ n₂ : Nat}\n    (h₁ : run n₁ c₁ s = some sMid) (h₂ : run n₂ c₂ sMid = some s\') :\n    run (max n₁ n₂ + 1) (c₁ ;; c₂) s = some s\' := by\n  simp only [run]\n  rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n  exact run_le (Nat.le_max_right n₁ n₂) h₂'},

    {t:'trace', title:'Reconciling the two budgets — the three unchanged lines <code>c₁ c₂ : Cmd</code>, <code>s sMid s\' : State</code>, <code>n₁ n₂ : Nat</code> are dropped from every state below',
     start:'h₁ : run n₁ c₁ s = some sMid\nh₂ : run n₂ c₂ sMid = some s\'\n⊢ run (max n₁ n₂ + 1) (c₁ ;; c₂) s = some s\'',
     steps:[
       {tac:'simp only [run]',
        state:'⊢ (match run (max n₁ n₂) c₁ s with\n    | some s\' => run (max n₁ n₂) c₂ s\'\n    | none => none) =\n    some s\'',
        h:'The <code>+ 1</code> has been consumed by the clause and both sub-runs are at <code>max n₁ n₂</code>. This is the goal that <code>h₁</code> and <code>h₂</code>, at their own fuels, do not fit.'},
       {tac:'rw [run_le (Nat.le_max_left n₁ n₂) h₁]',
        state:'⊢ (match some sMid with\n    | some s\' => run (max n₁ n₂) c₂ s\'\n    | none => none) =\n    some s\'',
        h:'<code>run_le</code> raised <code>h₁</code> from <code>n₁</code> to <code>max n₁ n₂</code>, and rewriting with the result replaced the scrutinee. The <code>match</code> now reduces.'},
       {tac:'exact run_le (Nat.le_max_right n₁ n₂) h₂',
        state:'No goals.',
        h:'The goal is definitionally <code>run (max n₁ n₂) c₂ sMid = some s\'</code>, and <code>h₂</code> raised the same way is exactly that. As in the soundness proof, nothing simplifies the <code>match</code> first.'}
     ],
     done:'No goals.'},

    {t:'p', h:'Why <code>max</code> and not <code>n₁ + n₂</code>. Both are bounds above both fuels, and swapping one for the other costs only two different lemmas — the version with <code>+</code> was written out and compiles. The reason for <code>max</code> is that it says the true thing. The <code>seq</code> clause hands the same budget to both halves and takes it back afterwards; the halves do not spend out of a shared pot, so adding their budgets describes a machine that is not this one. <code>max</code> also gives the smaller bound, which matters the moment the same reconciliation is done twice, as it is in the <code>loopTrue</code> case.'},

    {t:'ex',
     id: 'm5-4',
     name: 'run_mono, run_le, run_complete',
     hard: true,
     why: 'Completeness is what makes a <i>failed</i> test informative: if the interpreter gives no answer at any fuel you care to try, this theorem is the reason to suspect the program rather than the budget. The three proofs are also the only place in the course where induction is run over a proof of an inequality, and the only place where two facts at different sizes have to be brought to a common size before they can be combined.',
     setup: 'Three theorems, in order; each uses the one before it. <code>run_mono</code> is <code>run_sound</code>\'s induction with a different payload. <code>run_le</code> is three lines. <code>run_complete</code> inducts on the derivation, not on the fuel.',
     goal: 'theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s\' : State),\n    run n c s = some s\' → run (n + 1) c s = some s\' := by\n  sorry\n\ntheorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s\' : State}\n    (h : run n c s = some s\') : run m c s = some s\' := by\n  sorry\n\ntheorem run_complete {c : Cmd} {s s\' : State} (h : Exec c s s\') :\n    ∃ n, run n c s = some s\' := by',
     hints: [
       'Three statements. The first says one more unit of fuel preserves an answer. The second says any larger fuel does, where <code>n ≤ m</code> is a proof object with two constructors. The third says every derivation is computed at some fuel — the fuel is existentially quantified, so you get to choose it, and you have to choose it for each rule of <code>Exec</code>.',
       'The first is the same induction as soundness: on the fuel, with everything else left in the goal. The second is an induction over the proof of the inequality: at <code>refl</code> the two bounds coincide, and at <code>step</code> you have the result one lower and need it one higher. The third is an induction over the derivation, one branch per rule; the leaf rules need one unit, and the rules with two premises need a single number that works for both premises.',
       '<code>simpa [run] using h</code> for the five branches of <code>run_mono</code> that finish in one move — the commands that do not run another command — and <code>simp only [run] at h ⊢</code> for the three that do. <code>induction hle with | refl | step</code>, and <code>run_mono</code> inside the second branch. For completeness: <code>induction h with</code>, <code>exact ⟨1, …⟩</code> at the leaves, <code>obtain</code> to open the two induction hypotheses, <code>refine ⟨max n₁ n₂ + 1, ?_⟩</code>, and <code>run_le</code> with <code>Nat.le_max_left</code> and <code>Nat.le_max_right</code>.',
       '<code>run_mono</code> opens exactly as soundness did, with <code>intro n</code> and <code>induction n with</code>; that leaves a <code>zero</code> branch closed by <code>intro c s s\' h; simp [run] at h</code> and a <code>succ</code> branch whose <code>ih</code> is quantified over every command and every pair of states. <code>run_le</code> in full is <code>induction hle with</code>, <code>| refl =&gt; exact h</code>, <code>| step _ ih =&gt; exact run_mono _ _ _ _ ih</code> — two names in the second branch, not one, because <code>Nat.le.step</code> carries a sub-proof and the induction hypothesis comes after it. <code>run_complete</code> opens on <code>induction h with</code>, which leaves ten branches with the fuel still to be chosen in each; the first of them is closed by <code>exact ⟨1, rfl⟩</code>.'
     ],
     sol: 'theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s\' : State),\n    run n c s = some s\' → run (n + 1) c s = some s\' := by\n  intro n\n  induction n with\n  | zero => intro c s s\' h; simp [run] at h\n  | succ n ih =>\n    intro c s s\' h\n    cases c with\n    | skip => simpa [run] using h\n    | assign x e => simpa [run] using h\n    | load x l => simpa [run] using h\n    | write l e => simpa [run] using h\n    | free l => simpa [run] using h\n    | seq c₁ c₂ =>\n        simp only [run] at h ⊢\n        cases hr : run n c₁ s with\n        | none    => rw [hr] at h; simp at h\n        | some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s\' h\n    | ite b c₁ c₂ =>\n        simp only [run] at h ⊢\n        cases hb : b.eval s.store with\n        | true  => rw [hb] at h; exact ih c₁ s s\' h\n        | false => rw [hb] at h; exact ih c₂ s s\' h\n    | loop b c =>\n        simp only [run] at h ⊢\n        cases hb : b.eval s.store with\n        | false => rw [hb] at h; exact h\n        | true  =>\n            rw [hb] at h\n            cases hr : run n c s with\n            | none    => rw [hr] at h; simp at h\n            | some s₁ =>\n                rw [hr] at h\n                have : run (n + 1) c s = some s₁ := ih c s s₁ hr\n                rw [this]\n                exact ih _ s₁ s\' h\n\ntheorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s\' : State}\n    (h : run n c s = some s\') : run m c s = some s\' := by\n  induction hle with\n  | refl => exact h\n  | step _ ih => exact run_mono _ _ _ _ ih\n\ntheorem run_complete {c : Cmd} {s s\' : State} (h : Exec c s s\') :\n    ∃ n, run n c s = some s\' := by\n  induction h with\n  | skip => exact ⟨1, rfl⟩\n  | assign => exact ⟨1, rfl⟩\n  | load hl => exact ⟨1, by simp [run, hl]⟩\n  | write hl => exact ⟨1, by simp [run, hl]⟩\n  | free hl => exact ⟨1, by simp [run, hl]⟩\n  | seq _ _ ih₁ ih₂ =>\n      obtain ⟨n₁, h₁⟩ := ih₁\n      obtain ⟨n₂, h₂⟩ := ih₂\n      refine ⟨max n₁ n₂ + 1, ?_⟩\n      simp only [run]\n      rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n      exact run_le (Nat.le_max_right n₁ n₂) h₂\n  | iteTrue hb _ ih =>\n      obtain ⟨n, hn⟩ := ih\n      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩\n  | iteFalse hb _ ih =>\n      obtain ⟨n, hn⟩ := ih\n      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩\n  | loopFalse hb => exact ⟨1, by simp only [run, hb]⟩\n  | loopTrue hb _ _ ihb ihr =>\n      obtain ⟨n₁, h₁⟩ := ihb\n      obtain ⟨n₂, h₂⟩ := ihr\n      refine ⟨max n₁ n₂ + 1, ?_⟩\n      simp only [run, hb]\n      rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n      exact run_le (Nat.le_max_right n₁ n₂) h₂',
     solNote: 'Three theorems and one idea: an answer survives being given more room. If you have climbed all four hints on <code>run_complete</code> and the <code>seq</code> case still will not close, open the solution. The arrangement of <code>obtain</code>, <code>refine</code> and two <code>run_le</code>s is a shape rather than a discovery, and having read it once you will write it again in the <code>loopTrue</code> case unaided.',
     expl: '<code>run_mono</code> is the soundness induction with the conclusion replaced: the branches with sub-runs now have to rebuild a <code>match</code> at a higher fuel, which is what <code>rw [ih …]</code> does. <code>run_le</code> converts one step into any number of steps by walking the proof of <code>≤</code>. <code>run_complete</code> inducts on the derivation, choosing a fuel in each branch; the leaves take 1, the composite rules take one more than the largest fuel their premises needed.',
     walk: [
       {tac:'run_mono: intro n', h:'The same opening as soundness, and for the same reason: everything after the fuel is left in the goal so that <code>ih</code> quantifies over it.'},
       {tac:'induction n with', h:'Two branches. The statement being inducted is the whole <code>∀ c s s\', …</code>.'},
       {tac:'| zero => intro c s s\' h; simp [run] at h', h:'With no fuel the hypothesis says <code>none = some s\'</code> and the branch closes on the contradiction, exactly as in soundness. The conclusion is never looked at.'},
       {tac:'| succ n ih => intro c s s\' h; cases c with', h:'Eight branches on the command, with <code>ih</code> quantified over commands and states.'},
       {tac:'| skip => simpa [run] using h', h:'Simplified both the hypothesis and the goal with <code>run</code> and the default set, leaving <code>s = s\'</code> on both sides, and closed the goal with the hypothesis.'},
       {tac:'| assign x e => | load x l => | write l e => | free l =>', h:'The same line four more times. In the three memory branches both the hypothesis and the goal reduce to the same stuck <code>match</code>, because the clause does not consult the fuel at all — the fuel patterns there are <code>_ + 1</code>.'},
       {tac:'| seq c₁ c₂ => simp only [run] at h ⊢', h:'Unfolded the clause in both places. The hypothesis is a <code>match</code> at fuel <code>n</code>; the goal is the same <code>match</code> at fuel <code>n + 1</code>. Nothing else changed, and the two are not yet comparable.'},
       {tac:'cases hr : run n c₁ s with', h:'Split on the first half\'s run at the lower fuel, saving the equation.'},
       {tac:'| none    => rw [hr] at h; simp at h', h:'Nothing came out of the first half, so the hypothesis is contradictory and the branch is free.'},
       {tac:'| some s₁ => rw [hr] at h', h:'Resolved the hypothesis\' <code>match</code>, so <code>h</code> became <code>run n c₂ s₁ = some s\'</code> definitionally. The goal still has an unresolved <code>match</code>, at the higher fuel.'},
       {tac:'rw [ih c₁ s s₁ hr]', h:'The step that has no counterpart in the soundness proof. <code>ih c₁ s s₁ hr</code> is a proof that <code>run (n + 1) c₁ s = some s₁</code>, and rewriting the goal with it replaces the goal\'s scrutinee, making its <code>match</code> reduce too.'},
       {tac:'exact ih c₂ s₁ s\' h', h:'Both sides are now at fuel <code>n + 1</code> with the same intermediate state, and the induction hypothesis on the second half closes it.'},
       {tac:'| ite b c₁ c₂ => simp only [run] at h ⊢; cases hb : b.eval s.store with', h:'The guard does not depend on the fuel, so once it is split the two sides are the same run at two fuels and <code>ih</code> alone finishes each branch. This is the branch where the difference between goal and hypothesis is visible: the split writes <code>true</code> into the goal, which becomes <code>(match true with …) = some s\'</code>, and leaves <code>h</code> saying <code>match BExpr.eval s.store b with …</code>.'},
       {tac:'| true => rw [hb] at h; exact ih c₁ s s\' h', h:'One rewrite, and it is in the hypothesis only — the goal was already substituted by the case split. Both sides now reduce, and the induction hypothesis at <code>c₁</code> is exactly what is left.'},
       {tac:'| loop b c => simp only [run] at h ⊢; cases hb : b.eval s.store with', h:'The last and longest branch.'},
       {tac:'| false => rw [hb] at h; exact h', h:'A loop whose guard is false returns <code>some s</code> at every fuel, so hypothesis and goal are the same proposition.'},
       {tac:'| true  => rw [hb] at h; cases hr : run n c s with', h:'The guard is true, so the body runs; split on whether it finished inside the lower budget.'},
       {tac:'| none    => rw [hr] at h; simp at h', h:'Contradiction again.'},
       {tac:'| some s₁ => rw [hr] at h', h:'The hypothesis becomes the statement about the rest of the loop at fuel <code>n</code>.'},
       {tac:'have : run (n + 1) c s = some s₁ := ih c s s₁ hr', h:'The body\'s run raised to the higher fuel, named so the rewrite below has something short to cite. <code>rw [ih c s s₁ hr]</code> does the same thing in one line.'},
       {tac:'rw [this]; exact ih _ s₁ s\' h', h:'Rewriting makes the goal\'s <code>match</code> reduce; the second use of <code>ih</code> is at <code>.loop b c</code>, left as <code>_</code> because the expected type fixes it.'},
       {tac:'run_le: induction hle with', h:'Inducted over the proof of <code>n ≤ m</code> rather than over any number. Two branches, from the two constructors of <code>Nat.le</code>.'},
       {tac:'| refl => exact h', h:'In this branch <code>m</code> has been replaced by <code>n</code> in the goal, so the goal is the hypothesis.'},
       {tac:'| step _ ih => exact run_mono _ _ _ _ ih', h:'<code>ih</code> is the result at the lower bound; <code>run_mono</code> lifts it by one, which is the difference between the two bounds in this branch. The underscore before <code>ih</code> is the sub-proof of the inequality, unused.'},
       {tac:'run_complete: induction h with', h:'Inducted over the derivation. Ten branches, one per rule of <code>Exec</code>, and each has to supply a fuel.'},
       {tac:'| skip => exact ⟨1, rfl⟩', h:'One unit is enough, and at that fuel <code>run 1 .skip s</code> reduces to <code>some s</code>, so the second component is <code>rfl</code>. The anonymous constructor builds the existential: a witness and a proof about it.'},
       {tac:'| assign => exact ⟨1, rfl⟩', h:'The same, with the record the clause builds matching the state the rule concludes term for term.'},
       {tac:'| load hl => exact ⟨1, by simp [run, hl]⟩', h:'One unit again, but now the clause is a <code>match</code> on <code>s.heap l</code> and <code>hl</code> is the premise saying what that is. Handing both to <code>simp</code> resolves the <code>match</code> and closes the equation.'},
       {tac:'| write hl => | free hl =>', h:'The same line with the same premise. The <code>by …</code> sits in an argument position inside the anonymous constructor, which is the term-level tactic block Unit 09 introduced.'},
       {tac:'| seq _ _ ih₁ ih₂ =>', h:'Two premises, so two induction hypotheses. The two underscores are the sub-derivations, which are not needed once their induction hypotheses are in hand.'},
       {tac:'obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂', h:'Opened the two existentials, naming the two fuels and the two equations. Until this point the fuels do not exist as terms.'},
       {tac:'refine ⟨max n₁ n₂ + 1, ?_⟩', h:'Committed to a fuel — the larger of the two, plus one for this rule — and left the equation as a hole. Choosing the witness before proving anything about it is what makes the rest of the branch a computation rather than a search.'},
       {tac:'simp only [run]', h:'Unfolded the <code>seq</code> clause, which consumed the <code>+ 1</code> and put both halves at <code>max n₁ n₂</code>.'},
       {tac:'rw [run_le (Nat.le_max_left n₁ n₂) h₁]', h:'Raised the first half from <code>n₁</code> and rewrote with the result, resolving the goal\'s <code>match</code>.'},
       {tac:'exact run_le (Nat.le_max_right n₁ n₂) h₂', h:'Raised the second half from <code>n₂</code>. The goal is definitionally that statement, so nothing reduces the <code>match</code> first.'},
       {tac:'| iteTrue hb _ ih => obtain ⟨n, hn⟩ := ih', h:'One premise, so one fuel to open.'},
       {tac:'exact ⟨n + 1, by simp only [run, hb]; exact hn⟩', h:'One more unit for the rule itself. <code>simp only [run, hb]</code> uses the guard equation to pick the branch of the <code>match</code>, and <code>hn</code> is what is left.'},
       {tac:'| iteFalse hb _ ih => …', h:'The mirror image, with the other clause of the conditional.'},
       {tac:'| loopFalse hb => exact ⟨1, by simp only [run, hb]⟩', h:'No premise at all, so one unit, and the clause returns <code>some s</code> once the guard is known false. No <code>exact</code> follows the <code>simp only</code>: it closes the goal on its own.'},
       {tac:'| loopTrue hb _ _ ihb ihr => obtain … obtain … refine ⟨max n₁ n₂ + 1, ?_⟩', h:'Two premises, so the <code>seq</code> shape repeated. The second premise is a run of the same loop, and its fuel is treated no differently from the body\'s.'},
       {tac:'simp only [run, hb]; rw [run_le … h₁]; exact run_le … h₂', h:'The only difference from the <code>seq</code> case is that the guard equation joins the <code>simp only</code>, because this clause has an outer <code>match</code> to get past before the inner one.'}
     ],
     deep: [
       {t:'trace', title:'run_mono, the seq branch — the rewrite that has no analogue in soundness. The unchanged lines <code>case succ.seq</code>, <code>n : Nat</code>, <code>c₁ c₂ : Cmd</code>, <code>s s\' : State</code> are dropped from every state below, and <code>ih</code> from every state after the first',
        start:'ih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → run (n + 1) c s = some s\'\nh : run (n + 1) (c₁ ;; c₂) s = some s\'\n⊢ run (n + 1 + 1) (c₁ ;; c₂) s = some s\'',
        steps:[
          {tac:'simp only [run] at h ⊢',
           state:'h :\n  (match run n c₁ s with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\n⊢ (match run (n + 1) c₁ s with\n    | some s\' => run (n + 1) c₂ s\'\n    | none => none) =\n    some s\'',
           h:'Two stuck <code>match</code>es at two different fuels. This is the shape <code>simpa</code> cannot handle, and the reason five branches use one tactic and three use six.'},
          {tac:'cases hr : run n c₁ s with … | some s₁ => rw [hr] at h',
           state:'s₁ : State\nh :\n  (match some s₁ with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\nhr : run n c₁ s = some s₁\n⊢ (match run (n + 1) c₁ s with\n    | some s\' => run (n + 1) c₂ s\'\n    | none => none) =\n    some s\'',
           h:'The hypothesis has resolved; the goal has not, because its scrutinee is at fuel <code>n + 1</code> and <code>hr</code> is about fuel <code>n</code>.'},
          {tac:'rw [ih c₁ s s₁ hr]',
           state:'⊢ (match some s₁ with\n    | some s\' => run (n + 1) c₂ s\'\n    | none => none) =\n    some s\'',
           h:'Only the goal moved; <code>s₁</code>, <code>h</code> and <code>hr</code> stand as they were and are not repeated. The induction hypothesis, applied to the first half, is exactly the equation the goal\'s scrutinee needed. Both sides now reduce and the branch closes with <code>ih</code> on the second half.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Read the three theorems as one statement about budgets: an answer once obtained is stable upwards (<code>run_mono</code>, <code>run_le</code>), so any finite collection of answers can be brought to a common budget, so a derivation built from finitely many sub-derivations has a budget (<code>run_complete</code>). The finiteness is the derivation\'s, and it is the same finiteness that made induction over derivations legitimate in Unit 20.'}
     ],
     pitfall: 'Carrying <code>simpa [run] using h</code> into the <code>seq</code> branch of <code>run_mono</code>, on the strength of it having closed the five before it. It fails, and the message is the clearest statement of the rule on this page: <code>Type mismatch: After simplification, term h has type (match run n c₁ s with | some s\' =&gt; run n c₂ s\' | none =&gt; none) = some s\' but is expected to have type (match run (n + 1) c₁ s with | some s\' =&gt; run (n + 1) c₂ s\' | none =&gt; none) = some s\'</code>. Nothing is malformed; the two sides are the same <code>match</code> at two different fuels, and no simplification closes that gap because closing it <i>is</i> the theorem. The fix is <code>simp only [run] at h ⊢</code> and then the case split, and the branches where <code>simpa</code> does work are exactly the five commands that do not run another command. The other mistake is writing <code>| step ih =&gt; exact run_mono _ _ _ _ ih</code> with one name instead of two. <code>Nat.le.step</code> takes the sub-proof as an argument, and the induction hypothesis comes after it, so a single name binds the sub-proof and the error arrives on the application: <code>Application type mismatch: The argument ih has type n.le m✝ but is expected to have type run m✝ c s = some s\'</code>. The message names <code>ih</code> and a type that is an inequality, which is the tell — the induction hypothesis was never the thing you named.',
     variants: 'Replace <code>max n₁ n₂</code> by <code>n₁ + n₂</code> throughout and everything still compiles, with the two <code>Nat.le_max_*</code> citations replaced by the two corresponding facts about addition — the bound gets larger and nothing else changes. Drop <code>run_le</code> entirely and try to close the <code>seq</code> case with <code>n₁ + 1</code> as the fuel: <code>rw [h₁]</code> succeeds and then <code>exact h₂</code> is rejected — <code>Type mismatch: h₂ has type run n₂ c₂ sMid = some s\' but is expected to have type (match some sMid with | some s\' =&gt; run n₁ c₂ s\' | none =&gt; none) = some s\'</code> — because nothing has made the two fuels equal. Reverse <code>run_mono</code> to say that fewer units preserve an answer and it is false at the first program that needs any fuel at all: <code>run 2 demoProg demoStart</code> is a state and <code>run 1 demoProg demoStart</code> is <code>none</code>, both by <code>rfl</code>.'
    },

    /* ============================================== what is not proved ==== */

    {t:'sec', s:'A program with no answer'},

    {t:'p', h:'Completeness says a fuel exists. It does not say how to find one, and it does not bound one in terms of the program: the fuel it produces is read off the derivation, so you need the derivation before you can compute the budget, which is the wrong way round for testing. Nothing better is available, and the reason is a program.'},

    {t:'code', cap:'A loop whose guard is <code>0 ≠ 1</code>, with an empty body. The guard evaluates to <code>true</code> in every store, and the body changes nothing, so every run of it is followed by another.',
     src:'def spin : Cmd := .loop (.not (.equals (.const 0) (.const 1))) .skip'},

    {t:'code', cap:'No fuel is enough. The induction is on the fuel, and the <code>succ</code> branch splits again on the fuel — because one unit went on reaching the loop clause, and what is left has to cover the body before it can cover the next turn. With nothing left the body already returns <code>none</code>; with something left it returns the state unchanged and the remaining loop is at exactly the fuel <code>ih</code> speaks about.',
     src:'theorem run_spin_none : ∀ (n : Nat) (s : State), run n spin s = none := by\n  intro n\n  induction n with\n  | zero => intro s; rfl\n  | succ n ih =>\n      intro s\n      show (match run n Cmd.skip s with\n            | some s\' => run n spin s\'\n            | none    => none) = none\n      cases n with\n      | zero   => rfl\n      | succ m => exact ih s'},

    {t:'p', h:'The <code>show</code> is doing real work. In <code>spin</code> the guard is a closed term, so <code>b.eval s.store</code> evaluates to <code>true</code> without knowing the store, so the outer <code>match</code> of the <code>loop</code> clause reduces on its own and what is left is the inner one. <code>show</code> states that reduced form, and Lean accepts it because it is definitionally what the goal already was. Stating it is what lets the two branches of <code>cases n</code> close by <code>rfl</code> and by <code>ih</code>.'},

    {t:'state', cap:'The goal before the <code>show</code>, and after it, with the three context lines <code>n : Nat</code>, <code>ih : ∀ (s : State), run n spin s = none</code>, <code>s : State</code> dropped from both.',
     src:'⊢ run (n + 1) spin s = none\n\n⊢ (match run n Cmd.skip s with\n    | some s\' => run n spin s\'\n    | none => none) =\n    none'},

    {t:'code', cap:'And so no derivation exists either. This is the theorem that makes the fuel honest: <code>spin</code> does not fault and does not finish, and the relation has nothing to say about it beyond the absence of a tree.',
     src:'theorem spin_diverges (s s\' : State) : ¬ Exec spin s s\' := by\n  intro hex\n  obtain ⟨n, hn⟩ := run_complete hex\n  rw [run_spin_none n s] at hn\n  exact absurd hn (by simp)'},

    {t:'p', h:'The proof runs completeness backwards. Suppose a derivation; completeness turns it into a fuel and an answer; <code>run_spin_none</code> says that answer is <code>none</code>; and <code>none = some s\'</code> is impossible. Unit 19 conflated a program that faults with a program that never stops, on the grounds that neither has a derivation. <code>spin_diverges</code> is the first proof in the course that a particular program is in the second class rather than the first, and it needed the interpreter to say it.'},

    /* ================================================== retrospective ===== */

    {t:'sec', s:'Retrospective'},

    {t:'detail', title:'What does <code>run n c s = none</code> not tell you?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Anything about <code>c</code>. It says the budget <code>n</code> did not suffice, and three unrelated situations produce it: the program faults, the program runs forever, or the program is fine and <code>n</code> was too small. <code>run 1 demoProg demoStart = none</code> and <code>run 100 (Cmd.load 0 5) demoStart = none</code> are both true and mean opposite things.'},
      {t:'p', h:'This is why soundness is stated with <code>some s\'</code> as its hypothesis and why there is no companion theorem in the <code>none</code> direction. The one you might hope for — <code>run n c s = none → ¬ Exec c s s\'</code> — is false, and <code>demoProg</code> at fuel 1 is the counterexample. What is true is the contrapositive of completeness: if <code>run n c s = none</code> for <b>every</b> <code>n</code>, there is no derivation. That is a statement about infinitely many runs, so it is not something a test can establish, and <code>spin_diverges</code> is what proving it looks like.'}
    ]},

    {t:'detail', title:'Why <code>max</code> and not <code>+</code>?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Because the fuel bounds the depth of the recursion rather than the number of steps taken, and <code>max</code> is the operation that matches that reading: a sequence of a thousand commands nested to depth ten needs ten units, not a thousand. Not because <code>+</code> fails — it compiles, with the two <code>Nat.le_max_*</code> citations replaced by the corresponding facts about addition, and gives a larger number with nothing behind it.'}
    ]},

    {t:'detail', title:'What would break if <code>Exec</code> were nondeterministic?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Soundness would survive untouched. It says every answer <code>run</code> gives is <i>an</i> answer the relation allows, and adding more allowed answers cannot make that false. The proof does not use determinism anywhere; every branch builds a derivation and none of them rules one out.'},
      {t:'p', h:'Completeness would become false as stated, and not marginally. <code>run</code> is a function, so for each fuel it returns at most one state; a relation permitting two different final states for one program cannot have both of them produced by <code>run n c s</code> at any <code>n</code>. The repair is to stop asking for a function: the interpreter would have to return a set or a list of states, and the theorem would say that every state related to <code>s</code> appears in that collection for some fuel. Every proof on this page would then carry a membership argument where it currently carries an equation, which is a fair measure of what determinism is buying here.'},
      {t:'p', h:'That the relation is deterministic is Unit 20\'s theorem, and this unit is where the two facts sit side by side: a deterministic relation, and a function that computes it.'}
    ]},

    {t:'dod', h:'You can say why a total interpreter for this language cannot exist, and why a fuel argument gives one that is total and still useful. You can read <code>run</code>\'s clauses against <code>Exec</code>\'s rules and pair them up, including the two guard clauses against <code>iteTrue</code> and <code>iteFalse</code>. You can run a program with <code>#eval</code>, choose a fuel by trying, and close the resulting equation with <code>rfl</code>. You can induct on the fuel with the command and states left in the goal, and say what goes wrong when they are introduced first. You can state the rule for <code>simp [run]</code> against <code>simp only [run] at h ⊢</code> and name the branches where it bites. You can look at a hypothesis displaying an unreduced <code>match</code>, decide whether it is already the thing you want, and hand it to <code>exact</code> or to <code>Option.some.inj</code> without simplifying. You can prove <code>run_mono</code>, lift it to <code>run_le</code> by inducting on a proof of <code>n ≤ m</code>, and use <code>max</code> with <code>run_le</code> to bring two fuel bounds together. And you can say what completeness does not give you, with <code>spin</code> as the reason.'},

    {t:'p', h:'Two descriptions of the same partial function, and neither says anything about what <i>should be true</i> before or after a run. Nothing in this course so far mentions both a command and an assertion.'}

  ]
});
