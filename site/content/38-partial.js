registerChapter({
  id: 'partial',
  num: '35',
  phase: 'Phase 8 · Control and termination',
  title: 'Partial correctness, and conditionals',
  ledgerForward: ['hoare_while_variant'],
  blurb: 'One quantifier moves and a total triple becomes a partial one. The implication runs one way, and only because runs are unique — and the conditional gets a rule in each reading, by opposite proofs.',

  orient: {
    youWill: [
      'State both readings of a triple side by side and say which quantifier moved, and what it turned into.',
      'Prove <code>partial_of_total</code>, and name the single ingredient it needs — determinism, proved in Unit 20 and unused since.',
      'Say why the converse fails, and produce the command that refutes it.',
      'Prove the partial structural rules, and say what changed: in the total versions you <i>build</i> a derivation, in the partial ones you are <i>handed</i> one and take it apart.',
      'Lift a guard into an assertion with <code>bTrue</code> and <code>bFalse</code>, and predict — before running Lean — the exact shape of the hypothesis each branch of an inversion will hand you.',
      'Prove the partial conditional rule in two lines, because inversion supplies exactly the extra conjunct each branch hypothesis is asking for.',
      'Prove the <b>total</b> conditional rule, where you must split on the guard <i>before</i> you can choose a branch, and keep the equation the split would otherwise throw away.'
    ],
    needs: [
      'Unit 19: <code>Exec</code> and its ten constructors, and inversion by <code>cases h with | ctor …</code>.',
      'Unit 20: <code>exec_deterministic</code>, and why <code>induction</code> needs an index that is a variable.',
      'Unit 22: <code>Hoare</code>, <code>PartialHoare</code>, and the four rules proved there.',
      'Unit 26: the constant-command induction idiom, and why an induction needs its index left as a variable.',
      'Unit 31: <code>wp</code>, and the two directions of a <code>⊣⊢</code> proof by <code>constructor</code>.'
    ],
    payoff: 'The loop rule of Unit 36 is a partial rule, and it has to be: nothing about a loop can be proved in the total reading until Unit 37 supplies a termination argument. This page is where the weak reading stops being a definition nobody uses and becomes the reading Unit 36 is written in.'
  },

  blocks: [

    /* ============================================== picking up the thread ==== */

    {t:'p', h:"Use them, then. <code>Cmd</code> has eight constructors and the logic has a rule for six of them — <code>skip</code>, assignment, the three memory commands, and sequencing. Giving <code>ite</code> a rule is this page's work and it costs two theorems, one in each reading of a triple. Giving <code>loop</code> a rule is not this page's work, and the reason is visible before any loop rule is written down."},

    {t:'p', h:"Look at what a total triple demands. <code>Hoare P c Q</code> says: for every store and heap satisfying <code>P</code> there <b>is</b> a state <code>s'</code> that <code>c</code> reaches, and <code>Q</code> holds there. To prove one you must produce a derivation. A derivation of a loop run is a tower of <code>loopTrue</code> steps with a <code>loopFalse</code> on top — one storey per iteration, as Unit 19 drew it — and nothing in the syntax of <code>.loop b c</code> says how many storeys. For a loop whose guard never goes false there is no tower at all, so a total triple about it is false as soon as anything satisfies its precondition."},

    {t:'p', h:"The other definition has been sitting in the file since Unit 22 and has been used for nothing."},

    {t:'code', cap:'Both readings, as Unit 22 wrote them. Same three arguments, same components; the difference is where <code>s\'</code> is bound and what joins the two facts about it.',
     src:"def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap\n\ndef PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap"},

    {t:'txt', cap:'One quantifier moved to the front and changed sign; the conjunction under it became an implication. Everything else is identical, character for character.',
     src:"  Hoare P c Q          ∀ σ h,      P σ h  →   ∃ s',  Exec c ⟨σ, h⟩ s'  ∧  Q s'.store s'.heap\n                                              ‾‾‾‾                       ‾\n  PartialHoare P c Q   ∀ σ h s',   P σ h  →          Exec c ⟨σ, h⟩ s'  →  Q s'.store s'.heap\n                           ‾‾‾                                           ‾"},

    {t:'p', h:"Read it as the transposition it is: <code>∃ x, A x ∧ B x</code> against <code>∀ x, A x → B x</code>. The first asserts that the set of runs is non-empty and that some member of it is good. The second asserts that every member is good, and asserts nothing about whether there is one. The two agree exactly when there is precisely one run. They disagree at both ends: when there are several — which cannot happen here, and Unit 20 is why — and when there are none."},

    {t:'p', h:"There are two ways for a command to have no run, and this language can do both. It can fault: <code>.load x l</code> from a heap where <code>l</code> is unallocated has no derivation, which is what <code>exec_load_stuck</code> says. Or it can fail to stop. Unit 22 exhibited the first and used it to reject <code>PartialHoare</code> as the primary definition. With <code>loop</code> in play the second arrives, and it points the other way."},

    {t:'svg', cap:'Three commands, and how each is judged. A run is an arrow. The total reading asks for an arrow that lands in <code>Q</code>; the partial reading asks that every arrow that exists lands in <code>Q</code>. Where there is no arrow the first has nothing to point at and the second has nothing to check.',
     src:"<svg viewBox=\"0 0 640 240\" role=\"img\" aria-label=\"Three rows. Row one, a terminating command: a box P with an arrow to a box Q; both Hoare and PartialHoare are ticked. Row two, a faulting command: a box P with an arrow that stops at a cross; Hoare is crossed and PartialHoare ticked. Row three, a looping command: a box P with a dashed arrow trailing off; Hoare is crossed and PartialHoare ticked.\">\n  <defs>\n    <marker id=\"ah38\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"currentColor\"/>\n    </marker>\n  </defs>\n  <g class=\"dg\">\n    <text x=\"432\" y=\"26\" text-anchor=\"middle\" class=\"dg-lab\">Hoare</text>\n    <text x=\"552\" y=\"26\" text-anchor=\"middle\" class=\"dg-lab\">PartialHoare</text>\n\n    <text x=\"20\" y=\"64\" class=\"dg-note\">it stops</text>\n    <rect class=\"dg-box a\" x=\"120\" y=\"42\" width=\"58\" height=\"32\" rx=\"5\"/>\n    <text x=\"149\" y=\"64\" text-anchor=\"middle\" class=\"dg-t\">P</text>\n    <path d=\"M 186 58 L 274 58\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah38)\"/>\n    <rect class=\"dg-box b\" x=\"282\" y=\"42\" width=\"58\" height=\"32\" rx=\"5\"/>\n    <text x=\"311\" y=\"64\" text-anchor=\"middle\" class=\"dg-t\">Q</text>\n    <text x=\"432\" y=\"64\" text-anchor=\"middle\" class=\"dg-t\">✓</text>\n    <text x=\"552\" y=\"64\" text-anchor=\"middle\" class=\"dg-t\">✓</text>\n\n    <text x=\"20\" y=\"134\" class=\"dg-note\">it faults</text>\n    <rect class=\"dg-box a\" x=\"120\" y=\"112\" width=\"58\" height=\"32\" rx=\"5\"/>\n    <text x=\"149\" y=\"134\" text-anchor=\"middle\" class=\"dg-t\">P</text>\n    <path d=\"M 186 128 L 228 128\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\"/>\n    <path d=\"M 234 120 L 250 136 M 250 120 L 234 136\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.6\"/>\n    <text x=\"432\" y=\"134\" text-anchor=\"middle\" class=\"dg-t\">✗</text>\n    <text x=\"552\" y=\"134\" text-anchor=\"middle\" class=\"dg-t\">✓</text>\n\n    <text x=\"20\" y=\"204\" class=\"dg-note\">it never stops</text>\n    <rect class=\"dg-box a\" x=\"120\" y=\"182\" width=\"58\" height=\"32\" rx=\"5\"/>\n    <text x=\"149\" y=\"204\" text-anchor=\"middle\" class=\"dg-t\">P</text>\n    <path d=\"M 186 198 L 258 198\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" stroke-dasharray=\"5 4\" opacity=\"0.75\"/>\n    <text x=\"280\" y=\"204\" text-anchor=\"middle\" class=\"dg-t\">⋯</text>\n    <text x=\"432\" y=\"204\" text-anchor=\"middle\" class=\"dg-t\">✗</text>\n    <text x=\"552\" y=\"204\" text-anchor=\"middle\" class=\"dg-t\">✓</text>\n  </g>\n</svg>"},

    {t:'p', h:"The two ticks in the bottom rows are one theorem, and its proof is a term with no tactics in it. If a command has no run from any state at all, every partial triple you can write about it holds, whatever its precondition and whatever its postcondition."},

    {t:'code', tag:'illustration', cap:'The premise says: from no store and no heap does <code>c</code> reach anything. The proof spends it immediately — <code>hex</code> is a run, <code>hstuck σ h s\'</code> says there is none, and <code>absurd</code> puts the two together. The postcondition is never looked at, which is the point.',
     src:"example (P Q : Assertion) (c : Cmd) (hstuck : ∀ σ h s', ¬ Exec c ⟨σ, h⟩ s') :\n    PartialHoare P c Q :=\n  fun σ h s' _ hex => absurd hex (hstuck σ h s')"},

    {t:'p', h:"The same premise refutes the total reading, provided something satisfies the precondition — the total triple promises a run and the premise says there is none."},

    {t:'code', tag:'illustration', cap:'The precondition has to be inhabited somewhere, or the total triple is vacuous too. With that, the refutation is three lines: take a state where <code>P</code> holds, ask the triple for its run, hand the run to the premise.',
     src:"example (P Q : Assertion) (c : Cmd) (hstuck : ∀ σ h s', ¬ Exec c ⟨σ, h⟩ s')\n    (hP : ∃ σ h, P σ h) : ¬ Hoare P c Q := by\n  intro htot\n  obtain ⟨σ, h, hp⟩ := hP\n  obtain ⟨s', hex, _⟩ := htot σ h hp\n  exact hstuck σ h s' hex"},

    {t:'p', h:"One instance of that premise is available now. <code>exec_load_stuck</code> is not quite the shape <code>hstuck</code> asks for — it is about the empty heap, not about every heap, and <code>.load 0 0</code> does run from a heap where location 0 is allocated. So the instance is proved directly, with <code>emp</code> in the precondition doing the work of pinning the heap to <code>Heap.empty</code>."},

    {t:'code', tag:'illustration', cap:'A load from an empty heap, judged both ways. The first proof rewrites the heap using <code>hp : h = Heap.empty</code> and then hands the run to <code>exec_load_stuck</code>. The second asks the total triple for its run at one concrete state and hands <i>that</i> to the same theorem. The postcondition is <code>aFalse</code> in both, so the partial triple is asserting that every run of this command establishes a contradiction — and it is true, because there are no runs.',
     src:"example : PartialHoare emp (.load 0 0) aFalse := by\n  intro σ h s' hp hex\n  rw [hp] at hex\n  exact absurd hex (exec_load_stuck 0 0 σ s')\n\nexample : ¬ Hoare emp (.load 0 0) aFalse := by\n  intro htot\n  obtain ⟨s', hex, _⟩ := htot (fun _ => 0) Heap.empty rfl\n  exact exec_load_stuck 0 0 (fun _ => 0) s' hex"},

    {t:'p', h:"The other instance is the loop. Take the guard <code>0 ≠ 1</code>, which evaluates to <code>true</code> at every store, and put <code>skip</code> under it."},

    {t:'code', tag:'illustration', cap:'A command with a body that does nothing and a guard that never goes false. The second line is the guard evaluated: <code>Atom.eval</code> sends both constants to themselves, <code>0 == 1</code> is <code>false</code>, and <code>!false</code> is <code>true</code>, at any store whatsoever.',
     src:"def spinSkip : Cmd := .loop (.not (.equals (.const 0) (.const 1))) .skip\n\nexample (σ : Store) : (BExpr.not (.equals (.const 0) (.const 1))).eval σ = true := rfl"},

    {t:'p', h:"<code>spinSkip</code> has no run from any state, so by the two theorems above every partial triple about it holds and every total triple with a satisfiable precondition fails. That is the one claim on this page not turned into Lean: a proof of it has to induct over a derivation whose command index is pinned to <code>spinSkip</code> rather than left as a variable, which is the manoeuvre Unit 26 needed for locality of a loop. Nothing below depends on it."},

    /* ================================================= one direction only ==== */

    {t:'sec', s:'One direction, and the ingredient it needs'},

    {t:'p', h:"The two readings are not independent. Determinism gives a command at most one run, so a good run is the only run there is, and the total reading should imply the partial one."},

    {t:'p', h:"Write the proof and watch where it stalls. Five <code>intro</code>s open <code>PartialHoare</code>, giving a store, a heap, a final state <code>s'</code>, the precondition and a run reaching <code>s'</code>. The hypothesis <code>h : Hoare P c Q</code>, applied to that store and heap, produces a state of its own."},

    {t:'state', cap:'Five lines of the eleven in scope after <code>obtain</code>; the rest is unchanged from the statement and is in the fold below. Two final states are now in play, and the postcondition is known at the wrong one.',
     src:"hex : Exec c { store := σ, heap := hh } s'\ns'' : State\nhex'' : Exec c { store := σ, heap := hh } s''\nhq : Q s''.store s''.heap\n⊢ Q s'.store s'.heap"},

    {t:'detail', title:'The full context at that point', open:false, blocks:[
      {t:'state', cap:'Eleven lines, from <code>trace_state</code> placed immediately after the <code>obtain</code>.',
       src:"P Q : Assertion\nc : Cmd\nh : Hoare P c Q\nσ : Store\nhh : Heap\ns' : State\nhp : P σ hh\nhex : Exec c { store := σ, heap := hh } s'\ns'' : State\nhex'' : Exec c { store := σ, heap := hh } s''\nhq : Q s''.store s''.heap\n⊢ Q s'.store s'.heap"}
    ]},

    {t:'p', h:"Nothing in that context says <code>s'</code> and <code>s''</code> are the same state. Ending the proof with <code>exact hq</code> is rejected with <code>Type mismatch: hq has type Q s''.store s''.heap but is expected to have type Q s'.store s'.heap</code>, and the mismatch is not a Lean inconvenience. It is the mathematical content: two runs of the same command from the same state, and the claim that they agree is a theorem about the language, not about the logic."},

    {t:'p', h:"That theorem is <code>exec_deterministic</code>. Unit 20 proved it, said it would be spent later, and nothing has spent it since. This is later."},

    {t:'ex',
     id:'x70',
     name:'partial_of_total',
     why:"The one implication between the two readings, and the only place in the entire course where <code>exec_deterministic</code> is used. Fifteen units separate the proof from the use, and the gap says what determinism is for: it is not a convenience of the semantics, it is precisely the hypothesis under which a weaker logic follows from a stronger one. The course does not spend the theorem again — Units 36 and 37 prove their loop rules directly in the reading each one needs — so its value is not that it is a tool. It is that it orders the two definitions, and names the property of the language that orders them.",
     setup:"You have <code>exec_deterministic : Exec c s s₁ → Exec c s s₂ → s₁ = s₂</code> from Unit 20, with <code>c</code>, <code>s</code>, <code>s₁</code>, <code>s₂</code> implicit. Nothing else is needed.",
     goal:"theorem partial_of_total {P Q : Assertion} {c : Cmd}\n    (h : Hoare P c Q) : PartialHoare P c Q := by",
     hints:[
       "Unfolded, the goal is: for every store <code>σ</code>, heap <code>hh</code> and state <code>s'</code>, if <code>P σ hh</code> and <code>c</code> runs from <code>⟨σ, hh⟩</code> to <code>s'</code>, then <code>Q</code> holds at <code>s'</code>. The order of the binders is the thing to read twice: <code>s'</code> comes third, before the precondition and before the run.",
       "You are handed one run and the hypothesis produces another. Both start at the same state and both are runs of the same command, so they end at the same state — and the hypothesis already tells you the postcondition holds at the end of its own.",
       "Five <code>intro</code>s, then <code>obtain</code> on the hypothesis applied to the store and heap, then <code>exec_deterministic</code>, then a rewrite.",
       "<code>intro σ hh s' hp hex</code> leaves <code>⊢ Q s'.store s'.heap</code> with <code>hex : Exec c ⟨σ, hh⟩ s'</code> in scope. Then <code>obtain ⟨s'', hex'', hq⟩ := h σ hh hp</code> puts the hypothesis's own run and its postcondition in scope, at the state <code>s''</code>."
     ],
     sol:"theorem partial_of_total {P Q : Assertion} {c : Cmd}\n    (h : Hoare P c Q) : PartialHoare P c Q := by\n  intro σ hh s' hp hex\n  obtain ⟨s'', hex'', hq⟩ := h σ hh hp\n  have : s' = s'' := exec_deterministic hex hex''\n  rw [this]; exact hq",
     solNote:"The anonymous <code>have</code> is enough because the equation is used once, on the very next tactic. Giving it a name and calling <code>subst</code> on it instead of rewriting compiles too.",
     expl:"The proof has exactly one idea in it and three lines of plumbing around it. You are given a run to <code>s'</code>; the hypothesis gives you a run to <code>s''</code> together with the postcondition at <code>s''</code>; determinism identifies the two states; the rewrite moves the goal onto the state where the postcondition is already known.",
     walk:[
       {tac:'intro σ hh s\' hp hex', h:"Five names for the five binders of <code>PartialHoare</code>. The third one is the <i>final state</i>, not the precondition proof — that is the quantifier that moved. The goal becomes <code>Q s'.store s'.heap</code>."},
       {tac:'obtain ⟨s\'\', hex\'\', hq⟩ := h σ hh hp', h:"<code>h σ hh hp</code> is an existential: a state, a run to it, and the postcondition there. Destructuring it names all three at once. The context now holds two runs of <code>c</code> from the same starting state, and nothing relating them."},
       {tac:'have : s\' = s\'\' := exec_deterministic hex hex\'\'', h:"The relation. Argument order decides which way the equation points: <code>hex</code> first gives <code>s' = s''</code>, which is the direction the rewrite below wants."},
       {tac:'rw [this]', h:"Rewrites the goal from <code>Q s'.store s'.heap</code> to <code>Q s''.store s''.heap</code> — the statement that is already in the context under the name <code>hq</code>."},
       {tac:'exact hq', h:"Closes it. The precondition <code>hp</code> was used exactly once, to get the hypothesis to produce anything at all."}
     ],
     deep:[
       {t:'trace', title:'partial_of_total, step by step (new hypotheses and the goal line only)',
        start:"⊢ PartialHoare P c Q",
        steps:[
          {tac:'intro σ hh s\' hp hex',
           state:"σ : Store\nhh : Heap\ns' : State\nhp : P σ hh\nhex : Exec c { store := σ, heap := hh } s'\n⊢ Q s'.store s'.heap",
           h:"The definition is now fully open. <code>hex</code> is the run you were handed; you did not choose it and you know nothing about it."},
          {tac:'obtain ⟨s\'\', hex\'\', hq⟩ := h σ hh hp',
           state:"s'' : State\nhex'' : Exec c { store := σ, heap := hh } s''\nhq : Q s''.store s''.heap\n⊢ Q s'.store s'.heap",
           h:"Three new hypotheses and an unchanged goal. This is the state where the proof would stop if the language were nondeterministic: everything you know is about <code>s''</code>, everything you must prove is about <code>s'</code>."},
          {tac:'have : s\' = s\'\' := exec_deterministic hex hex\'\'',
           state:"this : s' = s''\n⊢ Q s'.store s'.heap",
           h:"One line, and it is the whole theorem. The two runs are runs of the same command from the same state."},
          {tac:'rw [this]',
           state:"⊢ Q s''.store s''.heap",
           h:"The goal is now <code>hq</code>, character for character."}
        ],
        done:"No goals."}
     ],
     pitfall:"Getting the argument order of <code>exec_deterministic</code> backwards. <code>exec_deterministic hex'' hex</code> is equally well typed and gives <code>s'' = s'</code>; the next line then fails with <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern s'' in the target expression Q s'.store s'.heap</code>, because the goal mentions <code>s'</code> and the rewrite is looking for <code>s''</code>. The repair is either to swap the two arguments or to write <code>rw [← this]</code>.",
     variants:"Drop determinism and the theorem is false, not unproved. Replace <code>Exec</code> by a relation with two rules for <code>skip</code> — one leaving the state alone, one zeroing the store — and define the two readings over it verbatim. The total triple <code>{σ 0 = 7} skip {σ 0 = 7}</code> holds, witnessed by the first rule; the partial one fails, witnessed by the second. Both are compiled in the fold after this exercise. · The converse implication fails even <i>with</i> determinism, and the witness is the faulting load above: <code>PartialHoare emp (.load 0 0) aFalse</code> is provable and <code>Hoare emp (.load 0 0) aFalse</code> is refutable. So the two readings are genuinely ordered, not equivalent."
    },

    {t:'detail', title:'What breaks without determinism, compiled', open:false, blocks:[
      {t:'p', h:"The proof of <code>partial_of_total</code> uses determinism once, and that use is not removable. To see it, keep everything else and change only the semantics: a relation with two rules for <code>skip</code>, so that one command can reach two different states."},
      {t:'code', tag:'illustration', cap:'A deliberately nondeterministic stand-in for <code>Exec</code>, with the two readings defined over it word for word as Unit 22 defined them over <code>Exec</code>.',
       src:"inductive ExecND : Cmd → State → State → Prop where\n  | keep {s} : ExecND .skip s s\n  | wipe {s} : ExecND .skip s ⟨fun _ => 0, s.heap⟩\n\ndef HoareND (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', ExecND c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap\n\ndef PartialHoareND (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h s', P σ h → ExecND c ⟨σ, h⟩ s' → Q s'.store s'.heap"},
      {t:'code', tag:'illustration', cap:'The same triple, both ways. The total one is witnessed by <code>keep</code>, which changes nothing, so the precondition <i>is</i> the postcondition. The partial one is refuted by <code>wipe</code>, which sets every variable to zero: run it from a store where variable 0 holds 7 and the postcondition asks for <code>0 = 7</code>.',
       src:"example : HoareND (fact (fun σ => σ 0 = 7)) .skip (fact (fun σ => σ 0 = 7)) :=\n  fun σ h hp => ⟨⟨σ, h⟩, .keep, hp⟩\n\nexample : ¬ PartialHoareND (fact (fun σ => σ 0 = 7)) .skip (fact (fun σ => σ 0 = 7)) := by\n  intro hpar\n  have hbad := hpar (fun _ => 7) Heap.empty ⟨fun _ => 0, Heap.empty⟩ rfl .wipe\n  exact absurd hbad (by simp [fact])"},
      {t:'p', h:"So <code>partial_of_total</code> is a theorem about <i>this</i> language rather than about Hoare logic. The reading of the total triple matters here too: Unit 31 called it angelic — <i>there is</i> a run and it is good — and under nondeterminism it is the angelic reading that fails to imply the partial one. Read demonically, the total triple would be the partial one plus a termination claim, and the implication would be trivial."}
    ]},

    {t:'note', kind:'key', h:"<code>Hoare P c Q → PartialHoare P c Q</code>, and not conversely. The forward direction needs determinism and nothing else. The backward direction is false at every command that can fail to produce a run — by faulting, or by looping — and the whole subject of termination lives in that gap. Which reading a rule is proved in is therefore a decision, made per rule: the loop rule of Unit 36 is partial, because nothing about a loop can be built without a termination argument, and the variant rule of Unit 37 is total, because supplying one is exactly what it does."},

    /* ============================================== the structural rules ==== */

    {t:'sec', s:'The structural rules, run backwards'},

    {t:'p', h:"Three of Unit 22's four rules have partial counterparts with identical statements — only the word <code>Hoare</code> changes. Two of the three proofs turn inside out under that change; the third does not move at all, and why it does not is as informative as why the others do."},

    {t:'p', h:"Take sequencing. In the total reading you are given two triples and must produce a run of <code>c₁ ;; c₂</code>. You apply the first triple to get a run of <code>c₁</code> and a middle state, apply the second at that middle state to get a run of <code>c₂</code>, and glue them with <code>Exec.seq</code>. The derivation is your output. In the partial reading you are given a run of <code>c₁ ;; c₂</code> and must say something about where it lands. There is only one rule that concludes a <code>seq</code> run, so inversion splits it into a run of <code>c₁</code> and a run of <code>c₂</code> through a middle state you did not choose. The derivation is your input."},

    {t:'cmp',
     left:{t:'Total: build the derivation',
           h:"Two <code>obtain</code>s spend the hypotheses to <i>produce</i> runs, and the last line assembles them. <code>Exec.seq</code> appears in the answer.",
           src:"theorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by\n  intro σ h hp\n  obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp\n  obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq\n  exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩"},
     right:{t:'Partial: take the derivation apart',
           h:"One <code>cases</code> <i>consumes</i> the run you were handed, and the hypotheses are then applied along the two halves it produced. <code>Exec.seq</code> appears in the pattern.",
           src:"theorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R := by\n  intro σ h s' hp hex\n  cases hex with\n  | seq hex₁ hex₂ =>\n      rename_i sMid\n      exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂"}},

    {t:'p', h:"The middle state is where the reversal shows. On the left it is <code>s₁</code>, delivered by the first triple, and the second triple is applied there. On the right it is <code>sMid</code>, delivered by the inversion, and the first triple is applied <i>to</i> it — <code>h₁ σ h sMid hp hex₁</code> is the intermediate assertion, computed on the way past. Same three assertions, same order, opposite direction of travel."},

    {t:'ex',
     id:'m13-1',
     name:'partialHoare_skip, partialHoare_seq, partialHoare_consequence',
     why:"The three structural rules again with one quantifier flipped, which is the cheapest way to feel what the flip costs. <code>skip</code> and <code>seq</code> change from construction to inversion; consequence does not change at all, because it never touches a run. The shape is the one every later partial proof opens with: five <code>intro</code>s, then the run you were handed is the thing you consume. Unit 36's <code>partialHoare_while</code> opens exactly so.",
     setup:"The statements are Unit 22's with <code>Hoare</code> replaced by <code>PartialHoare</code> throughout. You need <code>Exec</code>'s constructors for inversion and nothing else; no heap lemma appears anywhere in the three proofs.",
     goal:"theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P := by\n  sorry\n\ntheorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R := by\n  sorry\n\ntheorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :\n    PartialHoare P' c Q' := by",
     hints:[
       "Unfolded, all three goals have the same five binders in the same order: a store <code>σ</code>, a heap <code>h</code>, a final state <code>s'</code>, then the precondition at <code>σ</code> and <code>h</code>, then a run of the command from <code>⟨σ, h⟩</code> to <code>s'</code>; what must be proved is the postcondition at <code>s'</code>. So <code>partialHoare_skip</code> asks for <code>P s'.store s'.heap</code> given <code>P σ h</code>, and those are two different terms until something says what <code>s'</code> is.",
       "For <code>skip</code>: the only rule concluding a <code>skip</code> run says the final state is the initial one, so take the run apart and the two terms coincide. For <code>seq</code>: the only rule concluding a <code>seq</code> run gives you two runs through a middle state, and the two hypotheses fit them in order. For consequence: no run needs to be examined at all — strengthen the precondition on the way in, weaken the postcondition on the way out.",
       "<code>cases hex</code> for <code>skip</code>; <code>cases hex with | seq hex₁ hex₂ => …</code> plus <code>rename_i</code> for <code>seq</code>; one <code>exact</code> and no <code>cases</code> at all for consequence. An entailment <code>hpre : P' ⊢ P</code> is applied as <code>hpre σ h hp</code>.",
       "<code>intro σ h s' hp hex</code> in each. In <code>partialHoare_skip</code>, <code>cases hex</code> then leaves <code>⊢ P { store := σ, heap := h }.store { store := σ, heap := h }.heap</code>, which <code>exact hp</code> closes because those two projections reduce."
     ],
     sol:"theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P := by\n  intro σ h s' hp hex\n  cases hex; exact hp\n\ntheorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R := by\n  intro σ h s' hp hex\n  cases hex with\n  | seq hex₁ hex₂ =>\n      rename_i sMid\n      exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂\n\ntheorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :\n    PartialHoare P' c Q' := by\n  intro σ h s' hp hex\n  exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)",
     solNote:"Three rules, nine lines of tactics, and the assignment rule is missing from the list on purpose: <code>hoare_assign</code> is a total rule and <code>partial_of_total</code> imports it, so there is nothing to prove.",
     expl:"<code>skip</code> and <code>seq</code> are inversions: the run is the thing you take apart, and the constructor you invert is the only one that could have concluded that command. Consequence is neither — it passes the run straight through to the hypothesis and composes an entailment on each side, exactly as the total version does, because a rule that never looks at a derivation cannot care which way the derivations are flowing.",
     walk:[
       {tac:'intro σ h s\' hp hex', h:"<code>partialHoare_skip</code>. Five names. The goal is <code>P s'.store s'.heap</code>; the hypothesis is <code>P σ h</code>. They differ in the state."},
       {tac:'cases hex', h:"There is one rule concluding <code>Exec .skip s s'</code>, and it forces <code>s' = s</code>. Inversion therefore removes <code>s'</code> from the context entirely and rewrites the goal to <code>P { store := σ, heap := h }.store { store := σ, heap := h }.heap</code>. The projections are left unreduced in the display, as they have been since Unit 22, and reduce on demand."},
       {tac:'exact hp', h:"Closes it, because that goal and <code>P σ h</code> are the same term."},
       {tac:'intro σ h s\' hp hex', h:"<code>partialHoare_seq</code>. Same opening; the run is now of <code>c₁ ;; c₂</code>."},
       {tac:'cases hex with', h:"One branch, because <code>Exec.seq</code> is the only rule whose conclusion is a <code>seq</code> run."},
       {tac:'| seq hex₁ hex₂ =>', h:"Two named premises: a run of <code>c₁</code> from the initial state to a middle state, and a run of <code>c₂</code> from that middle state to <code>s'</code>. The middle state itself is implicit in the constructor and so is not named here."},
       {tac:'rename_i sMid', h:"Names it. Before this line it is <code>s'✝</code>, which cannot be typed; after it, <code>hex₁ : Exec c₁ ⟨σ, h⟩ sMid</code> and <code>hex₂ : Exec c₂ sMid s'</code>."},
       {tac:'exact h₂ sMid.store sMid.heap s\' (h₁ σ h sMid hp hex₁) hex₂', h:"Read it inside out. <code>h₁ σ h sMid hp hex₁</code> is <code>Q</code> at the middle state — the intermediate assertion, produced rather than chosen. <code>h₂</code> is then applied at that state, at the final state <code>s'</code>, to that assertion and to the second run."},
       {tac:'intro σ h s\' hp hex', h:"<code>partialHoare_consequence</code>. Same opening a third time."},
       {tac:'exact hpost s\'.store s\'.heap (hc σ h s\' (hpre σ h hp) hex)', h:"<code>hpre σ h hp</code> turns the weaker precondition into the stronger one at the initial state; <code>hc</code> consumes it and the run, unchanged, and yields <code>Q</code> at <code>s'</code>; <code>hpost</code> at that state weakens <code>Q</code> to <code>Q'</code>. No <code>cases</code>, because the rule never asks what the run was."}
     ],
     deep:[
       {t:'trace', title:'partialHoare_skip — the contexts in full; they are short enough to print whole',
        start:"P : Assertion\n⊢ PartialHoare P Cmd.skip P",
        steps:[
          {tac:'intro σ h s\' hp hex',
           state:"P : Assertion\nσ : Store\nh : Heap\ns' : State\nhp : P σ h\nhex : Exec Cmd.skip { store := σ, heap := h } s'\n⊢ P s'.store s'.heap",
           h:"The goal is about <code>s'</code> and the hypothesis is about <code>σ</code> and <code>h</code>. Nothing here connects them; <code>s'</code> arrived as a universally quantified variable and could be any state."},
          {tac:'cases hex',
           state:"case skip\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ P { store := σ, heap := h }.store { store := σ, heap := h }.heap",
           h:"Both <code>s'</code> and <code>hex</code> have left the context — not been added to, <i>removed</i>. The only rule concluding a <code>skip</code> run has the same state on both sides, so inversion substitutes <code>⟨σ, h⟩</code> for <code>s'</code> everywhere and there is no longer a second state to be about. The goal is <code>hp</code> up to two projections."}
        ],
        done:"No goals."},
       {t:'trace', title:'partialHoare_seq — what the inversion produces (new hypotheses and the goal line only)',
        start:"⊢ PartialHoare P (c₁ ;; c₂) R",
        steps:[
          {tac:'intro σ h s\' hp hex',
           state:"σ : Store\nh : Heap\ns' : State\nhp : P σ h\nhex : Exec (c₁ ;; c₂) { store := σ, heap := h } s'\n⊢ R s'.store s'.heap",
           h:"The run of the whole sequence is a hypothesis. Nothing yet says it has two halves."},
          {tac:'cases hex with | seq hex₁ hex₂ =>',
           state:"s'✝ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s'✝\nhex₂ : Exec c₂ s'✝ s'\n⊢ R s'.store s'.heap",
           h:"<code>hex</code> is gone and three things stand in its place, one of which has an inaccessible name. The middle state exists because the derivation contained it, not because you supplied it."},
          {tac:'rename_i sMid',
           state:"sMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\n⊢ R s'.store s'.heap",
           h:"The same three hypotheses, now writable. This is the whole reason for the tactic."}
        ],
        done:"No goals."},
       {t:'code', tag:'illustration', cap:'The binder order of <code>PartialHoare</code> is a choice. Quantifying <code>s\'</code> after the precondition instead of before it gives an equivalent definition, and the translation both ways is a permutation of five arguments. Unit 22 put <code>s\'</code> at the front, which is why <code>intro</code> takes the final state third.',
        src:"def PartialHoareLate (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap\n\nexample (P Q : Assertion) (c : Cmd) : PartialHoare P c Q ↔ PartialHoareLate P c Q :=\n  ⟨fun hpar σ h hp s' hex => hpar σ h s' hp hex,\n   fun hpar σ h s' hp hex => hpar σ h hp s' hex⟩"}
     ],
     pitfall:"Opening with <code>intro σ h hp</code>, out of habit from the total rules. Lean accepts it and binds <code>hp : State</code> — the third binder of <code>PartialHoare</code> is the final state — leaving <code>⊢ P σ h → Exec Cmd.skip { store := σ, heap := h } hp → P hp.store hp.heap</code>. Nothing complains, and adding a fourth name only shifts the damage along: <code>intro σ h hp hex</code> gives <code>hp : State</code> and <code>hex : P σ h</code>, and the inversion on the next line reports <code>Tactic `cases` failed: major premise type is not an inductive type P σ h</code>. That message blames the <code>cases</code>, but the <code>cases</code> is correct and the <code>intro</code> above it is not. The same error, on the same line, is what <code>partialHoare_seq</code> gives from the same slip. The tell is in the context rather than the message: a hypothesis whose type prints as <code>State</code> under a name you chose for a proof.",
     variants:"Drop <code>rename_i sMid</code> and replace the two spelled-out projections with underscores: <code>exact h₂ _ _ s' (h₁ σ h _ hp hex₁) hex₂</code> compiles, because <code>hex₂ : Exec c₂ s'✝ s'</code> pins the middle state and structure eta solves the pair. Keep the name and delete the tactic and you get three <code>Unknown identifier</code> errors on one line. · Replace <code>cases hex with | seq …</code> by <code>obtain ⟨sMid, hex₁, hex₂⟩ := hex</code> and the names go inaccessible without any complaint at that line; the five errors arrive on the next one. · Turn the precondition entailment of <code>partialHoare_consequence</code> round — <code>hpre : P ⊢ P'</code> concluding <code>PartialHoare P' c Q'</code> — and the rule is false. Take <code>P = aFalse</code>, <code>P' = aTrue</code>, <code>c = .skip</code> and <code>Q = Q' = aFalse</code>: all three premises hold, the first two vacuously, and the conclusion says every state satisfies <code>aFalse</code>. Variance is read off the definition, and the flipped quantifier did not touch it."
    },

    /* ================================================= guards ==== */

    {t:'sec', s:'A guard is not an assertion, until you make it one'},

    {t:'p', h:"The conditional rule on paper reads: if <code>{P ∧ b} c₁ {Q}</code> and <code>{P ∧ ¬b} c₂ {Q}</code>, then <code>{P} if b then c₁ else c₂ {Q}</code>. Every symbol in it typechecks on paper. Two of them do not typecheck here. <code>P</code> is an <code>Assertion</code>, a predicate on a store and a heap. <code>b</code> is a <code>BExpr</code>, a piece of syntax. <code>b.eval σ</code> is a <code>Bool</code>, a value. There is no <code>∧</code> joining those and no <code>¬</code> applying to that."},

    {t:'p', h:"So lift the guard. The assertion wanted is: <i>the guard evaluates to <code>true</code> at this store</i>, and it says nothing at all about the heap."},

    {t:'code', cap:'Two definitions, each turning a piece of boolean syntax into an assertion. The heap binder is discarded in both — a guard reads the store and owns no memory.',
     src:"def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true\n\ndef bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false"},

    {t:'p', h:"<b>Why a definition rather than <code>fact</code>.</b> Unit 12's <code>fact</code> already lifts a store predicate to an assertion, and <code>bTrue</code> is an instance of it — the same term, checkable by <code>rfl</code>. The name is worth having because it will appear in the statement of the conditional rule and in every application of it, and because the shape <code>b.eval σ = true</code> is the shape the semantics produces, so a reader who sees <code>bTrue b</code> in a premise can predict what a proof of it will look like."},

    {t:'code', tag:'illustration', cap:'The same assertion under two spellings, equal by <code>rfl</code> because <code>fact</code> applied to a lambda beta-reduces to it.',
     src:"example (b : BExpr) : bTrue b = fact (fun σ => b.eval σ = true) := rfl"},

    {t:'p', h:"<b>Why <code>aAnd</code> rather than <code>∗</code>.</b> The rule will conjoin the guard with the precondition, and Unit 23 settled what happens if a store fact is joined with <code>∗</code>: the conjunct owns a heap of its own, and either it must be <code>pure</code> — forcing that heap empty and the whole precondition into a cut it did not ask for — or it owns an arbitrary heap and the loose reading of Unit 07 returns. Neither is wanted. The guard is a fact about the store, it consumes no memory, and the branch runs on the whole heap the conditional was entered with. <code>aAnd</code> is the connective that says that, and it is also the one whose proof is a two-slot bracket, which the next exercise depends on."},

    {t:'p', h:"<b>Why <code>bFalse b</code> rather than <code>bTrue (.not b)</code>.</b> The two assertions are equivalent, pointwise, and one <code>simp</code> proves it."},

    {t:'code', tag:'illustration', cap:'Equivalent at every store and heap: <code>BExpr.eval σ (.not b)</code> is <code>!(b.eval σ)</code>, and a boolean is <code>false</code> exactly when its negation is <code>true</code>.',
     src:"example (b : BExpr) (σ : Store) (h : Heap) : bFalse b σ h ↔ bTrue (.not b) σ h := by\n  simp [bTrue, bFalse, BExpr.eval]"},

    {t:'p', h:"Equivalent is not the same as equal, and <code>rfl</code> refuses them: <code>Tactic `rfl` failed: The left-hand side bFalse b is not definitionally equal to the right-hand side bTrue b.not</code>. That matters because of where these assertions are going. The <code>iteFalse</code> rule of <code>Exec</code> carries the premise <code>b.eval s.store = false</code>, spelled with <code>false</code> on the right. Inverting a conditional run puts that premise in your hands verbatim, and a rule stated with <code>bFalse</code> can take it as it stands."},

    {t:'code', tag:'sketch', cap:'The conditional rule with <code>bTrue (.not b)</code> in the second premise. Everything compiles except the last line, where the hypothesis handed over by inversion is offered to an assertion spelled the other way.',
     src:"theorem iteNotVariant {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bTrue (.not b))) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q := by\n  intro σ h s' hp hex\n  cases hex with\n  | iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'\n  | iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'"},

    {t:'state', cap:'The error. The <code>{ store := σ, heap := h }.store</code> in the reported type is the projection left unreduced in the display; it is not what fails. What fails is <code>= false</code> against an assertion asking for <code>= true</code> of a negation.',
     src:"error: Application type mismatch: The argument\n  hb\nhas type\n  BExpr.eval { store := σ, heap := h }.store b = false\nbut is expected to have type\n  bTrue b.not σ h\nin the application\n  ⟨hp, hb⟩"},

    {t:'p', h:"The repair is a <code>simp</code> in one branch, and the rule would then be asymmetric for no reason. Stating the assertion the way the semantics states its premise is what makes both branches cost nothing. That is a principle worth carrying: when a definition exists only to be met by a hypothesis some other definition produces, spell it the way that hypothesis is spelled."},

    /* ================================================= partial ite ==== */

    {t:'sec', s:'The conditional, given a run'},

    {t:'p', h:"Now predict the proof before writing it. The goal is a partial triple about <code>.ite b c₁ c₂</code>, so five <code>intro</code>s put a run of the conditional in your hands. Two rules conclude such a run, so inversion gives two branches. In the <code>iteTrue</code> branch you get the premise <code>b.eval s.store = true</code> and a run of <code>c₁</code>; the branch hypothesis <code>h₁</code> wants <code>aAnd P (bTrue b)</code> at the initial state and a run of <code>c₁</code>. You have the precondition already. The conjunct you are missing is precisely the premise the constructor hands you."},

    {t:'p', h:"That is the whole proof, twice."},

    {t:'ex',
     id:'m13-2',
     name:'partialHoare_ite',
     why:"The conditional rule, and the sharpest illustration on this page of what the partial reading buys: the derivation you are handed carries the information the branch hypothesis is short of, so inversion and application meet with nothing in between. Compare it with the total version in the next exercise, where the same information has to be manufactured before anything can be built. The guard vocabulary it installs is what Unit 36's loop rule is stated in: the body's precondition there is <code>aAnd I (bTrue b)</code> and the loop's postcondition is <code>aAnd I (bFalse b)</code>, the two conjuncts of this exercise with the invariant in place of <code>P</code>.",
     setup:"<code>bTrue</code> and <code>bFalse</code> are given, as above. You need the <code>iteTrue</code> and <code>iteFalse</code> constructors of <code>Exec</code>, both of which carry their guard premise first.",
     goal:"theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q := by",
     hints:[
       "Unfolded, the goal is: for every store <code>σ</code>, heap <code>h</code> and final state <code>s'</code>, if <code>P σ h</code> and <code>.ite b c₁ c₂</code> runs from <code>⟨σ, h⟩</code> to <code>s'</code>, then <code>Q s'.store s'.heap</code>. Each hypothesis says the same about one branch command, but under a precondition with a second conjunct: <code>aAnd P (bTrue b)</code> for <code>c₁</code>, <code>aAnd P (bFalse b)</code> for <code>c₂</code>.",
       "There are exactly two ways a conditional run can have been derived, and each of them tells you which way the guard went. Take the run apart and see what each case gives you.",
       "<code>cases hex with | iteTrue … | iteFalse …</code>, then one <code>exact</code> per branch. The conjunction <code>aAnd</code> is proved by a two-slot anonymous constructor.",
       "<code>intro σ h s' hp hex</code>, then <code>cases hex with</code>. In the first branch, <code>| iteTrue hb hex' =></code> puts <code>hb : BExpr.eval { store := σ, heap := h }.store b = true</code> and <code>hex' : Exec c₁ { store := σ, heap := h } s'</code> in scope — and that <code>hb</code>, despite how it prints, <i>is</i> a proof of <code>bTrue b σ h</code>, because the projection reduces to <code>σ</code>."
     ],
     sol:"theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q := by\n  intro σ h s' hp hex\n  cases hex with\n  | iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'\n  | iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'",
     solNote:"The two branches are the same line with the subscripts changed. Nothing distinguishes them except which constructor was inverted and which hypothesis is therefore applicable.",
     expl:"Five <code>intro</code>s, one <code>cases</code>, one <code>exact</code> per branch. The conjunct that the branch hypothesis needs and the precondition does not supply is the guard, and the guard premise is carried by the very constructor that put the run in the branch. So <code>⟨hp, hb⟩</code> is assembled from one thing you were given at the start and one thing the inversion produced, and no work happens in between.",
     walk:[
       {tac:'intro σ h s\' hp hex', h:"Store, heap, final state, precondition, run — the same opening as every partial rule. The goal becomes <code>Q s'.store s'.heap</code>."},
       {tac:'cases hex with', h:"Inversion on the conditional run. <code>Exec</code> has exactly two rules whose conclusion is <code>Exec (.ite b c₁ c₂) s s'</code>, so there are exactly two branches and no others to dismiss."},
       {tac:'| iteTrue hb hex\'  => exact h₁ σ h s\' ⟨hp, hb⟩ hex\'', h:"<code>hb</code> is the guard premise, <code>hex'</code> the run of the then-branch. <code>⟨hp, hb⟩</code> proves <code>aAnd P (bTrue b)</code> at <code>σ</code> and <code>h</code>: first slot the precondition, second slot the guard. <code>h₁</code> then takes the store, the heap, the final state, that pair, and the run."},
       {tac:'| iteFalse hb hex\' => exact h₂ σ h s\' ⟨hp, hb⟩ hex\'', h:"The mirror. <code>hb</code> now has <code>false</code> on the right, which is what <code>bFalse b</code> asks for; had the rule been stated with <code>bTrue (.not b)</code> this line would be the one that fails."}
     ],
     deep:[
       {t:'trace', title:'partialHoare_ite — the two branches (new hypotheses and the goal line only)',
        start:"⊢ PartialHoare P (Cmd.ite b c₁ c₂) Q",
        steps:[
          {tac:'intro σ h s\' hp hex',
           state:"σ : Store\nh : Heap\ns' : State\nhp : P σ h\nhex : Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s'\n⊢ Q s'.store s'.heap",
           h:"Neither branch hypothesis applies yet: both want a run of <code>c₁</code> or of <code>c₂</code>, and what is in scope is a run of the conditional."},
          {tac:'cases hex with | iteTrue hb hex\' =>',
           state:"case iteTrue\nhb : BExpr.eval { store := σ, heap := h }.store b = true\nhex' : Exec c₁ { store := σ, heap := h } s'\n⊢ Q s'.store s'.heap",
           h:"Two hypotheses in place of one, and the second is the run <code>h₁</code> was asking for. <code>hb</code> is the missing conjunct: the projection <code>{ store := σ, heap := h }.store</code> reduces to <code>σ</code>, so this is a proof of <code>bTrue b σ h</code>."},
          {tac:'| iteFalse hb hex\' =>',
           state:"case iteFalse\nhb : BExpr.eval { store := σ, heap := h }.store b = false\nhex' : Exec c₂ { store := σ, heap := h } s'\n⊢ Q s'.store s'.heap",
           h:"The same picture with <code>false</code> and <code>c₂</code>. The goal line is identical in both branches, because a conditional's two arms are required to establish the same postcondition."}
        ],
        done:"No goals."},
       {t:'detail', title:'The untrimmed context in the iteTrue branch', open:false, blocks:[
         {t:'state', cap:'Thirteen lines, from <code>trace_state</code> at the head of the branch. The trace above shows the last three; the ten it omits are the statement\'s own binders and hypotheses, unchanged throughout.',
          src:"case iteTrue\nP Q : Assertion\nb : BExpr\nc₁ c₂ : Cmd\nh₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q\nh₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q\nσ : Store\nh : Heap\ns' : State\nhp : P σ h\nhb : BExpr.eval { store := σ, heap := h }.store b = true\nhex' : Exec c₁ { store := σ, heap := h } s'\n⊢ Q s'.store s'.heap"}
       ]}
     ],
     pitfall:"Writing the pair the other way round. <code>⟨hb, hp⟩</code> gives <code>Application type mismatch: The argument hb has type BExpr.eval { store := σ, heap := h }.store b = true but is expected to have type P σ h in the application And.intro hb</code>. <code>aAnd P (bTrue b)</code> puts <code>P</code> first, and an anonymous constructor fills slots in order — the error names <code>And.intro</code> even though the goal was written with <code>aAnd</code>, because <code>aAnd</code> unfolds to it.",
     variants:"State the rule with <code>bTrue (.not b)</code> in the second premise and the <code>iteFalse</code> branch stops compiling, exactly as shown above the exercise. The repair is a <code>have hb' : bTrue (.not b) σ h := by simp [bTrue, BExpr.eval, hb]</code> in that branch and <code>⟨hp, hb'⟩</code> in place of <code>⟨hp, hb⟩</code>. Reusing that same simp set on the hypothesis instead — <code>simp [bTrue, BExpr.eval, hb] at hb</code> — looks like the shorter route and destroys the hypothesis: <code>hb</code> is a member of its own simp set, so it rewrites itself to <code>True</code>, and the branch then fails with <code>The argument hb has type True but is expected to have type bTrue b.not σ h</code>. Dropping <code>hb</code> from the set is no better: <code>simp at hb</code> reduces the projection and stops, leaving <code>hb : BExpr.eval σ b = false</code>, which is what you already had. · Drop <code>h₂</code> altogether and the theorem is false. Take the guard <code>0 ≠ 0</code>, which evaluates to <code>false</code> everywhere, so <code>h₁</code> holds vacuously — its precondition demands the guard be <code>true</code> — and take <code>c₂ = .skip</code>, <code>P = aTrue</code>, <code>Q = aFalse</code>: the conditional always takes the else-branch and always lands somewhere <code>aFalse</code> does not hold. · Replace <code>aAnd</code> by <code>∗</code> in the premises and the two-slot bracket is read as a cut of the heap: <code>Application type mismatch: The argument hp has type P σ h of sort `Prop` but is expected to have type Heap of sort `Type` in the application Exists.intro hp</code>. Beyond the syntax, the guard conjunct would then own a heap of its own, so <code>h₁</code> would be a statement about a strictly smaller heap than the one the branch actually runs on."
    },

    /* ================================================= total ite ==== */

    {t:'sec', s:'The conditional, building a run'},

    {t:'p', h:"The same rule in the total reading is a different proof, and the difference is not cosmetic. Unit 22's four rules are all total, so a verification that mixes a conditional with an assignment needs the conditional rule in that reading too; <code>partial_of_total</code> runs the wrong way to supply it."},

    {t:'p', h:"Start it and the asymmetry is immediate. After <code>intro σ h hp</code> the goal is an existential — produce a state, produce a run of <code>.ite b c₁ c₂</code> reaching it, and prove the postcondition there. Every rule that builds such a run demands to know how the guard evaluated, and nothing in the context says. Applying <code>h₁</code> is refused for the same reason: it wants <code>aAnd P (bTrue b)</code>, and offering <code>⟨hp, rfl⟩</code> gets <code>Application type mismatch: The argument rfl has type ?m.11 = ?m.11 but is expected to have type bTrue b σ h</code>."},

    {t:'p', h:"So split on the guard. <code>b.eval σ</code> is a <code>Bool</code>, and a <code>Bool</code> has two constructors, so <code>cases b.eval σ with | true => … | false => …</code> is available — and useless."},

    {t:'state', cap:'The state at the head of the <code>true</code> branch after a bare <code>cases b.eval σ</code>, trimmed to the five lines that matter. It is the state before the split, unchanged: the goal never mentioned <code>b.eval σ</code>, so replacing that expression by a constructor changed nothing anywhere.',
     src:"case true\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ s', Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s' ∧ Q s'.store s'.heap"},

    {t:'p', h:"The information the split discovers is thrown away by the split itself. What you need is not that <code>b.eval σ</code> <i>is</i> one of two constructors — you knew that — but a proof, in the branch, that it equals the one that branch is about. That proof is what <code>Exec.iteTrue</code> takes as its first argument, and it is also a proof of <code>bTrue b σ h</code>, because that is what <code>bTrue b</code> unfolds to. One hypothesis, two consumers."},

    {t:'p', h:"The saved-equation form of <code>cases</code> is what keeps it. It was introduced in Unit 02, on an <code>Option</code>, and every use of it in a heap proof since has been on a lookup. Here the scrutinee is a <code>Bool</code>, and the equation it saves is the guard premise the semantics demands."},

    {t:'ex',
     id:'x71',
     name:'hoare_ite',
     hard: false,
     why:"The total conditional rule, missing from the logic until now, and the reason the total fragment could not handle a branch at all. It is also the reverse of the previous exercise in the exact sense that matters: there, the derivation you were handed told you which way the guard went; here you must decide first, keep the decision as a proof, and then build a derivation that quotes it. Unit 37's <code>hoare_while_variant</code> — the total loop rule, and the only rule in the course that buys termination — opens with the same tactic on the same expression and spends the saved equation in the same two places, so the move is worth having in your hands before you meet it inside an induction.",
     setup:"<code>bTrue</code>, <code>bFalse</code> and the two <code>ite</code> constructors, as before. The saved-equation form of <code>cases</code> — <code>cases hbv : e with …</code>, which names the equation <code>hbv</code> in every branch — is the only tactic here that has not appeared in a triple proof before.",
     goal:"theorem hoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : Hoare (aAnd P (bFalse b)) c₂ Q) :\n    Hoare P (.ite b c₁ c₂) Q := by",
     hints:[
       "Unfolded, the goal is: for every store <code>σ</code> and heap <code>h</code> satisfying <code>P</code>, there <i>exists</i> a state <code>s'</code> such that <code>.ite b c₁ c₂</code> runs from <code>⟨σ, h⟩</code> to <code>s'</code> and <code>Q</code> holds there. Three binders, not five, and a run to be produced rather than consumed. Each hypothesis promises such a state for one branch command — but only from a precondition carrying a claim about the guard.",
       "You cannot prove either guard conjunct, because the guard's value is not determined by anything in scope. Split on it. Both halves of the split are then provable — in each one you know how the guard evaluated, which is exactly what both the hypothesis and the derivation-building rule are short of.",
       "<code>cases</code> on <code>b.eval σ</code>, in the form that saves the equation. Then in each branch, <code>obtain</code> the existential out of the matching hypothesis and rebuild it with the matching <code>Exec</code> constructor.",
       "<code>cases hbv : b.eval σ with | true => … | false => …</code>. In the first branch <code>hbv : b.eval σ = true</code>, which serves both as the second component of <code>⟨hp, hbv⟩</code> and as the first argument of <code>Exec.iteTrue</code>."
     ],
     sol:"theorem hoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : Hoare (aAnd P (bFalse b)) c₂ Q) :\n    Hoare P (.ite b c₁ c₂) Q := by\n  intro σ h hp\n  cases hbv : b.eval σ with\n  | true =>\n      obtain ⟨s', hex, hq⟩ := h₁ σ h ⟨hp, hbv⟩\n      exact ⟨s', Exec.iteTrue hbv hex, hq⟩\n  | false =>\n      obtain ⟨s', hex, hq⟩ := h₂ σ h ⟨hp, hbv⟩\n      exact ⟨s', Exec.iteFalse hbv hex, hq⟩",
     solNote:"<code>hbv</code> is used twice in each branch and would be used zero times without the colon. That is the entire content of the exercise.",
     expl:"The proof decides the guard, then does in each branch what the total rules always do: obtain a run from a hypothesis and rebuild it under a constructor. The final state is not chosen — it is whatever the branch's own triple produced — and the derivation is grown by one node, the <code>ite</code> step, whose premise is the equation the case split saved.",
     walk:[
       {tac:'intro σ h hp', h:"Three names, because <code>Hoare</code> has three binders. The goal is the existential: some final state, some run of the conditional reaching it, and the postcondition there."},
       {tac:'cases hbv : b.eval σ with', h:"Splits on the value of the guard at this store, and — because of the <code>hbv :</code> — records in each branch which value it was. Without the name and the colon this line changes nothing at all, since <code>b.eval σ</code> does not occur in the goal."},
       {tac:'| true =>', h:"The branch where <code>hbv : b.eval σ = true</code>. The goal is unchanged from before the split; the context has gained the one fact the rest of the branch needs."},
       {tac:'obtain ⟨s\', hex, hq⟩ := h₁ σ h ⟨hp, hbv⟩', h:"<code>⟨hp, hbv⟩</code> proves <code>aAnd P (bTrue b)</code> at <code>σ</code> and <code>h</code> — the precondition, and the guard fact the case split saved. <code>h₁</code> applied to it is an existential, and destructuring gives a final state, a run of <code>c₁</code>, and the postcondition at that state."},
       {tac:'exact ⟨s\', Exec.iteTrue hbv hex, hq⟩', h:"The same three components, with the run wrapped. <code>Exec.iteTrue</code> takes the guard premise and a run of the then-branch and returns a run of the whole conditional, ending at the same state — so <code>s'</code> and <code>hq</code> are reused untouched."},
       {tac:'| false =>', h:"<code>hbv : b.eval σ = false</code> here, which is what <code>bFalse b</code> and <code>Exec.iteFalse</code> both ask for. One case split, two branches, and each branch's equation happens to be spelled the way both of its consumers want."},
       {tac:'obtain ⟨s\', hex, hq⟩ := h₂ σ h ⟨hp, hbv⟩', h:"The mirror of the fourth line, with the else-branch's triple."},
       {tac:'exact ⟨s\', Exec.iteFalse hbv hex, hq⟩', h:"And the mirror of the fifth. The two branches never interact."}
     ],
     deep:[
       {t:'trace', title:'hoare_ite, the true branch (new hypotheses and the goal line only)',
        start:"⊢ Hoare P (Cmd.ite b c₁ c₂) Q",
        steps:[
          {tac:'intro σ h hp',
           state:"σ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ s', Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
           h:"An existential to be produced, not a hypothesis to be taken apart. Neither <code>h₁</code> nor <code>h₂</code> can be applied yet."},
          {tac:'cases hbv : b.eval σ with | true =>',
           state:"case true\nhbv : BExpr.eval σ b = true\n⊢ ∃ s', Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
           h:"The goal is untouched, which is why the bare <code>cases</code> is worthless. The gain is entirely in the new hypothesis."},
          {tac:'obtain ⟨s\', hex, hq⟩ := h₁ σ h ⟨hp, hbv⟩',
           state:"s' : State\nhex : Exec c₁ { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
           h:"A run of the branch, and the postcondition at its end. The goal wants a run of the conditional to the same place, which is one constructor away."}
        ],
        done:"No goals."},
       {t:'p', h:"Where the goal state is <i>not</i> the whole story is the guard's store. <code>hbv</code> is about <code>σ</code>; <code>Exec.iteTrue</code> asks for a premise about <code>{ store := σ, heap := h }.store</code>. Those are the same term after the projection reduces, so <code>hbv</code> is accepted in both roles without any coercion — the display shows them differently and the elaborator does not care."},
       {t:'code', tag:'illustration', cap:'The proof written with <code>by_cases</code> instead. It works, and it costs a tactic: <code>by_cases</code> splits a <i>proposition</i>, so the negative branch produces <code>¬ (b.eval σ = true)</code>, which is neither what <code>bFalse b</code> asks for nor what <code>Exec.iteFalse</code> asks for. One <code>simp</code> converts it, and the two branches are then no longer mirror images.',
        src:"theorem hoare_ite_bycases {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : Hoare (aAnd P (bFalse b)) c₂ Q) :\n    Hoare P (.ite b c₁ c₂) Q := by\n  intro σ h hp\n  by_cases hbv : b.eval σ = true\n  case pos =>\n      obtain ⟨s', hex, hq⟩ := h₁ σ h ⟨hp, hbv⟩\n      exact ⟨s', Exec.iteTrue hbv hex, hq⟩\n  case neg =>\n      simp at hbv\n      obtain ⟨s', hex, hq⟩ := h₂ σ h ⟨hp, hbv⟩\n      exact ⟨s', Exec.iteFalse hbv hex, hq⟩"}
     ],
     pitfall:"Dropping the <code>hbv :</code> and writing <code>cases b.eval σ with | true => …</code>. The split is accepted, the goal is unchanged in both branches, and the next two lines fail with <code>Unknown identifier `hbv`</code> — twice in each branch and so four times in all, because the equation was wanted in two places on each side. The error names the identifier and says nothing about the case split, so the tell is that the goal state after the split is identical to the one before it: a case split that changes no goal has discarded everything it discovered.",
     variants:"Use <code>by_cases hbv : b.eval σ = true</code> and the positive branch is unchanged while the negative one fails twice — <code>Application type mismatch: The argument hbv has type ¬BExpr.eval σ b = true but is expected to have type bFalse b σ h</code>, and the same against <code>Exec.iteFalse</code>. Inserting <code>simp at hbv</code> repairs both; the compiled version is in the fold above. · Use <code>h₂</code> in the <code>true</code> branch and the same equation is refused twice, once by the assertion and once by the constructor: <code>The argument hbv has type BExpr.eval σ b = true but is expected to have type bFalse b σ h</code>, and <code>… but is expected to have type BExpr.eval { store := σ, heap := h }.store b = false in the application Exec.iteFalse hbv</code>. Each branch has exactly one hypothesis it can consume. · Drop the guard conjunct from both premises — that is, ask for <code>Hoare P c₁ Q</code> and <code>Hoare P c₂ Q</code> — and the rule is still true and still provable by these eight lines, but it is much weaker: it can say nothing about a conditional whose branches are correct only under the guard, which is what a conditional is for."
    },

    /* ================================================= wp coda ==== */

    {t:'sec', s:'And the weakest precondition of a conditional'},

    {t:'p', h:"Unit 31 turned a verification into a fold: compute <code>wp</code> of the last command against the postcondition, feed the result back as the postcondition of the one before it, and check that the precondition entails what falls out. The fold needs one equation per command, and it stopped short of the conditional."},

    {t:'code', cap:'The weakest precondition of a conditional. It is not built out of the branches\' weakest preconditions by any operation on assertions alone: the guard has to appear, and it appears twice, selecting a side.',
     src:"theorem wp_ite (b : BExpr) (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (.ite b c₁ c₂) Q ⊣⊢\n      aOr (aAnd (bTrue b) (wp c₁ Q)) (aAnd (bFalse b) (wp c₂ Q)) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | iteTrue hb hex' => exact Or.inl ⟨hb, s', hex', hq⟩\n    | iteFalse hb hex' => exact Or.inr ⟨hb, s', hex', hq⟩\n  · intro σ h hor\n    rcases hor with ⟨hb, s', hex, hq⟩ | ⟨hb, s', hex, hq⟩\n    · exact ⟨s', Exec.iteTrue hb hex, hq⟩\n    · exact ⟨s', Exec.iteFalse hb hex, hq⟩"},

    {t:'p', h:"Read the right-hand side as a case analysis rather than as a disjunction of two possibilities: at any given store the guard has one value, so exactly one disjunct is live, and it says <i>the guard went this way, and the branch it selects is safe and lands in <code>Q</code></i>. A conditional expression on assertions would say the same thing, and this language has no such expression; the guarded disjunction is how you write one out of the connectives Unit 12 supplied."},

    {t:'p', h:"The proof is the two halves of this page, side by side. The first bullet is <code>partialHoare_ite</code>'s move — a run of the conditional is handed over and inverted, and each branch's guard premise becomes the <code>bTrue</code> or <code>bFalse</code> conjunct of the disjunct it belongs to. The second is <code>hoare_ite</code>'s — a disjunct is taken apart, its guard conjunct becomes the constructor's premise, and the run is rebuilt. Neither half needs a case split on the guard, because both are handed one: forwards by the derivation, backwards by the disjunction."},

    {t:'detail', title:'The two goal states the bullets start from', open:false, blocks:[
      {t:'state', cap:'The forwards direction, after <code>intro σ h ⟨s\', hex, hq⟩</code>. The pattern destructures the <code>wp</code> on the left of the entailment in one step, since <code>wp c Q σ h</code> is an existential.',
       src:"case left\nb : BExpr\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ aOr (aAnd (bTrue b) (wp c₁ Q)) (aAnd (bFalse b) (wp c₂ Q)) σ h"},
      {t:'state', cap:'And the backwards direction, after <code>intro σ h hor</code> and the <code>rcases</code>, in its first case. <code>⟨hb, s\', hex, hq⟩</code> is a four-slot pattern for a two-slot conjunction whose right component is itself an existential of a pair — the flattening rule of Unit 01.',
       src:"case right.inl\nb : BExpr\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\nhb : bTrue b σ h\ns' : State\nhex : Exec c₁ { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ wp (Cmd.ite b c₁ c₂) Q σ h"}
    ]},

    {t:'p', h:"The same two moves give an equation for the loop, and the equation shows why the fold stops there. A loop either fails its guard and finishes, or passes it, runs its body once, and faces the same loop again."},

    {t:'code', tag:'illustration', cap:'True, provable by the two moves of this page, and useless as a computation rule. Read the right-hand side: the second disjunct contains <code>wp (.loop b c) Q</code>, the expression the equation is about. Unfolding it produces a longer expression of the same shape, and there is no <i>n</i>th step at which it stops.',
     src:"example (b : BExpr) (c : Cmd) (Q : Assertion) :\n    wp (.loop b c) Q ⊣⊢\n      aOr (aAnd (bFalse b) Q) (aAnd (bTrue b) (wp c (wp (.loop b c) Q))) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | loopFalse hb => exact Or.inl ⟨hb, hq⟩\n    | loopTrue hb hbody hrest => exact Or.inr ⟨hb, _, hbody, s', hrest, hq⟩\n  · intro σ h hor\n    rcases hor with ⟨hb, hq⟩ | ⟨hb, s₁, hbody, s₂, hrest, hq⟩\n    · exact ⟨⟨σ, h⟩, Exec.loopFalse hb, hq⟩\n    · exact ⟨s₂, Exec.loopTrue hb hbody hrest, hq⟩"},

    {t:'note', kind:'info', h:"<code>wp_ite</code> is stated for <code>wp</code>, which Unit 31 defined with the existential in it — the total reading. So the fold now computes total correctness through a conditional. Through a loop it computes nothing, and the equation above says why: the calculus needs the weakest precondition of a loop to be <i>given</i>, not unfolded. That is what an invariant is."},

    {t:'dod', h:"You can state both readings of a triple, say which quantifier moved and what the conjunction became, and say at which commands they disagree. You can prove <code>partial_of_total</code>, name determinism as its only ingredient, and produce the two-rule semantics that makes it false. You can refute the converse with a faulting load. You can prove the three partial structural rules, and say for each whether it takes the derivation apart or never looks at it, and what its total counterpart did instead. You can lift a guard into an assertion, defend <code>aAnd</code> against <code>∗</code> and <code>bFalse</code> against <code>bTrue (.not b)</code>, and predict the exact hypothesis an inversion will hand you. You can prove the conditional rule in both readings, and say why the second needs a case split that the first gets for free — and why that split must save its equation."},

    {t:'p', h:"Every rule so far was proved by looking at one derivation, or by building one. A loop's derivation has unknown height, and the command it is about is <i>fixed</i> while the induction wants to generalise it. That mismatch has a standard fix, you saw it once in Unit 26, and now it is compulsory."}

  ]
});
