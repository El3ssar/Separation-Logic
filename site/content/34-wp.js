registerChapter({
  id: 'wp',
  num: '31',
  phase: 'Phase 6 · Verification',
  title: 'Weakest preconditions',
  blurb: 'One definition that computes the intermediate assertions instead of guessing them — and the discovery that it was not a new idea at all, but the definition of a Hoare triple read from the other end.',

  orient: {
    youWill: [
      'Define <code>wp c Q</code> and say precisely which states it collects, and which of the two obvious readings the definition takes.',
      'Prove that <code>Hoare P c Q</code> and <code>P ⊢ wp c Q</code> are the same proposition, and say what a proof by <code>Iff.rfl</code> is claiming.',
      'Compute <code>wp</code> for <code>skip</code>, <code>assign</code> and <code>seq</code> by two moves — invert a derivation going forwards, build one going backwards.',
      'Re-derive all four structural rules of Unit 22 from three equations and a monotonicity lemma.',
      'State, rather than feel, what the word <i>weakest</i> means: a soundness theorem and an optimality theorem.',
      'Compute <code>wp</code> against a real postcondition for <code>free</code> and for <code>write</code>, and recognise the existential over the value the command never reads.',
      'Decide whether a precondition you wrote is the weakest one, and produce a counterexample when it is not.',
      'Transport the frame rule to <code>wp</code> in one term, and explain why that term typechecks.'
    ],
    needs: [
      'Unit 22: <code>Hoare</code> and its existential, <code>PartialHoare</code>, <code>subst</code>, and the four structural rules.',
      'Unit 19: <code>Exec</code> and inversion by <code>cases … with | ctor …</code>; <code>rename_i</code>.',
      'Unit 12: <code>⊢</code>, <code>⊣⊢</code>, <code>entails_trans</code>, <code>equiv_trans</code>, <code>aExists</code>.',
      'Units 05–06: <code>singleton_same</code>, <code>singleton_other</code>, <code>write_other</code>, <code>erase_other</code>, <code>write_singleton</code>, <code>erase_singleton</code>.',
      'Unit 27: <code>hoare_frame</code>, and Unit 24&rsquo;s <code>HeapLocal</code> and <code>Preserves</code>.'
    ],
    payoff: 'Practical verification tools are built on this definition, and the reason is on this page: it turns the one creative act in a proof — choosing what goes between two commands — into a calculation that runs from the postcondition backwards. It also closes the account on Hoare triples, by showing there was only ever one object.'
  },

  blocks: [

    /* ============================================== the missing function ==== */

    {t:'p', h:"The function that computes them has been inside the definition of a Hoare triple since Unit 22. Take the last command of <code>swap</code>, <code>[l₂] := tmp₁</code>, and the postcondition <code>(l₁ ↦ b) ∗ (l₂ ↦ a)</code>. There is a set of states from which that command runs and lands in that postcondition. Nothing was chosen: the command and the postcondition determine the set. Every assertion on the previous page was an attempt to describe such a set by hand."},

    {t:'p', h:"So name the set. It is a predicate on stores and heaps, which is exactly what an <code>Assertion</code> is, so the thing being named is an assertion — one built from a command and another assertion. Before writing it down, decide what &ldquo;runs and lands in&rdquo; is going to mean, because there are two readings and they are not equivalent."},

    {t:'cmp',
     left:{t:'The angelic reading', kind:'good', h:"<b>There exists</b> a run of <code>c</code> from this state, and it ends in <code>Q</code>. Being in the set is a promise that the command finishes, does not fault, and delivers <code>Q</code>."},
     right:{t:'The demonic reading', h:"<b>For every</b> run of <code>c</code> from this state, it ends in <code>Q</code>. Being in the set promises nothing about whether the command finishes at all — a state from which <code>c</code> faults immediately is in the set, vacuously."}},

    {t:'p', h:"Unit 22 made this choice once already, and made it in the first column: <code>Hoare</code> quantifies existentially over the final state, and <code>PartialHoare</code> — the definition kept for contrast and used nowhere since — quantifies universally. Taking the second column here would produce a definition that does not match the triple the last nine units have been about. So the first column it is, and the definition is two lines with nothing new in them."},

    {t:'code', cap:'The command runs, and where it lands satisfies <code>Q</code>. The state is split into its two halves on the way in, because an <code>Assertion</code> takes a store and a heap, and glued back into a <code>State</code> for <code>Exec</code>.',
     src:"def wp (c : Cmd) (Q : Assertion) : Assertion :=\n  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap"},

    {t:'defn', term:'Weakest precondition',
     h:"<code>wp c Q</code> is the assertion holding of exactly those states from which <code>c</code> runs safely into <code>Q</code>: there is a run, it finishes, and where it finishes satisfies <code>Q</code>. It is called <i>weakest</i> because it is the largest such assertion in the entailment order: any <code>P</code> for which the triple <code>Hoare P c Q</code> holds is contained in it. That claim is two theorems, and you prove both of them below.",
     cap:'A function from a command and a postcondition to a precondition is called a <i>predicate transformer</i>. This one transforms backwards: the postcondition is the input.'},

    {t:'p', h:"One word in that card is doing work that has not been paid for. <i>Largest</i> presumes a comparison, and the comparison is <code>⊢</code>, which Unit 12 proved is a preorder and not a partial order — two assertions can each entail the other without being equal. So <code>wp c Q</code> is a greatest element of the set of valid preconditions, not <i>the</i> greatest, and any two greatest elements are related by <code>⊣⊢</code>. That is the strongest uniqueness statement available and it is the one the exercises will state."},

    /* ================================================ one thing, not two ==== */

    {t:'sec', s:'One statement, not two'},

    {t:'p', h:"Now put the definition of <code>wp</code> next to the definition of <code>Hoare</code> and read them against each other. <code>Hoare P c Q</code> is <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>. The part after the arrow is the body of <code>wp c Q</code>, applied to the same <code>σ</code> and <code>h</code>. And <code>∀ σ h, P σ h → R σ h</code> is what <code>P ⊢ R</code> unfolds to."},

    {t:'p', h:"So the two propositions are not two. They are one expression, written with different abbreviations folded in. Lean has a word for that, and a proof term for it."},

    {t:'code', cap:'The whole proof. <code>Iff.rfl</code> is reflexivity of <code>↔</code>: it proves <code>A ↔ A</code>, and nothing else.',
     src:"theorem hoare_iff_entails_wp (P Q : Assertion) (c : Cmd) :\n    Hoare P c Q ↔ P ⊢ wp c Q := Iff.rfl"},

    {t:'note', kind:'key', title:'What <code>Iff.rfl</code> claims',
     h:"<code>Iff.rfl</code> has type <code>?a ↔ ?a</code> — one metavariable, used twice. Offering it against the goal <code>Hoare P c Q ↔ P ⊢ wp c Q</code> asks Lean to solve <code>?a</code> against <b>both</b> sides at once, which succeeds only if the two sides are the same term after unfolding definitions. It is not a theorem relating two objects. It is the observation that there is one object, and that the two names for it were introduced nine units apart."},

    {t:'code', tag:'illustration', cap:'The same fact three ways. The first is <code>rfl</code> at <code>Prop</code>: the two propositions are equal, and not only equivalent. The second and third unfold each side to the same explicit statement.',
     src:"example (P Q : Assertion) (c : Cmd) : Hoare P c Q = (P ⊢ wp c Q) := rfl\n\nexample (P Q : Assertion) (c : Cmd) :\n    Hoare P c Q ↔ (∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap) := Iff.rfl\n\nexample (P Q : Assertion) (c : Cmd) :\n    (P ⊢ wp c Q) ↔ (∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap) := Iff.rfl"},

    {t:'p', h:"The consequence is practical and it is immediate. Anywhere a <code>Hoare</code> triple is expected you may supply an entailment into a <code>wp</code>, and the other way round, with no coercion and no lemma — <code>exact</code> accepts it because the elaborator unfolds both. Half the terms below are one-liners for that reason alone."},

    {t:'detail', title:'Why the same line fails for <code>PartialHoare</code>', tag:'aside', open:false, blocks:[
      {t:'p', h:"The demonic reading is not an idle alternative; it is <code>PartialHoare</code>, defined in Unit 22 and used nowhere since. Try the same proof against it."},
      {t:'code', tag:'sketch', cap:'This does not compile.',
       src:"theorem partial_iff_entails_wp (P Q : Assertion) (c : Cmd) :\n    PartialHoare P c Q ↔ P ⊢ wp c Q := Iff.rfl"},
      {t:'state', cap:'Lean reports the metavariable unsolved: it could not make one term out of the two sides.',
       src:"error: Type mismatch\n  Iff.rfl\nhas type\n  ?m.1 ↔ ?m.1\nbut is expected to have type\n  PartialHoare P c Q ↔ P ⊢ wp c Q"},
      {t:'p', h:"The reason is the quantifier. <code>PartialHoare P c Q</code> is <code>∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap</code>: the final state is bound outermost and universally. <code>wp</code> binds it innermost and existentially. No amount of unfolding turns one into the other, and it would be wrong if it did — the two say different things about a command that faults."},
      {t:'p', h:"There is a partial-correctness predicate transformer, obtained by moving the quantifier in <code>wp</code>&rsquo;s body the same way. It is not defined here, because nothing in this course needs it and a definition with no question attached is what this course is trying to avoid."}
    ]},

    /* ==================================================== three equations ==== */

    {t:'sec', s:'Three equations'},

    {t:'p', h:"A definition is not yet a calculus. To compute <code>wp c Q</code> for a compound <code>c</code> you want equations that push <code>wp</code> through the structure of the command until nothing is left but the postcondition and the small commands. Here are the first three, and every one of them is proved by the same two moves."},

    {t:'ol', items:[
      "<b>Left to right</b>, you are handed a run of <code>c</code> and have to produce information about the starting state. You invert the derivation: <code>cases hex</code>, and the constructor tells you what the final state was.",
      "<b>Right to left</b>, you are handed information about the starting state and have to produce a run. You build the derivation: name the final state, apply the constructor, hand over the postcondition proof."
    ]},

    {t:'p', h:"Both directions are needed because these are <code>⊣⊢</code> statements, and a <code>⊣⊢</code> is a pair. Unit 12 proved <code>⊣⊢</code> facts by writing the pair out with <code>⟨…, …⟩</code>; from here on the goals are big enough that it is worth splitting the pair with <code>constructor</code> and proving the halves as separate tactic blocks. <code>intro</code> on an unsplit <code>⊣⊢</code> goal does nothing at all — <code>AssertionEquiv</code> is a conjunction, not a function type, so there is no binder to introduce."},

    {t:'state', cap:'What <code>intro σ h</code> says if you try it before <code>constructor</code>.',
     src:"error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce\n\nQ : Assertion\n⊢ wp Cmd.skip Q ⊣⊢ Q"},

    /* --------------------------------------------------------- m12-1 --- */

    {t:'ex',
     id:'m12-1',
     name:'wp_skip / wp_assign',
     why:"These are your first two computations of a predicate transformer, and they are the two easiest, so the pattern is visible before the goals get large. <code>wp_assign</code> also settles an old debt. Unit 22 defined <code>subst</code> semantically — compose the assertion with the store update — and defended it on economy: with no syntax of assertions there is no substitution lemma and no induction to do. Economy is a reason to like a definition, not a reason to believe it is the right one. Here it is not a definition to accept but the answer to a computation: the weakest precondition of an assignment <i>is</i> the substituted postcondition, and there is nothing else it could be.",
     setup:"Two theorems under one marker. <code>subst x e Q</code> is Unit 22&rsquo;s <code>fun σ h => Q (Store.set σ x (e.eval σ)) h</code>. The two <code>Exec</code> constructors you need are <code>Exec.skip</code> and <code>Exec.assign</code>; both have no premises.",
     goal:"theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q := by\n\ntheorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :\n    wp (.assign x e) Q ⊣⊢ subst x e Q := by",
     hints:[
       "Unfolded, <code>wp .skip Q ⊣⊢ Q</code> is two entailments. Left to right: for every <code>σ</code> and <code>h</code>, if there is a state <code>s'</code> with <code>Exec .skip ⟨σ, h⟩ s'</code> and <code>Q s'.store s'.heap</code>, then <code>Q σ h</code>. Right to left: if <code>Q σ h</code>, then such an <code>s'</code> exists. The second theorem unfolds identically with <code>subst x e Q σ h</code> — that is, <code>Q (Store.set σ x (e.eval σ)) h</code> — standing where <code>Q σ h</code> stands here.",
       "Going left to right you know a run of <code>skip</code> exists but not yet what it did; the rule for <code>skip</code> says the final state is the initial one, so read that off the derivation. Going right to left you have to supply the final state yourself, and for <code>skip</code> there is only one candidate. The assignment differs in one place only: its rule fixes a different final state — same heap, store updated at <code>x</code> — so the same two moves work, and all that changes is which state you read off and which state you supply.",
       "<code>constructor</code> splits the <code>⊣⊢</code>. <code>intro σ h ⟨s', hex, hq⟩</code> takes the three binders of an entailment and destructures the existential in one go. <code>cases hex</code> inverts the run. In the other direction the anonymous constructor builds the whole existential: state, derivation, postcondition proof.",
       "Start <code>constructor</code>, then <code>· intro σ h ⟨s', hex, hq⟩</code>. That leaves <code>hex : Exec Cmd.skip { store := σ, heap := h } s'</code> and <code>hq : Q s'.store s'.heap</code> with goal <code>⊢ Q σ h</code> — so the only thing standing between you and <code>exact hq</code> is that Lean does not yet know <code>s'</code> is <code>⟨σ, h⟩</code>. <code>wp_assign</code> is the same four lines with <code>Exec.assign</code> in place of <code>Exec.skip</code>; the state you supply in its backward direction is the one the rule builds, and it is the state <code>subst</code> evaluates <code>Q</code> at."
     ],
     sol:"theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex; exact hq\n  · intro σ h hq\n    exact ⟨⟨σ, h⟩, Exec.skip, hq⟩\n\ntheorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :\n    wp (.assign x e) Q ⊣⊢ subst x e Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex; exact hq\n  · intro σ h hq\n    exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
     solNote:"The two proofs are the same five lines with the witness state and the constructor name changed. That is not an accident of these two commands: it is the shape every <code>wp</code> equation for a command with one rule takes, and it is why the next three exercises feel familiar even as the goals grow.",
     expl:"Left to right, inversion replaces the unknown <code>s'</code> by whatever the rule says the final state is, which converts <code>hq</code> from a statement about <code>s'</code> into a statement about the initial state. Right to left, you supply that same state explicitly and the rule accepts it. The only difference between the two theorems is which state that is: <code>⟨σ, h⟩</code> for <code>skip</code>, and the store updated at <code>x</code> for the assignment.",
     walk:[
       {tac:'constructor', h:"Splits <code>⊣⊢</code> into its two components, <code>case left</code> and <code>case right</code>. <code>AssertionEquiv</code> is a conjunction of two entailments, so this is the same <code>constructor</code> that splits an <code>∧</code>."},
       {tac:'intro σ h ⟨s\', hex, hq⟩', h:"Four things at once. Three binders come from the entailment — the store, the heap, and the proof of the left-hand assertion — and the fourth is a pattern that opens the existential in <code>wp</code> into a state, a derivation and a postcondition proof."},
       {tac:'cases hex', h:"Inverts the run. <code>Exec</code> has exactly one rule concluding a run of <code>skip</code>, and its conclusion fixes the final state, so <code>s'</code> disappears and <code>hq</code> is restated at the initial state — with the structure literal left unreduced, which <code>exact</code> does not mind."},
       {tac:'exact hq', h:"<code>hq : Q { store := σ, heap := h }.store { store := σ, heap := h }.heap</code> and the goal is <code>Q σ h</code>. Those are the same term after projecting the literal, so this closes."},
       {tac:'intro σ h hq', h:"The other direction. No pattern this time: the hypothesis is <code>Q σ h</code> and nothing more, and the existential has moved into the goal."},
       {tac:'exact ⟨⟨σ, h⟩, Exec.skip, hq⟩', h:"Builds the existential. The outer bracket supplies the witness state and then flattens into the conjunction: the derivation, and the proof that <code>Q</code> holds there. For the assignment the witness is <code>⟨Store.set σ x (e.eval σ), h⟩</code>, which is precisely the state <code>Exec.assign</code> produces — and precisely the state <code>subst</code> evaluates <code>Q</code> at."}
     ],
     deep:[
       {t:'trace', title:'wp_skip, both directions',
        start:"Q : Assertion\n⊢ wp Cmd.skip Q ⊣⊢ Q",
        steps:[
          {tac:'constructor',
           state:"case left\nQ : Assertion\n⊢ wp Cmd.skip Q ⊢ Q\n\ncase right\nQ : Assertion\n⊢ Q ⊢ wp Cmd.skip Q",
           h:"Two goals, one per component, and the entailments point in opposite directions. The two bullets below take them in order."},
          {tac:'intro σ h ⟨s\', hex, hq⟩',
           state:"case left\nQ : Assertion\nσ : Store\nh : Heap\ns' : State\nhex : Exec Cmd.skip { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ Q σ h",
           h:"The goal is now about the initial state and the hypothesis about an unknown final one. Nothing connects them yet, which is exactly what <code>hex</code> is for."},
          {tac:'cases hex',
           state:"case left.skip\nQ : Assertion\nσ : Store\nh : Heap\nhq : Q { store := σ, heap := h }.store { store := σ, heap := h }.heap\n⊢ Q σ h",
           h:"<code>s'</code> is gone and <code>hq</code> now speaks about the initial state, spelled as projections of a structure literal. The single branch is named <code>skip</code> after the only applicable rule."},
          {tac:'intro σ h hq',
           state:"case right\nQ : Assertion\nσ : Store\nh : Heap\nhq : Q σ h\n⊢ wp Cmd.skip Q σ h",
           h:"The second component. The goal is a <code>wp</code> applied to a store and a heap — an existential waiting for a witness."}
        ],
        done:'No goals.'},
       {t:'p', h:"The assignment&rsquo;s inversion produces the same shape with a much larger display, because the state <code>Exec.assign</code> builds is a structure literal containing another one."},
       {t:'state', cap:'After <code>cases hex</code> in <code>wp_assign</code>, left to right. Every occurrence of <code>{ store := σ, heap := h }</code> is a projection Lean has not bothered to reduce; the goal is closed by <code>exact hq</code> regardless.',
        src:"case left.assign\nx : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\nhq :\n  Q\n    { store := { store := σ, heap := h }.store.set x (Atom.eval { store := σ, heap := h }.store e),\n        heap := { store := σ, heap := h }.heap }.store\n    { store := { store := σ, heap := h }.store.set x (Atom.eval { store := σ, heap := h }.store e),\n        heap := { store := σ, heap := h }.heap }.heap\n⊢ subst x e Q σ h"}
     ],
     pitfall:"Reaching for <code>exact hq</code> before <code>cases hex</code>. It looks as though it should work, because <code>hq</code> is a proof of <code>Q</code> at <i>some</i> state, and Lean answers <code>Type mismatch … has type Q s'.store s'.heap but is expected to have type Q σ h</code>. The message is the point: until the derivation is inverted, <code>s'</code> is an arbitrary state and there is no reason for <code>Q</code> to hold at the initial one.",
     variants:"Reverse the equation for the assignment and it stays true — <code>⊣⊢</code> is symmetric, and <code>equiv_symm</code> from Unit 12 turns one into the other. What does not survive is weakening either side to a single entailment and expecting the other: <code>subst x e Q ⊢ wp (.assign x e) Q</code> alone is the assignment rule of Unit 22, and it says nothing about the precondition being weakest. Both directions are the content."},

    {t:'p', h:"Now the interesting one. <code>skip</code> and <code>assign</code> are single commands; <code>;;</code> is where a calculus either appears or does not."},

    {t:'p', h:"Ask what the weakest precondition of <code>c₁ ;; c₂</code> against <code>Q</code> should be. Whatever <code>c₁</code> leaves behind has to be enough for <code>c₂</code> to reach <code>Q</code> — that is, it has to satisfy <code>wp c₂ Q</code>. So the states you may start in are the states from which <code>c₁</code> reaches <code>wp c₂ Q</code>. Composition of commands becomes composition of transformers, in the opposite order."},

    /* --------------------------------------------------------- m12-2 --- */

    {t:'ex',
     id:'m12-2',
     name:'wp_seq',
     hard:false,
     why:"This is the equation that makes backwards reasoning a method rather than a slogan. Read right to left it says: to verify <code>c₁ ;; c₂ ;; … ;; cₙ</code> against <code>Q</code>, start at <code>Q</code>, apply <code>wp cₙ</code>, then <code>wp cₙ₋₁</code>, and keep going. The previous unit&rsquo;s four hand-chosen assertions were the four stages of that fold, computed by hand. Nothing else in this course turns a search into a calculation as directly.",
     setup:"The command is <code>c₁ ;; c₂</code>, so the only rule that can conclude the run is <code>Exec.seq</code>, which carries a middle state. Both directions have to handle that middle state, and it is the one place the two directions are not mirror images.",
     goal:"theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q) := by",
     hints:[
       "Left to right: given a run of <code>c₁ ;; c₂</code> from <code>⟨σ, h⟩</code> to some <code>s''</code> with <code>Q</code> true at <code>s''</code>, show that <code>wp c₁ (wp c₂ Q)</code> holds at <code>σ</code> and <code>h</code>. Unfolded, that is a nested existential: a state reachable by <code>c₁</code>, from which a further state is reachable by <code>c₂</code>, satisfying <code>Q</code>. Right to left is that nested existential taken apart and reassembled as one run.",
       "The run of a sequence is built from two runs with a state in the middle. Going forwards, inversion hands you that middle state and both halves; you have to re-present it as the witness of the outer existential and the two halves as the two inner claims. Going backwards you have both halves already and must glue them.",
       "Inversion on a rule with premises needs the named form, <code>cases hex with | seq h₁ h₂ => …</code>, because you want the two sub-derivations. In the other direction <code>Exec.seq</code> takes the two sub-derivations and produces the composite. The destructuring <code>intro</code> pattern nests: <code>⟨s₁, hex₁, s₂, hex₂, hq⟩</code>.",
       "Start <code>constructor</code>, then <code>· intro σ h ⟨s'', hex, hq⟩</code> and <code>cases hex with | seq h₁ h₂ => …</code>. That leaves the middle state as an inaccessible <code>s'✝</code>, which you never have to name: write the witness as <code>_</code> and let <code>h₁</code> determine it."
     ],
     sol:"theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q) := by\n  constructor\n  · intro σ h ⟨s'', hex, hq⟩\n    cases hex with\n    | seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩\n  · intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩\n    exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",
     solNote:"Six lines, and the whole of backwards reasoning is in them. What is <i>not</i> in them: any assumption that <code>c₁</code> has one outcome. The equation holds whichever run the existential picks.",
     expl:"Both directions are re-bracketing the same data. A run of <code>c₁ ;; c₂</code> ending in <code>Q</code> is a middle state, a run of <code>c₁</code> to it, a run of <code>c₂</code> from it, and a proof of <code>Q</code>; and <code>wp c₁ (wp c₂ Q)</code> unfolds to exactly those four things nested the other way. Inversion turns the composite into its parts, and <code>Exec.seq</code> turns the parts back into the composite.",
     walk:[
       {tac:'constructor', h:"Splits the <code>⊣⊢</code> into its two entailments, which become the two bullets. They are not mirror images here: the forward one has to <i>find</i> the middle state inside a derivation, the backward one is handed it and has to glue two derivations around it."},
       {tac:'intro σ h ⟨s\'\', hex, hq⟩', h:"Opens the outer existential in the left-hand side. <code>s''</code> is the <i>final</i> state of the whole sequence, not the middle one."},
       {tac:'cases hex with | seq h₁ h₂ =>', h:"Inverts the composite run. The middle state arrives inaccessible as <code>s'✝</code> because the named form gives names to the premises and not to the existentially bound index; the two premises are <code>h₁ : Exec c₁ { store := σ, heap := h } s'✝</code> and <code>h₂ : Exec c₂ s'✝ s''</code>."},
       {tac:'exact ⟨_, h₁, ⟨s\'\', h₂, hq⟩⟩', h:"Builds the nested existential. The outer witness is the middle state, written <code>_</code> and recovered by unifying with <code>h₁</code>&rsquo;s type; the inner one is the final state, which is still named. The proof term therefore mentions a state whose name the reader is not allowed to type — a good reason to write <code>_</code> rather than fight for a name."},
       {tac:'intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩', h:"The other direction, and the pattern goes two deep in one go: a state and a run for <code>c₁</code>, then inside the postcondition a second state, run and proof."},
       {tac:'exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩', h:"Glues. <code>Exec.seq</code> wants the second run to start where the first ended, and the first ended at <code>s₁</code> while <code>hex₂</code> starts at <code>{ store := s₁.store, heap := s₁.heap }</code>. Those are the same state by structure eta, so nothing has to be said."}
     ],
     deep:[
       {t:'trace', title:'wp_seq, the three states that matter',
        start:"c₁ c₂ : Cmd\nQ : Assertion\n⊢ wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q)",
        steps:[
          {tac:'intro σ h ⟨s\'\', hex, hq⟩',
           state:"case left\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns'' : State\nhex : Exec (c₁ ;; c₂) { store := σ, heap := h } s''\nhq : Q s''.store s''.heap\n⊢ wp c₁ (wp c₂ Q) σ h",
           h:"One run, one postcondition proof, and a goal that wants two runs. The middle state does not exist yet as a name."},
          {tac:'cases hex with | seq h₁ h₂ =>',
           state:"case left.seq\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns'' : State\nhq : Q s''.store s''.heap\ns'✝ : State\nh₁ : Exec c₁ { store := σ, heap := h } s'✝\nh₂ : Exec c₂ s'✝ s''\n⊢ wp c₁ (wp c₂ Q) σ h",
           h:"There it is, daggered. The goal is unchanged, and everything needed to fill it is now in the context — which is what makes the next line a single <code>exact</code>."},
          {tac:'intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩',
           state:"case right\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\ns₂ : State\nhex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂\nhq : Q s₂.store s₂.heap\n⊢ wp (c₁ ;; c₂) Q σ h",
           h:"Both middle states are named here, and <code>hex₂</code> starts at <code>s₁</code> rebuilt from its own projections. <code>Exec.seq</code> accepts it because a structure is equal to the record of its fields."}
        ],
        done:'No goals.'}
     ],
     pitfall:"Writing <code>cases hex</code> without <code>with | seq h₁ h₂</code>. The branch appears with all three of its contents inaccessible — <code>s'✝</code>, <code>h₁✝</code>, <code>h₂✝</code> — and the inversion itself reports nothing at all. The failure surfaces on the next line instead, twice over: <code>Unknown identifier `h₁`</code> and <code>Unknown identifier `h₂`</code>, both pointing inside the <code>exact</code> term. Nothing in either message mentions <code>cases</code>, which is why the fix is not obvious from the error: name the premises whenever you intend to use them.",
     variants:"Drop the middle <code>wp</code> and ask for <code>wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ Q</code>, and it breaks in the right-to-left direction: take <code>c₁ = skip</code>, <code>c₂ = free 0</code> and <code>Q = emp</code>, and the empty heap is in <code>wp .skip emp</code> while freeing an unallocated address faults, so it is in nothing on the left. The more tempting error is to expect an ordering fact: that <code>wp (c₁ ;; c₂) Q ⊣⊢ wp c₂ (wp c₁ Q)</code>. That fails left to right at <code>c₁ = [0] := 1</code>, <code>c₂ = free 0</code>, <code>Q = emp</code>: the one-cell heap at <code>0</code> is in the left-hand side, and the right-hand side is inhabited by nothing at all. Its innermost transformer is <code>wp ([0] := 1) emp</code>, and no state is in that one — a write leaves the cell it wrote allocated, so it never lands in <code>emp</code>. Transformers compose in the reverse of the order the commands run, because the postcondition travels backwards through the program, and reversing the two is the same mistake as reversing a composition of functions."},

    {t:'p', h:"Written out for four commands, the equation is a fold. This is the previous unit&rsquo;s table with the guessing removed."},

    {t:'txt', cap:'The four assertions of a four-command program, computed rather than chosen. Each line is the one below it with one more transformer applied.',
     src:"wp (c₁ ;; c₂ ;; c₃ ;; c₄) post\n  ⊣⊢  wp c₁ (wp (c₂ ;; c₃ ;; c₄) post)\n  ⊣⊢  wp c₁ (wp c₂ (wp (c₃ ;; c₄) post))\n  ⊣⊢  wp c₁ (wp c₂ (wp c₃ (wp c₄ post)))\n\n       A₃  =  wp c₄ post\n       A₂  =  wp c₃ A₃\n       A₁  =  wp c₂ A₂\n       pre =  wp c₁ A₁"},

    {t:'p', h:"One thing is missing from that chain, and it is not a formality. Getting from the first line to the second is one application of <code>wp_seq</code>. Getting from the second to the third means rewriting <i>underneath</i> <code>wp c₁</code>, and nothing so far licenses that. A transformer that could turn an entailment into a non-entailment would make the fold meaningless."},

    /* --------------------------------------------------------- m12-3 --- */

    {t:'ex',
     id:'m12-3',
     name:'wp_mono',
     why:"Without this the fold above does not typecheck past its second line: <code>wp_seq</code> rewrites the argument of <code>wp c₁</code>, and only a congruence law lets you do that. It is also what makes <code>wp c</code> a map of the entailment preorder <i>to itself</i> rather than an arbitrary function on assertions: it respects the order, which is what a monotone function on a preorder is.",
     setup:"Two assertions, an entailment between them, and one command. Nothing about the command is used: the proof works for every <code>c</code>, and never inverts or builds a derivation.",
     goal:"theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q' := by",
     hints:[
       "Unfolded: for every <code>σ</code> and <code>hh</code>, if there is a state reachable by <code>c</code> satisfying <code>Q</code>, then there is a state reachable by <code>c</code> satisfying <code>Q'</code>. Both existentials range over the same runs.",
       "The same run works. Take the state the first existential gives you, keep the derivation exactly as it is, and upgrade only the postcondition proof, using the entailment you were handed.",
       "One <code>intro</code> carrying a destructuring pattern and one <code>exact</code> are the whole proof — no <code>cases</code>, because no derivation is inverted, and no lemma about <code>Exec</code>. The entailment <code>h</code> is a function: applied to a store, a heap and a proof of <code>Q</code> there, it returns a proof of <code>Q'</code> there. The state to apply it at is <code>s'</code>, so its two components are <code>s'.store</code> and <code>s'.heap</code>.",
       "<code>intro σ hh ⟨s', hex, hq⟩</code> leaves <code>⊢ wp c Q' σ hh</code> with <code>hex</code> and <code>hq</code> in hand. The witness and the derivation are reused verbatim; only the third slot changes."
     ],
     sol:"theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q' := by\n  intro σ hh ⟨s', hex, hq⟩\n  exact ⟨s', hex, h s'.store s'.heap hq⟩",
     solNote:"The heap is called <code>hh</code> and not <code>h</code> because <code>h</code> is already the entailment. Renaming is cosmetic here, but in a longer proof shadowing a hypothesis you still need is a real cost.",
     expl:"Monotonicity of <code>wp c</code> costs nothing because <code>wp</code> quantifies over runs and the runs do not depend on the postcondition. The same witness serves both existentials; only the last component is replaced, by applying the given entailment at the state that witness names.",
     walk:[
       {tac:'intro σ hh ⟨s\', hex, hq⟩', h:"Three binders of the entailment plus a destructuring of the existential in <code>wp c Q</code>. Afterwards the goal is <code>wp c Q' σ hh</code> — the same shape with a different postcondition."},
       {tac:'exact ⟨s\', hex, h s\'.store s\'.heap hq⟩', h:"Rebuilds the existential with two of its three components untouched. <code>h s'.store s'.heap hq</code> is an entailment applied to a store, a heap and a premise, which is how Unit 12 said entailments are used."}
     ],
     deep:[
       {t:'trace', title:'wp_mono, before and after',
        start:"Q Q' : Assertion\nc : Cmd\nh : Q ⊢ Q'\n⊢ wp c Q ⊢ wp c Q'",
        steps:[
          {tac:'intro σ hh ⟨s\', hex, hq⟩',
           state:"Q Q' : Assertion\nc : Cmd\nh : Q ⊢ Q'\nσ : Store\nhh : Heap\ns' : State\nhex : Exec c { store := σ, heap := hh } s'\nhq : Q s'.store s'.heap\n⊢ wp c Q' σ hh",
           h:"Everything the goal asks for is present except a proof of <code>Q'</code>, and <code>h</code> converts <code>hq</code> into one at the same state."}
        ],
        done:'No goals.'},
       {t:'p', h:"Here is the fold from the last section, made legitimate. Two applications of <code>wp_seq</code>, the second of them under <code>wp c₁</code>, which is exactly the step <code>wp_mono</code> pays for — once in each direction, because the statement is a <code>⊣⊢</code>."},
       {t:'code', tag:'illustration', cap:'The three-command fold, as a term.',
        src:"example (c₁ c₂ c₃ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; (c₂ ;; c₃)) Q ⊣⊢ wp c₁ (wp c₂ (wp c₃ Q)) :=\n  equiv_trans (wp_seq c₁ (c₂ ;; c₃) Q)\n    ⟨wp_mono c₁ (wp_seq c₂ c₃ Q).1, wp_mono c₁ (wp_seq c₂ c₃ Q).2⟩"}
     ],
     pitfall:"Applying <code>h</code> to <code>σ</code> and <code>hh</code> instead of to the components of <code>s'</code>. Lean complains about the <i>third</i> argument, not the first two: <code>The argument hq has type Q s'.store s'.heap but is expected to have type Q σ hh</code>. That reads like a complaint about nothing until you notice which state each side names — the entailment was applied at the initial state, and the only proof of <code>Q</code> you have is at the final one.",
     variants:"Reverse the hypothesis and the conclusion reverses with it, which is what monotone means; there is no contravariance anywhere in <code>wp</code>&rsquo;s postcondition argument. The direction that has no analogue is the command: there is no ordering on <code>Cmd</code> in this course, so &ldquo;monotone in <code>c</code>&rdquo; is not a statement one can even write here."},

    {t:'p', h:"With three equations and a congruence law, the structural rules of Unit 22 are no longer primitive. Each of them is a rearrangement of these."},

    {t:'code', tag:'illustration', cap:'The four rules of Unit 22, re-derived. Every one of these typechecks only because <code>Hoare P c Q</code> and <code>P ⊢ wp c Q</code> are the same proposition; the <code>Iff</code> is never applied.',
     src:"example (P : Assertion) : Hoare P .skip P := (wp_skip P).2\n\nexample (x : Var) (e : Atom) (Q : Assertion) : Hoare (subst x e Q) (.assign x e) Q :=\n  (wp_assign x e Q).2\n\nexample {P Q R : Assertion} {c₁ c₂ : Cmd} (h₁ : Hoare P c₁ Q) (h₂ : Hoare Q c₂ R) :\n    Hoare P (c₁ ;; c₂) R :=\n  entails_trans h₁ (entails_trans (wp_mono c₁ h₂) (wp_seq c₁ c₂ R).2)\n\nexample {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare P c Q) (hpost : Q ⊢ Q') : Hoare P' c Q' :=\n  entails_trans hpre (entails_trans hc (wp_mono c hpost))"},

    {t:'p', h:"Read the third one. <code>h₁</code> has type <code>Hoare P c₁ Q</code> and is being handed to <code>entails_trans</code>, which wants an entailment; it is accepted because it already is one. <code>wp_mono c₁ h₂</code> lifts the second triple under <code>wp c₁</code>, and <code>(wp_seq c₁ c₂ R).2</code> collapses the nested transformers back into one. Three steps, and the rule that took a middle assertion and two <code>obtain</code>s in Unit 22 is now a chain in the preorder."},

    {t:'p', h:"Consequence is even barer: pre-composition with <code>hpre</code>, post-composition with <code>wp_mono c hpost</code>. The variance Unit 22 pointed out — strengthen the precondition, weaken the postcondition — is here the plain fact that a transformer is monotone and composition of entailments runs one way."},

    {t:'note', kind:'info', title:'What determinism would have bought',
     h:"Nothing on this page. <code>wp_seq</code> in particular never assumes a command has one outcome: the forward direction inverts whichever derivation it is given, and the backward direction builds one, and neither cares whether others exist. If <code>Cmd</code> gained a nondeterministic construct, every equation here would still hold with <code>wp</code> read angelically. The demonic reading would need its own proofs, and its <code>seq</code> equation would hold too — the two readings differ on faults and on divergence, not on composition."},

    {t:'p', h:"Unit 29&rsquo;s method has a direction too. It runs along the program from the precondition, and it chooses each intermediate assertion by looking <i>one</i> command ahead: the cells the next rule owns, with everything else cut off beside them. The fold runs the other way and looks at the whole tail at once — <code>wp c₂ (wp c₃ (wp c₄ post))</code> is a single statement of what the last three commands need. Both routes prove the same triples. They differ in what you have to supply."},

    {t:'cmp',
     left:{t:'Forwards — Unit 29', h:"Begin at the precondition. At each command: choose the assertion that comes after it, cut off the frame, apply the small rule, reshape the <code>∗</code> so the next rule fits. The choice is yours at every step, and Unit 29 called it the one creative act. One command of lookahead is all you get, so a fact established early and needed late does not travel on its own — it is carried as a frame, and every command it passes costs a <code>Preserves</code> obligation. The previous unit&rsquo;s <code>preserves_load_fact</code> is one of those: the fact that <code>tmp₁</code> holds <code>a</code>, carried across the load that comes after it."},
     right:{t:'Backwards — the fold', h:"Begin at the postcondition. Apply <code>wp cₙ</code>, then <code>wp cₙ₋₁</code>, down to <code>c₁</code>. Nothing is chosen at any step: <code>wp_seq</code> fixes each assertion from the one after it. Nothing is carried either, because the assertion at each point already says everything the rest of the program needs, cells and store facts alike. What is left at the end is one entailment: the precondition you were asked for into the one that was computed."}},

    {t:'p', h:"That difference is why a verification tool computes weakest preconditions instead of searching forwards. A fold with no choice points is a program; a search over frames and intermediate assertions is not, and the thing being searched for — the assertion between two commands — is the thing the fold produces. The price is one equation per command form, and the three above buy every program built from <code>skip</code>, assignment and <code>;;</code>."},

    /* ================================================= weakest, precisely ==== */

    {t:'sec', s:'Weakest, precisely'},

    {t:'p', h:"The word <i>weakest</i> has been carrying an unproved claim since the definition card. It says two things, and they pull in opposite directions: <code>wp c Q</code> must be <i>small enough to be correct</i> — running <code>c</code> from anywhere in it really does deliver <code>Q</code>, so nothing unsafe may be inside — and <i>large enough to be optimal</i> — no correct precondition sticks out of it. Neither is obvious from the definition, and both are one line."},

    /* ----------------------------------------------------------- x63 --- */

    {t:'ex',
     id:'x63',
     name:'wp_sound and wp_weakest',
     why:"This is a design exercise: the work is writing the statements, not proving them. Until you can state optimality you cannot check anyone&rsquo;s claim to have found a weakest precondition, including your own — and the next two exercises compute two of them, so the check is about to be needed. It is also the cleanest illustration on the page of what <code>hoare_iff_entails_wp</code> bought: both proofs turn out to be terms you have already written, under other names.",
     setup:"On paper first, then in Lean. Two theorems. The first says <code>wp c Q</code> is a correct precondition for <code>c</code> against <code>Q</code>. The second says every correct precondition entails it. Between them they say <code>wp c Q</code> is a greatest element of the set of correct preconditions, in the <code>⊢</code> order. No new vocabulary is required — <code>Hoare</code>, <code>⊢</code> and <code>wp</code> are the whole alphabet.",
     goal:"-- Delete the line below and write your own `theorem wp_sound …` and\n-- `theorem wp_weakest …`. Any correct statement of each fact is accepted.\nexample : True := by",
     hints:[
       "Say each fact in English with no symbols. First: <i>starting anywhere in <code>wp c Q</code>, running <code>c</code> gets you into <code>Q</code>.</i> Second: <i>if starting anywhere in <code>P</code> and running <code>c</code> gets you into <code>Q</code>, then <code>P</code> is inside <code>wp c Q</code>.</i> Now ask which of the course&rsquo;s three relations — <code>Hoare</code>, <code>⊢</code>, <code>⊣⊢</code> — each sentence is.",
       "The first sentence is a triple with <code>wp c Q</code> in the precondition slot. The second is an implication whose hypothesis is a triple and whose conclusion is an entailment; the triple&rsquo;s precondition is arbitrary, so it must be a bound variable of the statement, and so must <code>Q</code> and <code>c</code>.",
       "The two statements are <code>Hoare (wp c Q) c Q</code>, universally quantified over <code>c</code> and <code>Q</code>; and <code>Hoare P c Q → P ⊢ wp c Q</code>, universally quantified over <code>P</code>, <code>Q</code> and <code>c</code>. Take <code>P</code>, <code>Q</code> and <code>c</code> implicit in the second, since they are all determined by the hypothesis.",
       "For the proofs: unfold nothing. <code>Hoare (wp c Q) c Q</code> is by definition <code>wp c Q ⊢ wp c Q</code>, and you proved that in Unit 12. <code>Hoare P c Q</code> is by definition <code>P ⊢ wp c Q</code>, so the hypothesis is already the conclusion."
     ],
     sol:"theorem wp_sound (c : Cmd) (Q : Assertion) : Hoare (wp c Q) c Q := fun _ _ hp => hp\n\ntheorem wp_weakest {P Q : Assertion} {c : Cmd} (h : Hoare P c Q) : P ⊢ wp c Q := h",
     solNote:"If you wrote <code>entails_refl (wp c Q)</code> for the first, that compiles too, and it is the more honest spelling: soundness of <code>wp</code> <i>is</i> reflexivity of entailment, seen through the identification. If you stated the second as <code>Hoare P c Q ↔ P ⊢ wp c Q</code> you restated <code>hoare_iff_entails_wp</code>, which is correct and strictly stronger; the one-directional form is kept here because it is the form that gets applied.",
     expl:"Both theorems are the identity function wearing different types. <code>wp_sound</code> takes a proof that the initial state is in <code>wp c Q</code> and must produce a run into <code>Q</code> — but being in <code>wp c Q</code> <i>is</i> having such a run, so it hands the proof straight back. <code>wp_weakest</code> takes a triple and must produce an entailment, and the triple already is one. Neither proof does any work, and that is the content: <i>weakest</i> is not an extra property of this definition, it is what the definition says.",
     walk:[
       {tac:'fun _ _ hp => hp', h:"Three arguments, because <code>Hoare</code> unfolds to a <code>∀ σ h, P σ h → …</code>. The store and heap are not consulted. The premise <code>hp : wp c Q σ h</code> unfolds to precisely the existential the goal asks for, so returning it is a complete proof."},
       {tac:'h', h:"No abstraction at all. The declared type of <code>wp_weakest</code>&rsquo;s conclusion and the declared type of its hypothesis are the same term after unfolding <code>Hoare</code> and <code>Entails</code>, so the hypothesis is accepted as the proof."}
     ],
     deep:[
       {t:'trace', title:'What the two goals look like once you <code>intro</code>',
        start:"c : Cmd\nQ : Assertion\n⊢ Hoare (wp c Q) c Q",
        steps:[
          {tac:'intro σ h hp',
           state:"c : Cmd\nQ : Assertion\nσ : Store\nh : Heap\nhp : wp c Q σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
           h:"The goal is the unfolding of <code>hp</code>&rsquo;s type. Lean displays the hypothesis folded and the goal unfolded, which makes the identity easy to miss and is worth pausing on: <code>exact hp</code> closes it."},
          {tac:'intro σ hh hp  -- now in the second theorem',
           state:"P Q : Assertion\nc : Cmd\nh : Hoare P c Q\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ wp c Q σ hh",
           h:"Now the folding is the other way round: the goal is folded and the hypothesis is not. <code>h σ hh hp</code> has exactly the goal&rsquo;s type, because <code>h</code>, read as an entailment, is a function of three arguments — which is why the whole proof is <code>h</code>."}
        ],
        done:'No goals.'}
     ],
     pitfall:"Stating optimality backwards, as <code>wp c Q ⊢ P</code>. That says every valid precondition is <i>above</i> the weakest one, which is false as soon as any precondition is strictly stronger than necessary — and almost all of them are. The check: <code>wp c Q</code> is the biggest set, and <code>P ⊢ wp c Q</code> is the containment that says <code>P</code> is inside it.",
     variants:"Two other correct statements, each buying something different. <code>Hoare P c Q ↔ P ⊢ wp c Q</code> is <code>hoare_iff_entails_wp</code> and contains both halves; it is what you would state if you wanted one theorem instead of two, at the cost of hiding that the two halves have different characters. Uniqueness can be stated instead of optimality: <i>if <code>Hoare P c Q</code> and every <code>P'</code> with <code>Hoare P' c Q</code> satisfies <code>P' ⊢ P</code>, then <code>P ⊣⊢ wp c Q</code></i>. That is the statement that justifies the definite article in &ldquo;the weakest precondition&rdquo;, and it follows from the two above by <code>⟨…, …⟩</code>. What you cannot state is equality of assertions: Unit 12 showed <code>⊢</code> is not antisymmetric, so uniqueness is only ever up to <code>⊣⊢</code>."},

    {t:'p', h:"So a precondition you have written is the weakest one exactly when the entailment runs both ways. One direction is your specification; the other is the claim that you gave nothing away. The commonest way to give something away is to pin down a value the command never reads — which is what the next two computations are about."},

    /* ============================================== computing wp for real ==== */

    {t:'sec', s:'Computing <code>wp</code> against a real postcondition'},

    {t:'p', h:"<code>skip</code>, <code>assign</code> and <code>;;</code> leave the postcondition abstract. The memory commands cannot: <code>free</code> and <code>write</code> change the heap, so computing their weakest precondition means committing to a particular <code>Q</code> and doing heap arithmetic. Start with the smallest interesting question. Freeing <code>l</code> leaves the heap empty. Which heaps could it have started from?"},

    {t:'p', h:"The answer has to be: exactly the one-cell heaps at <code>l</code>. <code>free</code> removes <code>l</code> and leaves everything else, so if the result is empty there was nothing else. Proving that in Lean is a claim about functions — a heap is a function, and two functions are equal when they agree everywhere — and it does not mention <code>wp</code>, <code>Exec</code> or assertions. It deserves to be a lemma of its own rather than four lines buried in a bigger proof."},

    {t:'code', cap:'Given a lookup at <code>l</code> and the fact that erasing <code>l</code> empties the heap, the heap was the singleton. Both hypotheses are needed: the first gives the value, the second gives the rest.',
     src:"theorem heap_eq_singleton {h : Heap} {l : Loc} {v : Val}\n    (hl : h l = some v) (hrest : Heap.erase h l = Heap.empty) :\n    h = Heap.singleton l v := by\n  funext x\n  by_cases hx : x = l\n  · subst hx; rw [hl, singleton_same]\n  · rw [singleton_other l x v hx]\n    have := congrFun hrest x\n    rw [erase_other h l x hx] at this\n    exact this"},

    {t:'trace', title:'heap_eq_singleton, the address split',
     start:"h : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\n⊢ h = Heap.singleton l v",
     steps:[
       {tac:'funext x',
        state:"x : Loc\n⊢ h x = Heap.singleton l v x",
        h:"An equation between heaps becomes an equation at an arbitrary address, and gives you <code>x</code> to case on. The five hypothesis lines are unchanged here and in the states below and are left off."},
       {tac:'by_cases hx : x = l',
        state:"case pos\nx : Loc\nhx : x = l\n⊢ h x = Heap.singleton l v x",
        h:"The address is either the one that was freed or not, and the two cases are answered by different hypotheses — <code>hl</code> at <code>l</code>, <code>hrest</code> everywhere else."},
       {tac:'rw [singleton_other l x v hx]',
        state:"case neg\nx : Loc\nhx : ¬x = l\n⊢ h x = none",
        h:"Away from <code>l</code> the singleton is unallocated, so the goal reduces to: the original heap was unallocated at <code>x</code> too. That is what <code>hrest</code> is about to say."},
       {tac:'have := congrFun hrest x',
        state:"case neg\nx : Loc\nhx : ¬x = l\nthis : h.erase l x = Heap.empty x\n⊢ h x = none",
        h:"<code>congrFun</code> is the converse of <code>funext</code>: it takes the equation between the two heaps down to this one address."},
       {tac:'rw [erase_other h l x hx] at this',
        state:"case neg\nx : Loc\nhx : ¬x = l\nthis : h x = Heap.empty x\n⊢ h x = none",
        h:"Erasing at <code>l</code> does not touch <code>x</code>, so the left side collapses to <code>h x</code>. The right side is definitionally <code>none</code>, so <code>exact this</code> closes the goal without a further rewrite."}
     ],
     done:'No goals.'},

    {t:'p', h:"With that in hand the computation of <code>wp (.free l) emp</code> is short, and its answer is the interesting part."},

    /* --------------------------------------------------------- m12-4 --- */

    {t:'ex',
     id:'m12-4',
     name:'wp_free_emp',
     hard:true,
     why:"The first weakest precondition in the course that could not have been guessed from the shape of a rule. Unit 23 gave <code>free</code> the small-footprint specification <code>Hoare (l ↦ v) (.free l) emp</code>, with <code>v</code> a parameter the caller supplies. Computing the weakest precondition tells you what happens to that parameter when nobody supplies it: it becomes an existential. That is the formal content of the sentence &ldquo;the value does not matter&rdquo;, and it is the pattern every rule with an unread value follows.",
     setup:"<code>heap_eq_singleton</code> is proved above and is in scope. <code>aExists</code> is Unit 12&rsquo;s existential over assertions, so <code>aExists (fun v => l ↦ v)</code> holds of a heap exactly when that heap is <code>Heap.singleton l v</code> for some <code>v</code>. The <code>free</code> rule of <code>Exec</code> has one premise, that the address is allocated, and its conclusion erases it.",
     goal:"theorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by",
     hints:[
       "Left to right: from a run of <code>free l</code> that ends with an empty heap, produce a value <code>v</code> and show the starting heap was <code>Heap.singleton l v</code>. Right to left: from a starting heap that is a singleton at <code>l</code>, produce a run of <code>free l</code> whose final heap is empty.",
       "Going forwards, inversion gives you both halves of <code>heap_eq_singleton</code>&rsquo;s hypotheses: the rule&rsquo;s premise is the lookup, and the postcondition <code>emp</code> at the final state says the erased heap is empty. The value in the existential is the one the premise mentions. Going backwards you must exhibit the final state; the heap component is <code>Heap.erase (Heap.singleton l v) l</code>, and Unit 06 has the theorem saying that is empty.",
       "<code>cases hex with | free hl => …</code> for the inversion. Forwards the tool is <code>refine</code>: apply <code>heap_eq_singleton</code> to <code>hl</code> and leave its second hypothesis as a hole. Backwards, the two lemmas are <code>singleton_same</code> for the rule&rsquo;s premise and <code>erase_singleton</code> for the postcondition; the hypothesis <code>hp</code> is a heap equation, so <code>subst hp</code> puts the singleton into the goal.",
       "After <code>cases hex with | free hl =></code>, write <code>refine ⟨_, heap_eq_singleton hl ?_⟩</code>. The witness is left as <code>_</code> because the value is inaccessible — the rule bound it and you cannot type its name — and unifying with <code>hl</code> determines it. The remaining goal is <code>⊢ h.erase l = Heap.empty</code>, which the postcondition proof already is."
     ],
     sol:"theorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by\n  constructor\n  · intro σ h ⟨s', hex, he⟩\n    cases hex with\n    | free hl =>\n        refine ⟨_, heap_eq_singleton hl ?_⟩\n        exact he\n  · intro σ h ⟨v, hp⟩\n    subst hp\n    exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v),\n           erase_singleton l v⟩",
     solNote:"Read the statement once more as a sentence about programs: <i>the states from which freeing <code>l</code> leaves you owning nothing are exactly the states in which you own <code>l</code> and nothing else</i>. The specification and its converse in one line — which is what a weakest precondition always is.",
     expl:"Forwards, the two facts <code>heap_eq_singleton</code> needs arrive from two different places: the lookup is the <code>free</code> rule&rsquo;s own premise, and the emptiness is the postcondition evaluated at the final state. Backwards, the run is constructed rather than found: the final heap is written out as an erase applied to a singleton, the premise is discharged by looking the address up in the singleton, and the postcondition by the Unit 06 equation that says erasing a singleton at its own address gives the empty heap.",
     walk:[
       {tac:'constructor', h:"The two directions. Forwards you are given a run and must produce a value; backwards you are given a value and must produce a run — and only the backward half ever mentions <code>Exec.free</code> by name."},
       {tac:'intro σ h ⟨s\', hex, he⟩', h:"Opens the entailment and the existential inside <code>wp</code>. <code>he</code> is the proof of <code>emp</code> at the final state, which after inversion becomes the claim that <code>h</code> with <code>l</code> erased is empty."},
       {tac:'cases hex with | free hl =>', h:"One rule concludes a run of <code>free</code>. Naming its premise <code>hl</code> is the whole reason for the named form: <code>hl</code> is the lookup <code>heap_eq_singleton</code> wants, and without a name it is inaccessible."},
       {tac:'refine ⟨_, heap_eq_singleton hl ?_⟩', h:"Supplies the shape of the answer and leaves one hole. The first slot is the value in the existential, written <code>_</code> because the name the rule gave it carries a dagger; unification with <code>hl</code>&rsquo;s type fills it in. The hole is <code>heap_eq_singleton</code>&rsquo;s second hypothesis."},
       {tac:'exact he', h:"The hole is <code>h.erase l = Heap.empty</code> and <code>he</code> is <code>emp</code> at a state whose heap is that erase — the same proposition wrapped in two unreduced projections, which <code>exact</code> sees through."},
       {tac:'intro σ h ⟨v, hp⟩', h:"The other direction. <code>hp</code> is <code>(fun v => l ↦ v) v σ h</code>, which unfolds to the heap equation <code>h = Heap.singleton l v</code>."},
       {tac:'subst hp', h:"Replaces <code>h</code> by the singleton everywhere, so the goal becomes <code>wp (Cmd.free l) emp σ (Heap.singleton l v)</code> and every subsequent lemma can be about singletons rather than about an abstract heap."},
       {tac:'exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v), erase_singleton l v⟩', h:"The whole existential in one term: the final state written exactly as the <code>free</code> rule will produce it, the rule applied to the lookup, and the Unit 06 equation as the proof of <code>emp</code>."}
     ],
     deep:[
       {t:'trace', title:'wp_free_emp, forwards',
        start:"l : Loc\n⊢ wp (Cmd.free l) emp ⊣⊢ aExists fun v => l ↦ v",
        steps:[
          {tac:'intro σ h ⟨s\', hex, he⟩',
           state:"case left\nl : Loc\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.free l) { store := σ, heap := h } s'\nhe : emp s'.store s'.heap\n⊢ aExists (fun v => l ↦ v) σ h",
           h:"Before inversion, <code>he</code> says nothing usable: it is <code>emp</code> at an unknown state."},
          {tac:'cases hex with | free hl =>',
           state:"case left.free\nl : Loc\nσ : Store\nh : Heap\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhe :\n  emp { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap\n⊢ aExists (fun v => l ↦ v) σ h",
           h:"The rule&rsquo;s value arrives daggered as <code>v✝</code> — that is the witness the goal wants, and the reason it is written <code>_</code> rather than named. <code>he</code> is now a statement about the erased heap."},
          {tac:'refine ⟨_, heap_eq_singleton hl ?_⟩',
           state:"case left.free\n⊢ h.erase l = Heap.empty",
           h:"One goal left, shown here as its conclusion only; the context is unchanged from the previous state. This is exactly what <code>he</code> says, with the projections reduced."}
        ],
        done:'No goals.'},
       {t:'p', h:"Weakening the postcondition all the way to <code>aTrue</code> shows what the rest of the work was for. What survives is the run existing at all, which is the safety condition of the command and nothing more."},
       {t:'code', tag:'illustration', cap:'<code>wp c aTrue</code> is the safety condition of <code>c</code>. For <code>free</code> that is: the address is allocated. No heap equation appears, and <code>heap_eq_singleton</code> is not needed.',
        src:"example (l : Loc) : wp (.free l) aTrue ⊣⊢ (fun _ h => ∃ v, h l = some v) := by\n  constructor\n  · intro σ h ⟨s', hex, _⟩\n    cases hex with\n    | free hl => exact ⟨_, hl⟩\n  · intro σ h ⟨v, hl⟩\n    exact ⟨⟨σ, Heap.erase h l⟩, Exec.free hl, True.intro⟩"},
       {t:'p', h:"The backward direction of the exercise itself is worth a line, because there is a shorter-looking final state that does not work."},
       {t:'state', cap:'What happens if you name the final heap <code>Heap.empty</code> instead of <code>Heap.erase (Heap.singleton l v) l</code>. The rule&rsquo;s conclusion fixes the final state to be an erase; it does not accept a heap that happens to be equal to one. Lean reports two errors here, one per component of the pair; this is the second, and it is the one that says why.',
        src:"error: Application type mismatch: The argument\n  Exec.free ?m.39\nhas type\n  Exec (Cmd.free ?m.37) ?m.36 { store := State.store ?m.36, heap := (State.heap ?m.36).erase ?m.37 }\nbut is expected to have type\n  Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } { store := σ, heap := Heap.empty }\nin the application\n  And.intro (Exec.free ?m.39)"}
     ],
     pitfall:"Trying to name the daggered value. Writing <code>refine ⟨v, …⟩</code> after the inversion gets <code>Unknown identifier `v`</code>, and adding <code>rename_i v</code> works but is unnecessary here — the underscore is determined, because <code>heap_eq_singleton hl</code> already mentions the value in its type. Reach for <code>rename_i</code> when you need to <i>write</i> the name, not when Lean can work it out.",
     variants:"The <code>aTrue</code> version is compiled above, and it is the general pattern: <code>wp c aTrue</code> is the safety condition of <code>c</code>, and everything beyond it in the postcondition is what costs work. In the other direction, drop the second hypothesis of <code>heap_eq_singleton</code> and the theorem becomes false rather than unprovable: <code>Heap.write (Heap.singleton 0 1) 1 2</code> holds <code>1</code> at address <code>0</code> and is not a singleton, and reading both sides at address <code>1</code> refutes it in four lines. Drop the <i>first</i> hypothesis instead and the statement no longer mentions <code>v</code> at all, so there is nothing left to state."},

    {t:'p', h:"The same question for <code>write</code> has the same answer, for a slightly different reason. To land in <code>l ↦ new</code> after writing <code>new</code> at <code>l</code>, you must have owned <code>l</code> and nothing else — but the value you owned is never consulted, because the write overwrites it."},

    /* --------------------------------------------------------- m12-5 --- */

    {t:'ex',
     id:'m12-5',
     name:'wp_write',
     hard:true,
     why:"The same existential as the previous exercise, arrived at by a different route, and the one the phrase <i>the value does not matter</i> was always about. Unit 23&rsquo;s write rule takes <code>old</code> as a parameter; here <code>old</code> is quantified away, and the proof shows exactly where: it is the value the <code>write</code> rule&rsquo;s premise mentions and the conclusion discards. It is also the last pointwise heap argument you are asked for.",
     setup:"The postcondition is fixed to <code>l ↦ new</code> and the value written is a constant, so no store is involved. <code>Exec.write</code>&rsquo;s premise is a lookup, and the value it mentions is bound by the rule and discarded by its conclusion — so after inversion it is inaccessible until you rename it.",
     goal:"theorem wp_write (l : Loc) (new : Val) :\n    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old) := by",
     hints:[
       "Left to right: from a run of <code>[l] := new</code> whose final heap is <code>Heap.singleton l new</code>, produce a value <code>old</code> and show the starting heap was <code>Heap.singleton l old</code>. Right to left: from a starting heap that is a singleton, build the run.",
       "You cannot use <code>heap_eq_singleton</code> here: it wants the erased heap to be empty, and nothing has been erased. The argument is the same in spirit though — split the address space at <code>l</code>. At <code>l</code> the starting heap holds the old value, by the rule&rsquo;s premise. Away from <code>l</code>, the write changed nothing, so the starting heap agrees with the final one, which is unallocated there.",
       "<code>rename_i old</code> after the inversion, because you need to write the name in the existential. Then <code>funext x</code> and <code>by_cases hx : x = l</code>. The lemmas for the second branch are <code>write_other</code> and <code>singleton_other</code>, applied inside <code>congrFun</code> of the postcondition equation. One thing will get in the way before any of that: inversion states <code>hl</code> and the postcondition about projections of a structure literal, and <code>rw</code> matches on syntax, so it will not find them in a goal that mentions <code>h</code> plainly. The cure is a <code>have</code> that restates each of the two at the reduced type — the proof carries over unchanged.",
       "After <code>cases hex with | write hl =></code> and <code>rename_i old</code> and <code>refine ⟨old, ?_⟩</code>, write two restatements before touching the goal: <code>have hl' : h l = some old := hl</code> and <code>have hq' : Heap.write h l new = Heap.singleton l new := hq</code>. Without them <code>rw</code> refuses, because <code>hl</code> and <code>hq</code> are stated about unreduced projections of a structure literal."
     ],
     sol:"theorem wp_write (l : Loc) (new : Val) :\n    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | write hl =>\n        rename_i old\n        refine ⟨old, ?_⟩\n        have hl' : h l = some old := hl\n        have hq' : Heap.write h l new = Heap.singleton l new := hq\n        funext x\n        by_cases hx : x = l\n        · subst hx; rw [hl', singleton_same]\n        · rw [singleton_other l x old hx]\n          have := congrFun hq' x\n          rw [write_other h l x new hx, singleton_other l x new hx] at this\n          exact this\n  · intro σ h ⟨old, hp⟩\n    subst hp\n    exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩,\n           Exec.write (singleton_same l old), write_singleton l old new⟩",
     solNote:"Two <code>have</code>s that look redundant are the difference between this proof and a stuck one; the pitfall below is the error you get without them. Everything after them is the region-splitting argument you have been doing since Unit 06 — two regions here, the written cell and everything else, because there is nothing outside the cell to be a third.",
     expl:"The forward direction proves a heap equation pointwise. At <code>l</code>, the restated premise gives the value directly and <code>singleton_same</code> matches it. Away from <code>l</code>, the postcondition equation is taken down to the address by <code>congrFun</code>, and then both sides are simplified by lemmas that say the write and the singleton are both blind there — leaving <code>h x = none</code>, which is what the goal had become. The backward direction is one <code>Exec.write</code> and one Unit 06 equation.",
     walk:[
       {tac:'constructor', h:"The two directions again. This time neither is short: forwards is a pointwise heap argument, backwards is a single existential whose every component has to be written out."},
       {tac:'intro σ h ⟨s\', hex, hq⟩', h:"Opens the entailment and the existential in <code>wp</code>. <code>hq</code> is the postcondition <code>l ↦ new</code> at the final state, and it is the hypothesis that will carry all the information about what the write did — but not until it has been inverted and restated."},
       {tac:'cases hex with | write hl =>', h:"Inverts, naming the premise. The value the premise mentions is <i>not</i> named by this — it is bound by the rule and does not appear in its conclusion, so it arrives as <code>old✝</code>."},
       {tac:'rename_i old', h:"Gives that value a typeable name. Unlike the previous exercise, this one is unavoidable: <code>refine ⟨old, ?_⟩</code> has to write it, because nothing else in the goal determines the witness."},
       {tac:'refine ⟨old, ?_⟩', h:"Supplies the witness of <code>aExists</code> and leaves the heap equation <code>(fun old => l ↦ old) old σ h</code>, which is <code>h = Heap.singleton l old</code>."},
       {tac:'have hl\' : h l = some old := hl', h:"A definitional restatement. <code>hl</code>&rsquo;s type mentions <code>{ store := σ, heap := h }.heap l</code>; <code>hl'</code> is the same proof with the projection reduced, and it is the reduced form that <code>rw</code> can find in the goal."},
       {tac:'have hq\' : Heap.write h l new = Heap.singleton l new := hq', h:"The same move on the postcondition. <code>hq</code> is <code>l ↦ new</code> at a state built out of projections and an <code>Atom.eval</code> of a constant; <code>hq'</code> is that with everything reduced."},
       {tac:'funext x', h:"Turns the heap equation into an equation at an arbitrary address and hands you <code>x</code> to split on."},
       {tac:'by_cases hx : x = l', h:"The two regions: the written cell, and everywhere else."},
       {tac:'subst hx; rw [hl\', singleton_same]', h:"At the cell. Rewriting with <code>hl'</code> makes the left side <code>some old</code>; <code>singleton_same</code> makes the right side the same, and <code>rw</code>&rsquo;s trailing <code>rfl</code> closes it."},
       {tac:'rw [singleton_other l x old hx]', h:"Away from the cell the singleton is <code>none</code>, so the goal is <code>h x = none</code>."},
       {tac:'have := congrFun hq\' x', h:"Brings the postcondition equation down to this one address: <code>h.write l new x = Heap.singleton l new x</code>."},
       {tac:'rw [write_other h l x new hx, singleton_other l x new hx] at this', h:"Both sides are blind at <code>x</code>: the write did not touch it, and the singleton does not hold it. What is left is <code>h x = none</code>."},
       {tac:'exact this', h:"Which is the goal."},
       {tac:'subst hp', h:"Backward direction. The starting heap becomes <code>Heap.singleton l old</code>, so the run can be written down concretely."},
       {tac:'exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩, Exec.write (singleton_same l old), write_singleton l old new⟩', h:"Final state, rule, postcondition. <code>write_singleton</code> is Unit 06&rsquo;s equation saying that writing over a singleton at its own address gives another singleton."}
     ],
     deep:[
       {t:'trace', title:'wp_write, the second region',
        start:"l : Loc\nnew : Val\n⊢ wp (Cmd.write l (Atom.const new)) (l ↦ new) ⊣⊢ aExists fun old => l ↦ old",
        steps:[
          {tac:'rename_i old; refine ⟨old, ?_⟩',
           state:"case left.write\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : { store := σ, heap := h }.heap l = some old\n⊢ (fun old => l ↦ old) old σ h",
           h:"The seven-line <code>hq</code> is omitted here and in the two states below; it is the postcondition at the written state, and it is what <code>hq'</code> restates. The goal is a heap equation with the beta-redex still standing."},
          {tac:'rw [singleton_other l x old hx]',
           state:"case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\n⊢ h x = none",
           h:"The second region, after both restatements and the split. <code>hl</code> is dropped from the display too, since <code>hl'</code> is the copy that gets used. Everything about the write is now in <code>hq'</code>, in a form <code>rw</code> can find."},
          {tac:'rw [write_other h l x new hx, singleton_other l x new hx] at this',
           state:"case neg\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\nthis : h x = none\n⊢ h x = none",
           h:"Hypothesis and goal coincide. The five binder lines <code>l new σ h old</code>, and <code>hl</code> and <code>hq</code> with them, are unchanged from the state above and are left off."}
        ],
        done:'No goals.'},
       {t:'p', h:"And here is the check that the precondition is genuinely the weakest, done by refuting a plausible alternative. <code>l ↦ 0</code> is a perfectly good precondition for this write — it entails the one above — but it is not the weakest, and a heap holding <code>1</code> at <code>l</code> proves it."},
       {t:'code', tag:'illustration', cap:'Sufficient is not weakest. The witness is a state in <code>wp</code> that the candidate precondition excludes.',
        src:"example (l : Loc) (new : Val) : ¬ (wp (.write l (.const new)) (l ↦ new) ⊢ (l ↦ 0)) := by\n  intro hbad\n  have hin : wp (.write l (.const new)) (l ↦ new) (fun _ => 0) (Heap.singleton l 1) :=\n    (wp_write l new).2 (fun _ => 0) (Heap.singleton l 1) ⟨1, rfl⟩\n  have hout := hbad (fun _ => 0) (Heap.singleton l 1) hin\n  have h1 := congrFun hout l\n  rw [singleton_same, singleton_same] at h1\n  exact absurd h1 (by simp)"}
     ],
     pitfall:"Skipping the two <code>have</code>s and rewriting with <code>hl</code> directly. Lean answers <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern { store := σ, heap := h }.heap x in the target expression h x = Heap.singleton x old x</code>. The proof <code>hl</code> is fine; its <i>type</i> is written with a projection the goal does not contain, and <code>rw</code> matches on syntax. A term-level application would have accepted <code>hl</code> unchanged — that asymmetry between <code>rw</code> and application is Unit 25&rsquo;s, and it bites again here.",
     variants:"Ask the same question of <code>copyCell</code> from Unit 29, whose specification is <code>Hoare ((src ↦ a) ∗ (dst ↦ b)) (copyCell tmp src dst) ((src ↦ a) ∗ (dst ↦ a))</code>. Is <code>(src ↦ a) ∗ (dst ↦ b)</code> the weakest precondition? No: <code>b</code> is never read — the program loads from <code>src</code> and writes over <code>dst</code> — so any state owning <code>dst</code> with any contents is in the weakest precondition, and pinning <code>b</code> excludes all but one of them. The refutation is the previous exercise&rsquo;s shape with two cells: take the same specification at <code>b + 1</code>, which puts a state satisfying <code>(src ↦ a) ∗ (dst ↦ (b+1))</code> inside <code>wp</code> — there is such a state as soon as <code>src ≠ dst</code> — and then read both heaps at <code>dst</code> and compare. Fixing it costs one existential: <code>(src ↦ a) ∗ aExists (fun w => dst ↦ w)</code>."},

    {t:'p', h:"Both computations landed in the same place: the small-footprint precondition of Unit 23, with the parameter the command never reads replaced by an existential. Two commands do not make a theorem, and stating one would mean quantifying over rules, which this course has no way to write. The reason is the same in both proofs, and it is visible at the inversion step: a rule&rsquo;s parameter is the value its premise reads out of the heap, and its conclusion then either uses that value or discards it. <code>free</code> erases the cell and <code>write</code> overwrites it, so both discard it, and nothing in either run depends on which value it was. That is the sharpest available answer to a question Unit 07 asked and Unit 13 decided. <i>How much do you own?</i> — exactly the footprint. <i>How much do you know about it?</i> — exactly what the command reads, and no more."},

    /* ==================================================== the punchline ==== */

    {t:'sec', s:'The frame rule, transported'},

    {t:'p', h:"One thing is still missing. The frame rule is stated about triples, and everything above is stated about <code>wp</code>. If the two languages were genuinely different, each theorem in one would need a translation into the other, and the translations would accumulate. They do not, and the frame rule is the case where that is worth demonstrating rather than asserting, because it is the theorem that cost the most to get: three units of locality machinery before Unit 27 could state it."},

    {t:'p', h:"Ask what the frame rule says about <code>wp</code>. If you can reach <code>Q</code> from here using only this part of the heap, then with an extra disjoint part <code>R</code> in hand you can reach <code>Q ∗ R</code>. Written as an entailment that is <code>wp c Q ∗ R ⊢ wp c (Q ∗ R)</code>, with the same two hypotheses Unit 27 needed: the command is heap-local, and it preserves <code>R</code>."},

    {t:'code', cap:'The frame rule for weakest preconditions. One term, no tactics.',
     src:"theorem wp_frame {Q R : Assertion} {c : Cmd}\n    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) :=\n  hoare_frame (fun _ _ hp => hp) hlocal hpres"},

    /* ----------------------------------------------------------- x64 --- */

    {t:'ex',
     id:'x64',
     name:'wp_frame',
     why:"The punchline of the unit, and the only exercise in it whose difficulty is entirely in the explanation. Writing the term takes a minute; saying why Lean accepts it is the whole of what this page has been building, and if you can say it you have understood <code>hoare_iff_entails_wp</code>. It also means the frame rule needs no separate proof in the <code>wp</code> world — there is no <code>wp</code> world.",
     setup:"<code>hoare_frame</code> has type <code>Hoare P c Q → HeapLocal c → Preserves c R → Hoare (P ∗ R) c (Q ∗ R)</code>, with <code>P</code>, <code>Q</code>, <code>R</code> and <code>c</code> implicit. You supply the two side conditions from the hypotheses. The question is what to put in the first slot, and what <code>P</code> becomes when you do.",
     goal:"theorem wp_frame {Q R : Assertion} {c : Cmd}\n    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) :=",
     hints:[
       "The goal <code>wp c Q ∗ R ⊢ wp c (Q ∗ R)</code> is, by definition, the triple <code>Hoare (wp c Q ∗ R) c (Q ∗ R)</code>. Compare that with the conclusion of <code>hoare_frame</code> and read off what <code>P</code> and <code>Q</code> must be.",
       "With <code>P := wp c Q</code>, <code>hoare_frame</code>&rsquo;s first argument has to be a proof of <code>Hoare (wp c Q) c Q</code> — that <code>wp c Q</code> is a correct precondition. That is a theorem you have already stated and proved on this page.",
       "The theorem is <code>wp_sound</code>, and its proof was the identity. You may cite it by name or inline its proof term; both compile.",
       "Write <code>hoare_frame (wp_sound c Q) hlocal hpres</code> — no <code>by</code>, no tactics, and <code>wp_sound</code>&rsquo;s two arguments supplied, because it takes them explicitly. That is a complete proof and it compiles. The solution below writes the same thing with <code>wp_sound</code>&rsquo;s own proof inlined, which is worth comparing once you have yours."
     ],
     sol:"theorem wp_frame {Q R : Assertion} {c : Cmd}\n    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) :=\n  hoare_frame (fun _ _ hp => hp) hlocal hpres",
     solNote:"<code>hoare_frame wp_sound hlocal hpres</code> does not compile: <code>wp_sound</code> takes <code>c</code> and <code>Q</code> explicitly, so Lean reports <code>The argument wp_sound has type ∀ (c : Cmd) (Q : Assertion), Hoare (wp c Q) c Q but is expected to have type Hoare (wp c Q) c Q</code>. Supply them — <code>hoare_frame (wp_sound c Q) hlocal hpres</code> — and it does. Edition 1 has no theorem of this shape at all, which is a small piece of evidence that the identification was never made explicit there.",
     expl:"Everything happens in the types. <code>hoare_frame</code>&rsquo;s conclusion is <code>Hoare (P ∗ R) c (Q ∗ R)</code>; the goal is an entailment which unfolds to <code>Hoare (wp c Q ∗ R) c (Q ∗ R)</code>; matching them forces <code>P := wp c Q</code>. That instantiation turns <code>hoare_frame</code>&rsquo;s first hypothesis into <code>Hoare (wp c Q) c Q</code>, which is soundness of <code>wp</code>, whose proof is the identity. So the entire content of the frame rule for predicate transformers is the instantiation, and the instantiation is free because the two statements were never two.",
     walk:[
       {tac:'hoare_frame …', h:"Applied at <code>P := wp c Q</code>, forced by unifying its conclusion with the goal. The goal is written as an entailment and the conclusion as a triple, and unification sees through both because they fold to the same term."},
       {tac:'(fun _ _ hp => hp)', h:"The first argument: a proof of <code>Hoare (wp c Q) c Q</code>. It ignores the store and the heap and returns the premise, because being in <code>wp c Q</code> already is the existential the triple asks for. This is <code>wp_sound</code>, inlined."},
       {tac:'hlocal hpres', h:"The two side conditions, unchanged from Unit 27. Nothing about them mentions <code>wp</code>: locality is a property of the command and preservation is a property of the command and the frame, and neither knows what the postcondition is."}
     ],
     deep:[
       {t:'trace', title:'The same proof in tactic mode, with the identification made visible',
        start:"Q R : Assertion\nc : Cmd\nhlocal : HeapLocal c\nhpres : Preserves c R\n⊢ wp c Q ∗ R ⊢ wp c (Q ∗ R)",
        steps:[
          {tac:'show Hoare (wp c Q ∗ R) c (Q ∗ R)',
           state:"Q R : Assertion\nc : Cmd\nhlocal : HeapLocal c\nhpres : Preserves c R\n⊢ Hoare (wp c Q ∗ R) c (Q ∗ R)",
           h:"<code>show</code> changes the display and nothing else — it is accepted precisely because the two goals are the same term. Now the goal is literally an instance of <code>hoare_frame</code>&rsquo;s conclusion."},
          {tac:'exact hoare_frame (wp_sound c Q) hlocal hpres',
           state:"No goals.",
           h:"With the goal in triple form the citation of <code>wp_sound</code> is visible rather than inlined. The term-mode proof does the same thing without the <code>show</code>."}
        ],
        done:'No goals.'},
       {t:'code', tag:'illustration', cap:'The tactic form, compiled.',
        src:"example {Q R : Assertion} {c : Cmd}\n    (hlocal : HeapLocal c) (hpres : Preserves c R) : wp c Q ∗ R ⊢ wp c (Q ∗ R) := by\n  show Hoare (wp c Q ∗ R) c (Q ∗ R)\n  exact hoare_frame (wp_sound c Q) hlocal hpres"},
       {t:'p', h:"And the reverse entailment, refuted. The command writes <code>5</code> at <code>l</code>, the postcondition is cut as <code>emp ∗ (l ↦ 5)</code>, and the left-hand side holds of every one-cell heap at <code>l</code>. The right-hand side holds of nothing, because its left conjunct asks for a run of a write that ends with an empty heap, and a write does not deallocate."},
       {t:'code', tag:'illustration', cap:'<code>wp c (Q ∗ R) ⊢ wp c Q ∗ R</code> is false. The refutation opens the star in the right-hand side and reads the empty heap at <code>l</code>.',
        src:"example (l : Loc) :\n    ¬ (wp (.write l (.const 5)) (emp ∗ (l ↦ 5)) ⊢ wp (.write l (.const 5)) emp ∗ (l ↦ 5)) := by\n  intro hbad\n  have hin : wp (.write l (.const 5)) (emp ∗ (l ↦ 5)) (fun _ => 0) (Heap.singleton l 0) :=\n    ⟨⟨fun _ => 0, Heap.write (Heap.singleton l 0) l 5⟩, Exec.write (singleton_same l 0),\n     Heap.empty, Heap.singleton l 5, (fun x => Or.inl rfl),\n     by rw [write_singleton, union_empty_left], rfl, rfl⟩\n  obtain ⟨h₁, h₂, hd, hu, ⟨s', hex, he⟩, hr⟩ := hbad _ _ hin\n  cases hex with\n  | write hl =>\n      have hemp : Heap.write h₁ l 5 = Heap.empty := he\n      have hl5 := congrFun hemp l\n      rw [write_same] at hl5\n      exact absurd hl5 (by simp [Heap.empty])"}
     ],
     pitfall:"Trying to prove it directly — <code>intro σ h ⟨hP, hR, hd, hu, hwp, hr⟩</code> and then reconstructing the frame argument by hand. It is provable that way, and it is Unit 27&rsquo;s eight lines written out again with <code>wp</code> substituted for <code>P</code>. The exercise is not to redo that work but to notice that it has already been done, for an arbitrary <code>P</code>, and that <code>wp c Q</code> is a <code>P</code>.",
     variants:"Drop <code>hpres</code> and the statement is false, and the witness is a store fact rather than a heap: take <code>c</code> to be <code>x := 5</code>, <code>Q</code> to be <code>emp</code> and <code>R</code> to be <code>fact (fun σ => σ x = 0)</code>. The empty heap with <code>x</code> zero is in <code>wp c Q ∗ R</code> and in nothing on the right, because the command falsifies the frame — which is Unit 27&rsquo;s refutation of <code>hoare_frame</code> in the <code>wp</code> spelling. Drop <code>hlocal</code> and the statement is still true of this language, and still provable — but not in one line. <code>hoare_frame</code> is the only route to the conclusion and it wants a <code>HeapLocal c</code>, so you would first have to produce one for an arbitrary <code>c</code>, by recursion over <code>Cmd</code> citing the eight locality lemmas of Units 24 to 26 in turn. Unit 29 called those lemmas &ldquo;always a name you look up&rdquo;; that is true when the command is a constructor and false when it is a variable. Reversing the entailment fails outright, and the refutation is above."},

    {t:'p', h:"That reversal is worth a closing remark, because it is the general shape of the frame rule and not a quirk of <code>wp</code>. Framing lets you carry a resource across a command; it does not let you decide, after the fact, which part of the final heap was the frame. Splitting the postcondition is a choice made in advance, and it is the same choice Unit 27 identified as the only decision in the proof of <code>hoare_frame</code>."},

    /* ========================================================== closing ==== */

    {t:'dod', h:"You can define a predicate transformer and say which of the two readings it takes; prove that <code>Hoare P c Q</code> and <code>P ⊢ wp c Q</code> are one proposition, and use that identification without ceremony in both directions; compute <code>wp</code> for <code>skip</code>, <code>assign</code> and <code>;;</code>, and re-derive all four structural rules of Unit 22 from the results; say which direction to drive a verification in, and why only one of the two can be run by a machine; state soundness and optimality as theorems and use them to check a precondition someone hands you; compute <code>wp</code> against a concrete postcondition for <code>free</code> and <code>write</code>, recognise the existential over the unread value, and refute a candidate precondition that is sufficient without being weakest; and transport the frame rule in one term."},

    {t:'p', h:"There is a limit to what has been computed, and it is not about <code>wp</code>. Every assertion so far describes a <i>bounded</i> number of cells. A linked list does not, and no finite combination of <code>↦</code> and <code>∗</code> can describe one."}

  ]
});
