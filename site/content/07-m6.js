/* M6 — Hoare triples
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m6 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm6',
  num: 'M6',
  phase: 'Phase 2 · Program logic',
  title: 'Hoare triples',
  blurb: 'Connecting assertions to execution — and the structural rules that let you stop unfolding the semantics.',

  orient: {
    youWill: [
      'Bridge a change of store with an operation on assertions, and never write a syntactic substitution.',
      'Read <code>Hoare P c Q</code> as the statement it unfolds to, and write that unfolding down before Lean shows it to you.',
      'Prove consequence, skip and sequencing straight from <code>Exec</code> — and then stop unfolding <code>Exec</code> for good.',
      'Exhibit two commands that satisfy every partial triple and no total one, for unrelated reasons.',
      'Verify a two-command program by choosing its intermediate assertion, which is the whole of the proof.'
    ],
    needs: [
      'M5’s <code>Exec</code> and its constructors, and <code>Store.set</code>.',
      'M3’s <code>emp</code>, <code>fact</code>, <code>aAnd</code>, and <code>⊢</code> applied to three arguments.',
      'Nothing about <code>∗</code>. It comes back in M7.'
    ],
    payoff: 'Every verification after this one is composition of triples: M7 adds the three heap rules, M8 the frame rule, M9 runs them on programs.'
  },

  blocks: [

    /* ================================================================
       1 — the operation M5 stopped for
       ================================================================ */

    { t: 'h3', s: 'Substitution, done semantically' },

    { t: 'p', h: 'The operation you need turns an assertion about the store <i>after</i> an assignment into one about the store <i>before</i> it. Classical Hoare logic writes it <code>Q[e/x]</code> and states the assignment axiom as <code>{Q[e/x]} x := e {Q}</code>: to have <code>Q</code> afterwards, demand beforehand what <code>Q</code> says with <code>e</code> in place of <code>x</code>. The bracket is the awkward part. Here it is, without the syntax.' },

    { t: 'code', src: "def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ h => Q (Store.set σ x (e.eval σ)) h" },

    { t: 'anat',
      src: "def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ h => Q (Store.set σ x (e.eval σ)) h",
      parts: [
        { m: '(e : Atom)',
          h: 'The expression stays syntax; only the assertion is semantic. That asymmetry is the trick. You need syntax for the thing the program executes, because the program is a tree. You do not need syntax for the thing you assert.' },
        { m: 'fun σ h =>',
          h: '<code>subst x e Q</code> is an <code>Assertion</code>, so it is a function of a store and a heap. Building it as a lambda rather than by recursion on the structure of <code>Q</code> is what makes the definition one line.' },
        { m: 'Store.set σ x (e.eval σ)',
          h: 'The store you would get after running <code>x := e</code>. Two separate facts live here. <code>e.eval σ</code> reads the <i>old</i> store — the right-hand side is evaluated before the write, which is the content of the assignment axiom. And there is no capture condition: a syntactic <code>Q[e/x]</code> has to worry about a binder inside <code>Q</code> capturing a variable free in <code>e</code>, but <code>Q</code> binds no program variables at all. It is a function of the whole store.' },
        { m: 'Q (Store.set σ x (e.eval σ)) h',
          h: 'The heap goes through untouched. When M7 states the rule for a <i>load</i> this shape stops working, because a load reads the heap — and that is the crack the rest of the course grows out of.' }
      ] },

    { t: 'cmp',
      left: { t: 'Deep embedding — assertions are syntax', kind: 'bad',
        h: 'Assertions become an inductive type <code>Form</code>. You then need a semantics <code>⟦·⟧ : Form → Assertion</code>, a capture-avoiding <code>Form.subst</code>, and a <b>substitution lemma</b> — <code>⟦Q[e/x]⟧ σ h ↔ ⟦Q⟧ (Store.set σ x (e.eval σ)) h</code> — proved by induction over <code>Form</code> with a side condition about free variables. Only then is the assignment rule provable. Every connective you add later reopens that induction.' },
      right: { t: 'Shallow embedding — assertions are functions', kind: 'good',
        h: '<code>subst</code> <i>is</i> the substitution lemma, and its proof is <code>rfl</code>. No capture, no free-variable predicate, no induction, and a new connective costs nothing because connectives are functions.',
        src: "example (x : Var) (e : Atom) (Q : Assertion) (σ : Store) (h : Heap) :\n    subst x e Q σ h = Q (Store.set σ x (e.eval σ)) h := rfl" } },

    { t: 'p', h: 'That <code>rfl</code> compiles, and it is the entire content of the comparison. The bill for the shallow embedding falls due somewhere this workbook never goes: with no syntax for assertions there is no induction over their structure, so you cannot state anything of the form “every assertion is equivalent to one in normal form”. A paper on the decidability of an assertion language needs the deep embedding. A course on ownership does not.' },

    /* ================================================================
       2 — the triple
       ================================================================ */

    { t: 'h3', s: 'What a triple says' },

    { t: 'p', h: 'Everything the definition needs now exists.' },

    { t: 'code', src: "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap" },

    { t: 'quote', h: 'From <b>every</b> state satisfying <code>P</code>, the command runs without getting stuck and lands in a state satisfying <code>Q</code>.' },

    { t: 'anat',
      src: "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap",
      parts: [
        { m: ': Prop',
          h: 'A triple is a proposition, not a piece of syntax and not an inductively generated judgement. There is no derivation system here, so the “rules” proved below are ordinary theorems about this statement — and there is no soundness theorem anywhere in the course, because soundness is the definition. That is the difference between a <b>semantic</b> and a <b>syntactic</b> program logic, and it is the whole reason the exercises are short.' },
        { m: '∀ σ h',
          h: 'A store and a heap separately, not one <code>State</code>, because that is what an assertion eats. A triple is the seam where the two representations meet, so a conversion has to happen somewhere; here it happens twice, in opposite directions, in the two conjuncts.' },
        { m: 'P σ h →',
          h: 'The precondition is a hypothesis: only ever used, never proved. An unsatisfiable one therefore makes the triple free — <code>Hoare aFalse c Q</code> for every <code>c</code> and <code>Q</code>, by <code>intro σ h hp</code> then <code>exact hp.elim</code>. That is the degenerate end of the contravariance <code>hoare_consequence</code> makes official.' },
        { m: "∃ s'",
          h: 'The load-bearing quantifier of the chapter. A final state exists exactly when a derivation exists, and M5 built <code>Exec</code> so that neither exists for a run that faults or diverges. One symbol, and it buys both.' },
        { m: "Exec c ⟨σ, h⟩ s'",
          h: 'The anonymous constructor assembling the two binders into a <code>State</code>, which is what <code>Exec</code> relates. Lean prints it back as <code>{ store := σ, heap := h }</code> — the same term, written out.' },
        { m: "Q s'.store s'.heap",
          h: 'The conversion running the other way. Every goal in this chapter displays those projections literally, often applied to a state you have just supplied: <code>{ store := σ.set x 10, heap := h }.store</code>. Lean will not tidy that for you, so learn to read past it.' }
      ] },

    { t: 'detail', title: 'Why those projections never get in your way', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'A goal containing <code>{ store := σ, heap := h }.store</code> looks like it needs a simplification step. It does not: projecting an explicit constructor is iota reduction, so that term <i>is</i> <code>σ</code> to the type checker.' },
        { t: 'p', h: 'The reverse direction is the surprising one. In <code>hoare_seq</code> below you obtain a hypothesis of type <code>Exec c₂ { store := s₁.store, heap := s₁.heap } s₂</code> and hand it to a constructor wanting <code>Exec c₂ s₁ s₂</code>, where <code>s₁</code> is an opaque variable with no constructor in sight. It is accepted because Lean 4 has <b>eta for structures</b>: rebuilding a structure from its own projections gives back something definitionally equal to the original.' },
        { t: 'code', tag: 'illustration',
          cap: 'Compiles against the M6 prelude. On paper you would not write this down; in Lean it is why <code>exact</code> succeeds where you expected a mismatch, and why you should not go looking for the rewrite.',
          src: "-- structure eta: a state is its own two projections, by rfl\nexample (s : State) : ({ store := s.store, heap := s.heap } : State) = s := rfl" }
      ] },

    { t: 'p', h: 'A triple is an ordinary application, its arguments are positional, and both assertions have the same type. Swap the pre- and postcondition by accident and what you wrote is still well-typed — merely false. Read the order off the definition, precondition first, once per proof.' },

    /* ================================================================
       3 — what the existential rules out
       ================================================================ */

    { t: 'h3', s: 'Two commands with no derivations' },

    { t: 'p', h: 'What makes the definition <b>total correctness</b> is where <code>Exec</code> sits: to the right of the arrow, so you must produce a run. Move it to the left and you may assume one instead.' },

    { t: 'code', src: "def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap" },

    { t: 'cmp',
      left: { t: '<code>Hoare</code> — total correctness', kind: 'good',
        h: '<code>s\'</code> is bound by <code>∃</code>, so nothing is vacuous. To prove the triple you exhibit a derivation, and exhibiting it <i>is</i> the termination argument.' },
      right: { t: '<code>PartialHoare</code> — partial correctness',
        h: '<code>s\'</code> is bound by <code>∀</code> and the derivation is a hypothesis. If there is no derivation the statement holds for nothing, which is the escape hatch that makes non-terminating programs specifiable. M13 uses it for real.' } },

    { t: 'p', h: 'Two commands have no derivations at all, for unrelated reasons. Both satisfy every partial triple and no total one.' },

    { t: 'h4', s: 'The one that faults' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M6 prelude. <code>cases hex</code> asks which constructor could have produced the derivation; only <code>Exec.load</code> can, and it carries <code>hl : h l = some v</code>, which the precondition <code>h = Heap.empty</code> contradicts.',
      src: "-- a load from the empty heap satisfies every partial triple, vacuously\ntheorem partial_load_emp (x : Var) (l : Loc) (Q : Assertion) :\n    PartialHoare emp (.load x l) Q := by\n  intro σ h s' he hex\n  cases hex with\n  | load hl => rw [he] at hl; simp [Heap.empty] at hl\n\n-- but no total triple, not even with the weakest possible postcondition\ntheorem not_hoare_load_emp (x : Var) (l : Loc) :\n    ¬ Hoare emp (.load x l) aTrue := by\n  intro hc\n  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | load hl => simp [Heap.empty] at hl" },

    { t: 'h4', s: 'The one that diverges' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M6 prelude. The induction is on the <i>derivation</i>: <code>loopFalse</code> needs the guard false, which <code>simp</code> refutes; <code>loopTrue</code> hands back an induction hypothesis for the same loop, so the argument closes on itself. Every other constructor dies on the equation <code>hc</code>.',
      src: "def forever : Cmd := .loop (.equals (.const 0) (.const 0)) .skip\n\ntheorem no_exec_forever : ∀ {c : Cmd} {s s' : State}, c = forever → Exec c s s' → False := by\n  intro c s s' hc hex\n  induction hex with\n  | loopFalse hb =>\n      cases hc; simp [BExpr.eval, Atom.eval] at hb\n  | loopTrue hb hbody hrest ihb ihr => exact ihr hc\n  | _ => cases hc\n\ntheorem partial_forever (P Q : Assertion) : PartialHoare P forever Q := by\n  intro σ h s' hp hex\n  exact (no_exec_forever rfl hex).elim\n\ntheorem not_hoare_forever : ¬ Hoare emp forever aTrue := by\n  intro hc\n  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty rfl\n  exact no_exec_forever rfl hex" },

    { t: 'detail', title: 'Why <code>no_exec_forever</code> carries an equation instead of just <code>¬ Exec forever s s\'</code>', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'The statement you would write on paper is <code>Exec forever s s\' → False</code>. Write that and <code>induction</code> refuses before you have typed a single case:' },
        { t: 'state', cap: 'Produced by <code>intro hex; induction hex</code> on the direct statement.',
          src: "error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)\n  forever" },
        { t: 'p', h: '<code>Exec</code> is indexed by the command, and the recursor generalises over that index, so the tactic needs a local variable there — otherwise the induction hypothesis it would have to build is not well-formed. Here the index is the constant <code>forever</code>.' },
        { t: 'p', h: 'The fix is to generalise the index by hand and record what it was: <code>{c : Cmd} → c = forever → Exec c s s\' → False</code>. Now <code>c</code> is a variable, the induction goes through, and each case opens by spending <code>hc</code> — to specialise, as in the <code>loopFalse</code> branch where <code>cases hc</code> turns the guard into <code>0 == 0</code>, or to die, as in the catch-all where <code>hc</code> equates two different constructors of <code>Cmd</code>. The same manoeuvre reappears in M13.' }
      ] },

    { t: 'p', h: 'Look at which postcondition those two refutations use. An unsatisfiable precondition makes a triple free, but an uninformative postcondition does not: <code>Hoare P c aTrue</code> still claims that <code>c</code> runs to completion from every <code>P</code>-state, and that is exactly what both theorems deny.' },

    { t: 'p', h: 'A big-step semantics cannot tell a fault from a divergence — both are the same missing derivation — and neither can a partial triple. M13 pays that bill. The other direction is free, and determinism is the only thing doing any work in it.' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M6 prelude. <code>PartialHoare</code> hands you an <i>arbitrary</i> run to <code>s\'</code>, while the total triple produced a run to an <code>s\'\'</code> of its own choosing; nothing but <code>exec_deterministic</code> identifies the two. <code>subst hs</code> then eliminates <code>s\'</code> and <code>hq</code> closes the goal.',
      src: "theorem partial_of_total {P Q : Assertion} {c : Cmd} (ht : Hoare P c Q) :\n    PartialHoare P c Q := by\n  intro σ h s' hp hex\n  obtain ⟨s'', hex'', hq⟩ := ht σ h hp\n  have hs : s' = s'' := exec_deterministic hex hex''\n  subst hs\n  exact hq" },

    /* ================================================================
       4 — structural rules
       ================================================================ */

    { t: 'sec', s: 'Exercises · structural rules' },

    { t: 'note', kind: 'key', title: 'The shape of all five proofs',
      h: 'You prove a triple by producing a witness: the final state, a derivation that reaches it, and the postcondition at it. Every proof below is <code>intro σ h hp</code> followed by one <code>⟨…⟩</code> holding those three things.' },

    { t: 'ex',
      id: 'm6-1',
      name: 'hoare_consequence',
      hard: false,
      why: 'Strengthen the precondition, weaken the postcondition. This is the door every Phase 1 entailment walks through into the program logic: <code>star_comm</code>, <code>star_assoc_left</code>, <code>two_cells_distinct</code> mention no command, and this rule is what lets them retype a specification. It is also the only rule that changes the shape of a spec without touching the program, so it is what you reach for when a primitive rule from M7 <i>nearly</i> matches the goal — M9 is largely <code>hoare_consequence (entails_refl _) step ?_</code> with the <code>∗</code>-algebra of M4 in the hole.',
      setup: 'In scope: <code>Hoare</code>, and <code>Entails</code> written <code>⊢</code>. No lemma about <code>Exec</code> is needed. The command <code>c</code> stays completely opaque, which is the point.',
      goal: "theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare P c Q) (hpost : Q ⊢ Q') : Hoare P' c Q'",
      hints: [
        'There is nothing to apply and nothing to case on. Write <code>intro σ h hp</code> and read what the goal turns into — <code>intro</code> unfolds <code>Hoare</code> on its own, so <code>unfold</code> never appears in this chapter.',
        'You have <code>hp : P\' σ h</code> and <code>hc</code> wants <code>P σ h</code>. <code>hpre</code> converts it — but <code>hpre : P\' ⊢ P</code> is <code>∀ σ h, P\' σ h → P σ h</code>, so it takes <b>three</b> arguments: <code>hpre σ h hp</code>.',
        '<code>hc σ h (hpre σ h hp)</code> is an existential. Take it apart with <code>obtain ⟨s\', hex, hq⟩ := …</code> — witness state, derivation, postcondition at that state.',
        'Rebuild the goal with the <i>same</i> witness and the <i>same</i> derivation, changing only the last component: <code>exact ⟨s\', hex, hpost s\'.store s\'.heap hq⟩</code>.'
      ],
      sol: "theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare (P) (c) (Q)) (hpost : Q ⊢ Q') : Hoare (P') (c) (Q') := by\n  intro σ h hp\n  obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)\n  exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
      expl: 'Pure plumbing, but the variance is worth naming: <code>P\'</code> must be <i>stronger</i> than <code>P</code>, <code>Q\'</code> <i>weaker</i> than <code>Q</code>. Unfolded, a triple has <code>P</code> to the left of an arrow and <code>Q</code> to the right, so it is the variance of a function type and holds for the same reason. You may always demand more of the caller and promise less. The proof never inspects <code>c</code>, which is why the rule already covers the commands we have no rules for yet.',
      walk: [
        { tac: 'intro σ h hp',
          h: 'The goal displayed as <code>Hoare P\' c Q\'</code>, which is not visibly a <code>∀</code>. <code>intro</code> succeeds anyway: it unfolds definitions on demand until it finds a binder. Three come off at once — store, heap, and the precondition — leaving the raw existential.' },
        { tac: "obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)",
          h: 'Two moves in one line. <code>hpre σ h hp : P σ h</code> converts the precondition; <code>hc σ h …</code> then runs the triple you were handed. <code>obtain</code> splits the resulting existential-of-conjunction in a single pattern.' },
        { tac: "exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
          h: 'The goal wants that shape with <code>Q\'</code> in place of <code>Q</code>. Nothing about the run changed, so the witness and the derivation are reused verbatim and only the last component is post-composed — with <code>hpost</code> applied to the store, the heap, and the proof.' }
      ],
      deep: [
        { t: 'trace', title: 'hoare_consequence, tactic by tactic',
          start: "P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\n⊢ Hoare P' c Q'",
          steps: [
            { tac: 'intro σ h hp',
              state: "P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\nσ : Store\nh : Heap\nhp : P' σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q' s'.store s'.heap",
              h: 'The moment to pause on: the goal you were shown as <code>Hoare P\' c Q\'</code> is <i>this</i>. The <code>⟨σ, h⟩</code> of the definition comes back as <code>{ store := σ, heap := h }</code>.' },
            { tac: "obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)",
              state: "P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\nσ : Store\nh : Heap\nhp : P' σ h\ns' : State\nhex : Exec c { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q' s'.store s'.heap",
              h: 'The goal has not moved; the context grew by exactly three things. <code>hex</code> matches the left conjunct of the goal on the nose. <code>hq</code> matches the right one except for <code>Q</code> against <code>Q\'</code>. That single mismatch is all that is left to do.' },
            { tac: "exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
              state: 'No goals.',
              h: 'The brackets build <code>Exists.intro s\' (And.intro hex …)</code>, which is why three entries suffice for a nested pair.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'What the reversed rule would let you prove', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'Suppose the rule read <code>(hpre : P ⊢ P\') → Hoare P c Q → Hoare P\' c Q</code>, weakening the precondition instead of strengthening it. Take <code>P := emp</code>, <code>P\' := aTrue</code>, <code>c := .skip</code>, <code>Q := emp</code>. The hypothesis <code>emp ⊢ aTrue</code> is trivial and <code>Hoare emp .skip emp</code> is <code>hoare_skip</code>, so you would get <code>Hoare aTrue .skip emp</code>: from any state, <code>skip</code> leaves you owning nothing. Here is the heap that refutes it.' },
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M6 prelude. The <code>have he\' : … := he</code> line is not a no-op: <code>he</code> has type <code>emp { store := …, heap := Heap.singleton 0 0 }.store { … }.heap</code>, and restating it at the definitionally equal type is what lets <code>rw</code> find a pattern. Delete the line and <code>rw [he]</code> reports <code>Did not find an occurrence of the pattern { store := fun x => 0, heap := Heap.singleton 0 0 }.heap</code>. Standing rule: <code>exact</code> and <code>have</code> work up to definitional equality, <code>rw</code> and <code>simp</code> match syntax.',
              src: "theorem not_hoare_true_skip_emp : ¬ Hoare aTrue Cmd.skip emp := by\n  intro hc\n  obtain ⟨s', hex, he⟩ := hc (fun _ => 0) (Heap.singleton 0 0) trivial\n  cases hex\n  have he' : Heap.singleton 0 0 = Heap.empty := he\n  have h0 : Heap.singleton 0 0 0 = Heap.empty 0 := by rw [he']\n  rw [singleton_same] at h0\n  exact absurd h0 (by simp [Heap.empty])" },
            { t: 'p', h: 'The same instance refutes the reversed postcondition rule: take <code>P := aTrue</code>, <code>Q := aTrue</code>, <code>Q\' := emp</code>, and note <code>emp ⊢ aTrue</code>.' }
          ] }
      ],
      pitfall: 'Applying an entailment to one argument. <code>hpre</code> looks like an implication, so you write <code>hpre hp</code>, and Lean says it wanted a <code>Store</code>: <br><code>Application type mismatch: The argument hp has type P\' σ h of sort `Prop` but is expected to have type Store of sort `Type` in the application hpre hp</code>. <br>The fix is <code>hpre σ h hp</code>. The same slip recurs at <code>hpost hq</code>, where the fix is <code>hpost s\'.store s\'.heap hq</code> — and note that those two arguments are projections of the <i>witness</i> state, not the original <code>σ</code> and <code>h</code>, because a postcondition is evaluated after the run.',
      variants: 'Drop <code>hpre</code> and the statement is false the moment <code>P\'</code> holds somewhere <code>P</code> does not: <code>hoare_skip emp</code> would yield <code>Hoare aTrue .skip emp</code>, refuted above. Reverse either entailment and the same counterexample applies. Drop <code>hpost</code> and there is no conclusion left to state. Keep all three hypotheses and the trace shows where each is spent: <code>hpre</code> on line 2, <code>hpost</code> on line 3, and <code>hc</code> supplying the witness that neither of them could produce.'
    },

    { t: 'ex',
      id: 'm6-2',
      name: 'hoare_skip / hoare_seq',
      hard: false,
      why: 'The two rules that turn a list of triples into a proof about a program. <code>hoare_skip</code> is the base case you will barely notice. <code>hoare_seq</code> you will use in every remaining chapter, and it is the first place where <i>you</i> have to invent something: the intermediate assertion is not determined by the statement.',
      setup: 'In scope: <code>Hoare</code>, plus <code>Exec.skip</code> and <code>Exec.seq : Exec c₁ s s\' → Exec c₂ s\' s\'\' → Exec (c₁ ;; c₂) s s\'\'</code>, which glues two derivations that agree at the middle state.',
      goal: "theorem hoare_skip (P : Assertion) : Hoare P .skip P\n\ntheorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare P c₁ Q) (h₂ : Hoare Q c₂ R) : Hoare P (c₁ ;; c₂) R",
      hints: [
        'For <code>hoare_skip</code>, ask what the witness has to be. <code>skip</code> changes nothing, so the final state is the initial one, <code>⟨σ, h⟩</code>, and everything else follows.',
        '<code>hoare_skip</code> needs no tactics at all. A proof of <code>∀ σ h, P σ h → …</code> is a function <code>fun σ h hp => …</code>, and its body is one anonymous constructor with three entries.',
        'For <code>hoare_seq</code>, run <code>h₁</code> on the initial store and heap to get an intermediate state <code>s₁</code>. Then run <code>h₂</code> — which wants a store and a heap, not a state, so feed it <code>s₁.store s₁.heap</code>.',
        'Run <code>h₁</code>, feed its final state to <code>h₂</code>, and glue the two derivations with <code>Exec.seq</code>.'
      ],
      sol: "theorem hoare_skip (P : Assertion) : Hoare (P) (.skip) (P) :=\n  fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩\n\ntheorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by\n  intro σ h hp\n  obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp\n  obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq\n  exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩",
      expl: 'The intermediate assertion <code>Q</code> appears in the hypotheses and not in the conclusion, so unification can never find it and you supply it by hand: <code>hoare_seq (Q := …) h₁ h₂</code>. Choosing that assertion <i>is</i> the act of verifying a program. Everything else in this proof is plumbing.',
      walk: [
        { tac: 'fun σ h hp =>',
          h: '<code>hoare_skip</code> is a term, not a tactic block. A proof of a <code>∀</code>-statement is a function, so the three binders of the unfolded <code>Hoare</code> become three lambda arguments; Lean checks the body against the unfolded type, so no <code>unfold</code> or <code>show</code> is wanted.' },
        { tac: '⟨⟨σ, h⟩, Exec.skip, hp⟩',
          h: 'Three entries for the existential-of-conjunction, with the inner <code>⟨σ, h⟩</code> the <code>State</code>. <code>Exec.skip</code> takes no argument: its type <code>Exec .skip s s</code> forces the two states to coincide, and unification reads off <code>s := ⟨σ, h⟩</code>. And <code>hp : P σ h</code> is accepted as a proof of <code>P ⟨σ, h⟩.store ⟨σ, h⟩.heap</code> because those projections reduce.' },
        { tac: 'intro σ h hp',
          h: '<code>hoare_seq</code> opens the same way, exposing an existential over the final state of the whole sequence.' },
        { tac: 'obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp',
          h: 'Run the first triple. <code>s₁</code> is the state after <code>c₁</code>, and <code>hq : Q s₁.store s₁.heap</code> puts the intermediate assertion exactly where you would want it.' },
        { tac: 'obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq',
          h: 'Run the second triple <i>from</i> <code>s₁</code>. Because <code>Hoare</code> quantifies over a store and a heap separately you must project — and so the derivation comes back stated at <code>{ store := s₁.store, heap := s₁.heap }</code> rather than at <code>s₁</code>.' },
        { tac: 'exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩',
          h: '<code>Exec.seq</code> wants <code>Exec c₂ s₁ s₂</code> and receives <code>Exec c₂ { store := s₁.store, heap := s₁.heap } s₂</code>. Structure eta makes those the same type, and <code>exact</code> checks up to definitional equality, so no rewrite is needed.' }
      ],
      deep: [
        { t: 'trace', title: 'hoare_seq, tactic by tactic',
          start: 'P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\n⊢ Hoare P (c₁ ;; c₂) R',
          steps: [
            { tac: 'intro σ h hp',
              state: "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
              h: 'One existential, for the final state of the <i>whole</i> sequence. The intermediate state is nowhere in the goal — it will exist only inside the derivation you build.' },
            { tac: 'obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp',
              state: "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\nσ : Store\nh : Heap\nhp : P σ h\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\nhq : Q s₁.store s₁.heap\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
              h: '<code>s₁</code> is now a genuine object in the context, and <code>hq</code> is the only appearance of the intermediate assertion in the whole proof. It gets used once, as the input to <code>h₂</code>.' },
            { tac: 'obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq',
              state: "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\nσ : Store\nh : Heap\nhp : P σ h\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\nhq : Q s₁.store s₁.heap\ns₂ : State\nhex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂\nhr : R s₂.store s₂.heap\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
              h: 'Look hard at <code>hex₂</code>. Its source state is <code>{ store := s₁.store, heap := s₁.heap }</code>, not <code>s₁</code> — the round trip through the projections left a visible scar. <code>Exec.seq</code> will accept it against <code>hex₁</code>, whose target is <code>s₁</code> exactly.' },
            { tac: 'exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩',
              state: 'No goals.',
              h: 'Witness <code>s₂</code>, derivation <code>Exec.seq hex₁ hex₂</code>, postcondition <code>hr</code>. The gluing happens at <code>s₁</code>, which is where the eta reduction silently happens.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'Named arguments: what <code>(Q := …)</code> means', tag: 'syntax', open: false,
          blocks: [
            { t: 'p', h: '<code>Q</code> is implicit, and implicit arguments are normally solved by unification against the goal. But the goal is <code>Hoare P (c₁ ;; c₂) R</code>, in which <code>Q</code> does not occur, so unification has nothing to work with. A named argument says what it is: <code>hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_</code> sets one implicit by name and leaves the rest alone. Omit it and Lean tells you precisely what is missing:' },
            { t: 'state',
              cap: 'What <code>refine hoare_seq ?_ ?_</code> produces on the M6-5 goal. The <code>?m.12</code> in the second position is the unsolved <code>Q</code>, and <code>⊢ Assertion</code> is Lean asking you for it.',
              src: "error: don't know how to synthesize implicit argument `Q`\n  @hoare_seq emp ?m.12 (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp) (Cmd.assign x (Atom.const 3))\n    (Cmd.assign y (Atom.var x)) ?m.16 ?m.17\ncontext:\nx y : Var\n⊢ Assertion" },
            { t: 'p', h: 'There is a second way — <code>apply hoare_seq</code>, leave the metavariable open, and let the subgoals force it. Avoid it here. The intermediate assertion is a design decision, and postponing a design decision until unification guesses it is how you end up with a proof you cannot read.' }
          ] },

        { t: 'detail', title: 'The same rule for partial correctness', tag: 'aside', open: false,
          blocks: [
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M6 prelude. You are <i>given</i> a derivation of the sequence, so <code>cases</code> takes it apart, and the intermediate state falls out of the derivation instead of out of a triple you had to run.',
              src: "theorem partial_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) : PartialHoare P (c₁ ;; c₂) R := by\n  intro σ h s' hp hex\n  cases hex with\n  | seq hex₁ hex₂ => exact h₂ _ _ _ (h₁ σ h _ hp hex₁) hex₂" },
            { t: 'p', h: 'The trade is on display: the total version had to build <code>Exec.seq hex₁ hex₂</code>, and building it is the termination argument. The partial version builds nothing.' }
          ] }
      ],
      pitfall: 'Feeding <code>h₂</code> a state instead of a store and a heap. <code>h₂ s₁ hq</code> looks natural — <code>s₁</code> is the state you just produced — and Lean answers <br><code>Application type mismatch: The argument s₁ has type State but is expected to have type Store in the application h₂ s₁</code>. <br>The fix is <code>h₂ s₁.store s₁.heap hq</code>. This is the one place where quantifying over <code>σ</code> and <code>h</code> separately costs you anything, and the cost is one projection per sequencing step.',
      variants: '<code>hoare_skip</code> looks too weak to bother stating — why the same <code>P</code> on both sides? Because that instance generates the others: <code>Hoare P .skip Q</code> holds <b>if and only if</b> <code>P ⊢ Q</code>, backwards by <code>hoare_consequence (entails_refl P) (hoare_skip P) he</code> and forwards by <code>cases</code> on the derivation, which forces the final state to be the initial one. So <code>hoare_skip P</code> is the strongest true triple for <code>skip</code> and everything else is consequence. <br><br><code>hoare_seq</code> asks nothing of the two commands: no disjointness, and no condition on <code>Q</code> beyond both halves agreeing on it. The two degenerate choices are legal and useless, but not symmetrically. <code>Q := aFalse</code> makes the second premise free and the first unprovable unless <code>P</code> is itself unsatisfiable. <code>Q := aTrue</code> makes the second premise normally unprovable while leaving the first with real work, since <code>Hoare P c₁ aTrue</code> still asserts that <code>c₁</code> terminates without faulting — which is what <code>not_hoare_load_emp</code> and <code>not_hoare_forever</code> deny. What a degenerate <code>Q</code> loses is information, not labour. Picking the <code>Q</code> in between is the skill. <br><br>Swap <code>Hoare</code> for <code>PartialHoare</code> throughout and the rule still holds, with a shorter proof: you receive the composite derivation and take it apart, instead of building it.'
    },

    { t: 'ex',
      id: 'm6-3',
      name: 'hoare_assign',
      hard: false,
      why: 'The assignment axiom. With a semantic <code>subst</code> it is nearly a tautology, and that is the point of having built <code>subst</code> first. It is also your template for backwards reasoning: given a postcondition, <code>subst</code> <i>computes</i> the precondition, and M12 turns that observation into a weakest-precondition calculus.',
      setup: 'In scope: <code>subst</code>, <code>Store.set</code>, and <code>Exec.assign</code>, whose indices force the final state to be <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code>. You do not get to choose it.',
      goal: "theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (subst x e Q) (.assign x e) Q",
      hints: [
        'Write the witness down first. What state does <code>x := e</code> produce from <code>⟨σ, h⟩</code>? The heap is untouched and the store gains one entry.',
        'Having introduced <code>hq : subst x e Q σ h</code>, unfold it in your head: it is <code>Q (Store.set σ x (e.eval σ)) h</code> — the postcondition at the state you just wrote down. No conversion is needed; <code>hq</code> already has the type you want.',
        'The final state is <code>⟨Store.set σ x (e.eval σ), h⟩</code>, and <code>subst x e Q σ h</code> is <i>by definition</i> <code>Q</code> there.'
      ],
      sol: "theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (subst x e Q) ((.assign x e)) (Q) := by\n  intro σ h hq\n  exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
      expl: 'Two lines, and the precondition is handed back as the postcondition without being touched — because they are the same term. The deep embedding would need a substitution function on assertion syntax plus a lemma relating it to the semantics before this theorem could even be stated.',
      walk: [
        { tac: 'intro σ h hq',
          h: 'The usual three binders. <code>hq : subst x e Q σ h</code> is displayed folded, not as the store update it unfolds to — which is fine here precisely because you never look inside it.' },
        { tac: 'exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩',
          h: 'Witness, derivation, postcondition. The witness is strictly redundant: <code>exact ⟨_, Exec.assign, hq⟩</code> also compiles, because <code>Exec.assign</code>’s indices determine the final state. Write it out anyway — it is the state the theorem is <i>about</i>, and from M7 on the derivation will not always pin it down. And <code>hq</code> closes the third component because <code>subst x e Q σ h</code> and <code>Q ⟨Store.set σ x (e.eval σ), h⟩.store ⟨…⟩.heap</code> are definitionally identical: unfold <code>subst</code>, apply the lambda, reduce two projections. Three reduction rules, no tactic.' }
      ],
      deep: [
        { t: 'trace', title: 'hoare_assign, tactic by tactic',
          start: 'x : Var\ne : Atom\nQ : Assertion\n⊢ Hoare (subst x e Q) (Cmd.assign x e) Q',
          steps: [
            { tac: 'intro σ h hq',
              state: "x : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\nhq : subst x e Q σ h\n⊢ ∃ s', Exec (Cmd.assign x e) { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
              h: 'Everything needed is on screen. The existential asks for a state, <code>Exec.assign</code> says which one, and <code>hq</code> is already the postcondition there. Nothing is left to prove, only to write down.' },
            { tac: 'exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩',
              state: 'No goals.',
              h: 'Write a witness that is not the state the assignment produces and this is where Lean complains — at <code>Exec.assign</code>, which fails to unify, not at <code>hq</code>.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'The rule in anger: backwards reasoning', tag: 'worked example', open: false,
          blocks: [
            { t: 'p', h: 'M6-4 below proves <code>assign_constant</code> from scratch, by producing the run. Here is the same theorem done the way you will do it from M9 onwards: apply the axiom, and let <code>hoare_consequence</code> leave you a pure entailment — a <i>verification condition</i> — with no program in it.' },
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M6 prelude. <code>entails_refl</code> is M3’s.',
              src: "theorem assign_constant' (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  refine hoare_consequence ?_ (hoare_assign x (.const 10) _) (entails_refl _)\n  intro σ h he\n  show Store.set σ x 10 x = 10 ∧ h = Heap.empty\n  exact ⟨by simp [Store.set], he⟩" },
            { t: 'trace', title: 'What the verification condition looks like',
              start: 'x : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 10)) (aAnd (fact fun σ => σ x = 10) emp)',
              steps: [
                { tac: 'refine hoare_consequence ?_ (hoare_assign x (.const 10) _) (entails_refl _)',
                  state: 'x : Var\n⊢ emp ⊢ subst x (Atom.const 10) (aAnd (fact fun σ => σ x = 10) emp)',
                  h: 'The command has vanished. What remains is a statement about assertions, with <code>subst</code> having already computed the precondition for you.' },
                { tac: 'intro σ h he',
                  state: 'x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ subst x (Atom.const 10) (aAnd (fact fun σ => σ x = 10) emp) σ h',
                  h: 'Still folded, so neither <code>simp</code> nor <code>exact</code> can help: you cannot see what to supply.' },
                { tac: 'show Store.set σ x 10 x = 10 ∧ h = Heap.empty',
                  state: 'x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 10 x = 10 ∧ h = Heap.empty',
                  h: 'One <code>show</code> strips <code>subst</code>, <code>aAnd</code>, <code>fact</code> and <code>emp</code> at once, all four being definitional. Lean re-prints <code>Store.set σ x 10</code> as <code>σ.set x 10</code>.' },
                { tac: 'exact ⟨by simp [Store.set], he⟩',
                  state: 'No goals.',
                  h: 'The right conjunct is <code>he</code> unchanged, because assignment does not touch the heap.' }
              ],
              done: 'No goals.' },
            { t: 'p', h: 'That is the shape of every proof from M9 on: structural rules push the program out of the goal, and what is left is mathematics about stores and heaps. M12 automates the pushing.' }
          ] }
      ],
      pitfall: '<code>subst</code> is a name collision and it will bite you. Here it is the definition above; in Lean it is also the core tactic that eliminates an equational hypothesis. So “open up <code>hq</code>” is spelled <code>unfold subst at hq</code>, and typing <code>subst hq</code> gets you <br><code>Tactic `subst` failed: did not find equation for eliminating \'hq\'</code>. <br>The tactic is not confused about your definition; it is looking for an <code>a = b</code> and finding an assertion. For what it is worth <code>unfold subst at hq</code> is harmless but never necessary — and a hypothesis displayed as <code>subst x e Q σ h</code> is easier to match against the theorem statement than one displayed as <code>Q (σ.set x (Atom.eval σ e)) h</code>.',
      variants: 'Change the witness heap from <code>h</code> to anything else and <code>Exec.assign</code> stops unifying: assignment is defined to preserve the heap, which is what will make this rule frame-friendly in M8. <br><br>Now move the precondition instead. Replace <code>subst x e Q</code> by <code>Q</code> itself — claim <code>Hoare Q (.assign x e) Q</code> — and it is false as soon as <code>Q</code> mentions <code>x</code>: with <code>Q := fact (fun σ => σ x = 0)</code> and <code>e := .const 1</code> the postcondition asserts <code>1 = 0</code>. Weaken to <code>aTrue</code> and that same instance still refutes it. Strengthen to <code>aFalse</code> and the triple becomes true and worthless. <code>subst x e Q</code> is the unique choice that is neither, and precisely: the triple holds, and every <i>other</i> precondition for which it holds entails it. That is what weakest precondition means, and M12 states it as <code>wp (.assign x e) Q ⊣⊢ subst x e Q</code>.'
    },

    /* ================================================================
       5 — programs
       ================================================================ */

    { t: 'sec', s: 'Exercises · small applications' },

    { t: 'p', h: 'The next two are about specific programs rather than about the logic, and both are done from first principles, building the <code>Exec</code> derivation by hand. It is the last time you do that.' },

    { t: 'ex',
      id: 'm6-4',
      name: 'assign_constant',
      hard: false,
      why: 'Your first concrete specification, and the exercise that teaches the most useful reading tactic in the workbook. The postcondition is an <code>aAnd</code> of a <code>fact</code> and an <code>emp</code>, and until you say <code>show</code> the goal is unreadable.',
      setup: 'In scope: <code>emp</code>, <code>aAnd</code>, <code>fact</code>, <code>Store.set</code>, <code>Exec.assign</code>. Nothing else, and no rule proved above — this one is from first principles.',
      goal: "theorem assign_constant (x : Var) :\n    Hoare emp (.assign x (.const 10))\n      (aAnd (fact (fun σ => σ x = 10)) emp)",
      hints: [
        'Same opening as <code>hoare_assign</code>: <code>intro σ h he</code>, then name the final state. Nothing touches the heap, so the witness keeps the <code>h</code> you were given and <code>he</code> proves the <code>emp</code> half of the postcondition unchanged.',
        'Use <code>refine</code> rather than <code>exact</code>, so you can supply what you know and leave a hole for what you have not proved. The brackets flatten, so the postcondition’s conjunction contributes two entries: <code>refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩</code>.',
        'The remaining goal displays as <code>fact (fun σ => σ x = 10) { store := σ.set x 10, heap := h }.store …</code>. That is definitionally an equation between numbers. Say so with <code>show</code>.',
        'After the <code>refine</code>, use <code>show Store.set σ x 10 x = 10</code> to make the goal readable, then <code>simp [Store.set]</code>.'
      ],
      sol: "theorem assign_constant (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  intro σ h he\n  refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩\n  show Store.set σ x 10 x = 10\n  simp [Store.set]",
      expl: 'The <code>show</code> is the trick worth stealing. <code>fact φ σ h</code> is definitionally <code>φ σ</code>, but <code>simp</code> will not see through <code>fact</code> unless told to — and <code>show</code> is both cheaper and more informative than adding <code>fact</code> to the simp set, because it records in the proof what the goal actually was.',
      walk: [
        { tac: 'intro σ h he',
          h: 'Three binders. <code>he : emp σ h</code>, definitionally <code>h = Heap.empty</code>; you hand it back untouched, so there is no reason to unfold it.' },
        { tac: 'refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩',
          h: 'Four entries for a nominally three-part obligation: witness, derivation, then <code>aAnd A B</code> flattening into its two conjuncts. <code>?_</code> holds the first conjunct, the only thing you must prove; <code>he</code> discharges the second on the spot. Note that <code>.const 10</code> evaluates to <code>10</code> definitionally, so you may write <code>Store.set σ x 10</code> and not <code>Store.set σ x ((Atom.const 10).eval σ)</code>.' },
        { tac: 'show Store.set σ x 10 x = 10',
          h: 'The goal was <code>fact (fun σ => σ x = 10) { … }.store { … }.heap</code>. <code>show</code> replaces a goal by any definitionally equal one, and here that strips <code>fact</code>, applies the lambda and reduces both projections in one step. Logically nothing happened; practically the goal became something you can act on.' },
        { tac: 'simp [Store.set]',
          h: 'Two rewrites, and <code>simp?</code> names them: <code>simp only [Store.set, ↓reduceIte]</code>. The first unfolds the definition to <code>(if x = x then 10 else σ x) = 10</code>, the second decides the conditional. Same one-liner as <code>update_same</code>, for the same reason.' }
      ],
      deep: [
        { t: 'trace', title: 'assign_constant, tactic by tactic',
          start: 'x : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 10)) (aAnd (fact fun σ => σ x = 10) emp)',
          steps: [
            { tac: 'intro σ h he',
              state: "x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign x (Atom.const 10)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 10) emp s'.store s'.heap",
              h: 'The goal wraps over three lines. Read it as: some state, reached by the assignment, at which the conjunction holds.' },
            { tac: 'refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩',
              state: 'x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) { store := σ.set x 10, heap := h }.store { store := σ.set x 10, heap := h }.heap',
              h: 'This is what an unreadable goal looks like. The projections are unreduced, <code>fact</code> is folded, and the <code>σ</code> bound inside the lambda shadows the <code>σ</code> in the context. All three are cosmetic and all three go away with one <code>show</code>.' },
            { tac: 'show Store.set σ x 10 x = 10',
              state: 'x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 10 x = 10',
              h: 'An equation between natural numbers.' },
            { tac: 'simp [Store.set]', state: 'No goals.', h: '' }
          ],
          done: 'No goals.' },

        { t: 'cmp',
          left: { t: 'Without the <code>show</code>', kind: 'bad',
            h: '<code>simp [Store.set]</code> normalises the projections and stops at <code>fact</code>, which is not in its simp set. It then reports the goal unsolved <i>and</i> warns that your simp argument went unused — a confusing pair, because the argument was fine and the wrapper was the problem.',
            src: 'error: unsolved goals\nx : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) (σ.set x 10) h\n\nwarning: This simp argument is unused:\n  Store.set' },
          right: { t: 'With the <code>show</code>', kind: 'good',
            h: '<code>fact</code> is gone before <code>simp</code> runs, so <code>Store.set</code> is the only thing left to unfold and it does get used. <code>simp [fact, Store.set]</code> also works — but then the proof no longer records what the goal <i>was</i>, and the next reader has to re-derive it.',
            src: 'show Store.set σ x 10 x = 10\nsimp [Store.set]' } },

        { t: 'detail', title: 'Why the brackets take four entries', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The obligation is <code>∃ s\', A ∧ (B ∧ C)</code>, whose fully explicit proof is <code>Exists.intro w (And.intro a (And.intro b c))</code>. Written out once, so that the flattening stops being magic:' },
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M6 prelude. Nobody writes proofs this way.',
              src: "example (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  intro σ h he\n  exact Exists.intro ⟨Store.set σ x 10, h⟩\n    (And.intro Exec.assign (And.intro (by show Store.set σ x 10 x = 10; simp [Store.set]) he))" },
            { t: 'p', h: 'The flattening is by <i>position</i>, not by type, so getting the two conjuncts in the wrong order produces a mismatch against whichever component Lean reached. Swapping the last two entries gives <code>Application type mismatch: The argument he has type emp σ h but is expected to have type fact (fun σ => σ x = 10) …</code> — and the error names <code>And.intro</code>, not the outer existential, which tells you how deep the problem is.' }
          ] }
      ],
      pitfall: 'Reaching for <code>simp [Store.set]</code> without the <code>show</code>, and then believing the warning. <code>This simp argument is unused: Store.set</code> reads like an invitation to delete it, but <code>Store.set</code> is not the problem — <code>fact</code> is. The goal <code>fact (fun σ => σ x = 10) (σ.set x 10) h</code> is an application of a constant <code>simp</code> has never been told to unfold, so it never reaches the store update underneath.',
      variants: 'Weaken the postcondition to <code>fact (fun σ => σ x = 10)</code> alone and the <code>refine</code> loses an entry — <code>⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_⟩</code> — and <code>he</code> is never used. No shorter, and one degree less useful: you have dropped the record that the heap is still empty, so the triple can no longer be sequenced with anything needing <code>emp</code>. <br><br>Rewrite the postcondition as <code>pure (fun σ => σ x = 10)</code> and <i>nothing</i> changes, not the proof and not the goal, because <code>pure φ</code> is <code>aAnd (fact φ) emp</code>. That is a renaming. <br><br>Replace <code>emp</code> in the precondition by <code>aTrue</code> and the theorem becomes <b>false</b>. Trace where: <code>he</code> is the only thing that ever proves the <code>emp</code> in the postcondition, and it exists only because the precondition supplied it. With <code>aTrue</code> you get <code>trivial</code> instead, which says nothing about the heap — and a starting heap of <code>Heap.singleton 0 0</code> refutes the triple by the same argument as <code>not_hoare_true_skip_emp</code>. Assignment does not clear memory.'
    },

    { t: 'ex',
      id: 'm6-5',
      name: 'assign_twice',
      hard: false,
      why: 'Your first two-command proof, and the first time you choose an intermediate assertion — the skill the rest of the workbook is built on. The interesting part is what you <i>do not</i> need.',
      setup: 'In scope: <code>hoare_seq</code>, plus everything used in M6-4. The program is <code>x := 3 ;; y := x</code>, and nothing says <code>x</code> and <code>y</code> are distinct.',
      goal: "theorem assign_twice (x y : Var) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp)",
      hints: [
        'Do not start with <code>intro</code>. The command is a sequence, so the first move is <code>hoare_seq</code>, and it fixes the shape of everything after it.',
        '<code>hoare_seq</code> cannot guess the intermediate assertion, since it does not appear in the goal. Supply it by name: <code>refine hoare_seq (Q := …) ?_ ?_</code>. What is true after <code>x := 3</code> and enough to finish with?',
        'The intermediate assertion should say what you learned and keep what you still own: <code>x</code> is <code>3</code>, and the heap is still empty. Each subgoal is then a single-assignment proof in the style of M6-4.',
        'The second subgoal ends in a conjunction. <code>show</code> it into readable form, <code>constructor</code>, then <code>show</code> each side into the explicit <code>if</code> it unfolds to. Look hard at the first one before you simplify it.',
        'Use <code>hoare_seq</code> with intermediate assertion <code>aAnd (fact (fun σ => σ x = 3)) emp</code>.'
      ],
      sol: "theorem assign_twice (x y : Var) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := by\n  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_\n  · intro σ h he\n    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 3 x = 3\n    simp [Store.set]\n  · intro σ h hpre\n    obtain ⟨hx, he⟩ := hpre\n    have hx' : σ x = 3 := hx\n    refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3\n    constructor\n    · show (if x = y then σ x else σ x) = 3\n      simp [hx']\n    · show (if y = y then σ x else σ y) = 3\n      simp [hx']",
      expl: 'Look at the hypothesis list: there is <b>no</b> <code>x ≠ y</code>. You will be tempted to add it and Lean will tell you it is unused. <code>y := x</code> copies the value of <code>x</code>, so even in the aliased case <code>x = y</code> the store still maps both names to <code>3</code>. In the proof this surfaces as the goal <code>(if x = y then σ x else σ x) = 3</code>, whose two branches coincide, so there is nothing for a disequality to decide. The formalisation caught a side condition you assumed you needed.',
      walk: [
        { tac: 'refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_',
          h: 'The whole design decision of the proof, in one line. <code>(Q := …)</code> fixes the implicit intermediate assertion that unification could never find, and the two <code>?_</code> become goals <code>refine_1</code> and <code>refine_2</code>.' },
        { tac: '· intro σ h he',
          h: 'First subgoal: <code>Hoare emp (x := 3) (aAnd (fact (fun σ => σ x = 3)) emp)</code>. That is <code>assign_constant</code> with <code>3</code> for <code>10</code>, so the next three lines are its proof.' },
        { tac: 'refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩',
          h: 'Witness, derivation, hole for the fact, <code>he</code> for the <code>emp</code>.' },
        { tac: 'show Store.set σ x 3 x = 3',
          h: 'Strips <code>fact</code> and the two state projections.' },
        { tac: 'simp [Store.set]',
          h: 'Closes it. First subgoal done.' },
        { tac: '· intro σ h hpre',
          h: 'Second subgoal: <code>Hoare (aAnd (fact (fun σ => σ x = 3)) emp) (y := x) (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp)</code>. This time the precondition is informative, so <code>hpre</code> is something you take apart rather than pass on.' },
        { tac: 'obtain ⟨hx, he⟩ := hpre',
          h: '<code>aAnd</code> is definitionally a conjunction, so <code>obtain</code> splits it with no unfolding.' },
        { tac: "have hx' : σ x = 3 := hx",
          h: 'The <code>show</code> move applied to a hypothesis. <code>hx</code> already proves <code>σ x = 3</code> definitionally, but it is <i>displayed</i> as <code>fact (fun σ => σ x = 3) σ h</code>, and <code>simp [hx]</code> refuses to use it as a rewrite rule in that form. Restating it at the transparent type gives <code>simp</code> something it can fire on.' },
        { tac: 'refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩',
          h: 'The witness store is <code>Store.set σ y (σ x)</code> because <code>(Atom.var x).eval σ</code> reduces to <code>σ x</code>. Note: <code>σ x</code>, not <code>3</code>. The semantics copies whatever is there, and connecting it to <code>3</code> is your job.' },
        { tac: 'show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3',
          h: 'Exposes the conjunction underneath. Both conjuncts are now statements about the post-assignment store.' },
        { tac: 'constructor',
          h: 'Splits <code>A ∧ B</code> into goals <code>left</code> and <code>right</code>.' },
        { tac: '· show (if x = y then σ x else σ x) = 3',
          h: 'The interesting line of the exercise. Unfolding <code>Store.set σ y (σ x)</code> at the point <code>x</code> gives <code>if x = y then σ x else σ x</code> — and <b>both branches are the same</b>. That is the formal content of “you do not need <code>x ≠ y</code>”: in the aliased case <code>y</code> was overwritten with what <code>x</code> held, which is what <code>x</code> holds.' },
        { tac: "simp [hx']",
          h: '<code>simp?</code> reports <code>simp only [hx\', ite_self]</code>. <code>ite_self</code> is <code>(if c then a else a) = a</code>, true for <i>any</i> decidable <code>c</code> — which is exactly why the guard never has to be decided. Then <code>hx\'</code> turns <code>σ x</code> into <code>3</code>.' },
        { tac: '· show (if y = y then σ x else σ y) = 3',
          h: 'The second conjunct, where the guard is <code>y = y</code> and the branches differ.' },
        { tac: "simp [hx']",
          h: 'Same finish, different first step: here <code>simp?</code> reports <code>simp only [↓reduceIte, hx\']</code>. The guard <i>is</i> decided, by evaluating its <code>Decidable</code> instance, and only then does <code>hx\'</code> fire. In the previous branch <code>ite_self</code> meant no decision was ever made.' }
      ],
      deep: [
        { t: 'trace', title: 'assign_twice, the states that matter',
          start: 'x y : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 3) ;; Cmd.assign y (Atom.var x)) (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp)',
          steps: [
            { tac: 'refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_',
              state: 'case refine_1\nx y : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 3)) (aAnd (fact fun σ => σ x = 3) emp)\n\ncase refine_2\nx y : Var\n⊢ Hoare (aAnd (fact fun σ => σ x = 3) emp) (Cmd.assign y (Atom.var x)) (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp)',
              h: 'Two goals, with the assertion you chose appearing as the postcondition of the first and the precondition of the second. That is the entire mechanism of sequencing: your <code>Q</code> is the handshake.' },
            { tac: '· intro σ h he',
              state: "case refine_1\nx y : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign x (Atom.const 3)) { store := σ, heap := h } s' ∧ aAnd (fact fun σ => σ x = 3) emp s'.store s'.heap",
              h: 'Identical in shape to M6-4.' },
            { tac: 'refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩',
              state: 'case refine_1\nx y : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 3) { store := σ.set x 3, heap := h }.store { store := σ.set x 3, heap := h }.heap',
              h: 'The same folded <code>fact</code> goal.' },
            { tac: 'show Store.set σ x 3 x = 3',
              state: 'case refine_1\nx y : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 3 x = 3',
              h: 'Closed by <code>simp [Store.set]</code>. On to the second bullet.' },
            { tac: '· intro σ h hpre',
              state: "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhpre : aAnd (fact fun σ => σ x = 3) emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
              h: 'These <code>σ</code> and <code>h</code> are <i>fresh</i>: the state at the start of the second command, unrelated to the ones in the first bullet. That is what <code>hoare_seq</code> bought — the two halves never mention each other’s states.' },
            { tac: 'obtain ⟨hx, he⟩ := hpre',
              state: "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
              h: '<code>hx</code> arrives folded.' },
            { tac: "have hx' : σ x = 3 := hx",
              state: "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
              h: 'The goal did not move. The context gained <code>hx\'</code>, whose proof term is literally <code>hx</code> — nothing computed, only re-typed at a transparent type.' },
            { tac: 'refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩',
              state: "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ fact (fun σ => σ x = 3 ∧ σ y = 3) { store := σ.set y (σ x), heap := h }.store\n    { store := σ.set y (σ x), heap := h }.heap",
              h: 'The witness store copies <code>σ x</code> into <code>y</code>. Nothing in the goal yet knows that <code>σ x</code> is <code>3</code>.' },
            { tac: 'show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3',
              state: "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ σ.set y (σ x) x = 3 ∧ σ.set y (σ x) y = 3",
              h: 'Readable at last.' },
            { tac: 'constructor',
              state: "case refine_2.left\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ σ.set y (σ x) x = 3\n\ncase refine_2.right\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ σ.set y (σ x) y = 3",
              h: 'Two equations about the same updated store, read at a different variable.' },
            { tac: '· show (if x = y then σ x else σ x) = 3',
              state: "case refine_2.left\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ (if x = y then σ x else σ x) = 3",
              h: 'The goal worth photographing. The <code>if</code> is there because <code>Store.set</code> is defined with one, and both branches are <code>σ x</code> because the value written was read from <code>x</code>. No case analysis is needed, and no disequality could help — there is nothing to distinguish.' },
            { tac: '· show (if y = y then σ x else σ y) = 3',
              state: "case refine_2.right\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ (if y = y then σ x else σ y) = 3",
              h: 'Guard true by reflexivity, and here the branches are <i>not</i> equal, so this conjunct genuinely depends on the assignment having happened.' }
          ],
          done: 'No goals.' },

        { t: 'cmp',
          left: { t: 'The explicit route (the solution)', kind: 'good',
            h: 'Two <code>show</code>s expose the <code>if</code>s. Slower to write, and it forces you to look at <code>(if x = y then σ x else σ x)</code>, which is the only interesting fact in the exercise.',
            src: "· show (if x = y then σ x else σ x) = 3\n  simp [hx']\n· show (if y = y then σ x else σ y) = 3\n  simp [hx']" },
          right: { t: 'The automatic route',
            h: 'Also compiles. <code>simp</code> collapses <code>if c then a else a</code> via <code>ite_self</code> and never shows you that it did. Fine in production, bad the first time: you would finish the exercise without noticing that aliasing had been handled.',
            src: "· simp [Store.set, hx']\n· simp [Store.set, hx']" } },

        { t: 'detail', title: 'What Lean says if you add the hypothesis anyway', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Add <code>(hxy : x ≠ y)</code> to the statement, leave the proof alone, and it still compiles — with a warning:' },
            { t: 'state',
              cap: 'The unused-variable linter doing mathematics for you: it is saying the theorem is stronger than you stated it.',
              src: 'warning: Variable name `hxy` is not explicitly referenced.\n\nThe binding can be removed (if unused) or named `_` (if used implicitly).\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`' },
            { t: 'p', h: 'Treat that as a result, not as noise. Whenever it fires on a hypothesis you added from intuition, the intuition was about a different theorem.' }
          ] },

        { t: 'detail', title: 'Where <code>x ≠ y</code> <i>is</i> genuinely needed', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'The intuition that wanted a disequality was not wrong in general, only about this program. Change the second command from a copy to a second constant — <code>x := 3 ;; y := 5</code> — and the side condition starts carrying weight.' },
            { t: 'code', tag: 'illustration',
              cap: 'All three compile against the M6 prelude. <code>simp [hxy, hx\']</code> in the left branch really does use <code>hxy</code>: remove it and <code>simp</code> stops with <code>⊢ ¬x = y</code> unproved. The third theorem is the one discussed under <b>variants</b> — the two <code>cases</code> compute the final store, after which <code>hq.2</code> reads <code>0 = 3</code>.',
              src: "theorem assign_two_constants (x y : Var) (hxy : x ≠ y) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.const 5))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 5)) emp) := by\n  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_\n  · intro σ h he\n    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 3 x = 3\n    simp [Store.set]\n  · intro σ h hpre\n    obtain ⟨hx, he⟩ := hpre\n    have hx' : σ x = 3 := hx\n    refine ⟨⟨Store.set σ y 5, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ y 5 x = 3 ∧ Store.set σ y 5 y = 5\n    constructor\n    · show (if x = y then 5 else σ x) = 3\n      simp [hxy, hx']\n    · show (if y = y then 5 else σ y) = 5\n      simp\n\n-- and without the hypothesis it is false: instantiate x and y to the same variable\ntheorem not_assign_two_constants :\n    ¬ (∀ (x y : Var), Hoare emp (.assign x (.const 3) ;; .assign y (.const 5))\n        (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 5)) emp)) := by\n  intro hall\n  obtain ⟨s', _, hq, _⟩ := hall 0 0 (fun _ => 0) Heap.empty rfl\n  have h35 : (3 : Nat) = 5 := by rw [← hq.1, ← hq.2]\n  exact absurd h35 (by simp)\n\n-- for contrast: reversing the original program fails for a different reason\ntheorem not_assign_reversed :\n    ¬ (∀ (x y : Var), Hoare emp (.assign y (.var x) ;; .assign x (.const 3))\n        (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp)) := by\n  intro hall\n  obtain ⟨s', hex, hq, _⟩ := hall 0 1 (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | seq h₁ h₂ =>\n      cases h₁\n      cases h₂\n      have h0 : (0 : Nat) = 3 := hq.2\n      exact absurd h0 (by simp)" },
            { t: 'p', h: 'The difference between the two exercises is one goal, and it is the goal the <code>show</code> exposes:' },
            { t: 'cmp',
              left: { t: '<code>x := 3 ;; y := x</code> — no hypothesis needed', kind: 'good',
                h: 'Both branches are the same term. There is nothing for a disequality to decide.',
                src: '⊢ (if x = y then σ x else σ x) = 3' },
              right: { t: '<code>x := 3 ;; y := 5</code> — hypothesis needed',
                h: 'The branches differ, so the <code>if</code> has to be decided. <code>simp [hxy, hx\']</code> runs as <code>simp only [hxy, ↓reduceIte, hx\']</code>: <code>hxy</code> rewrites the guard to <code>False</code>, and only then can the <code>else</code> branch be taken. Drop <code>hxy</code> and <code>simp</code> leaves the residual goal <code>⊢ ¬x = y</code>, which is unprovable — that residue <i>is</i> the side condition.',
                src: '⊢ (if x = y then 5 else σ x) = 3' } },
            { t: 'p', h: 'Read those two displays as the criterion: a side condition is needed exactly when the two branches of the <code>ite</code> that <code>Store.set</code> generates are not the same term.' }
          ] }
      ],
      pitfall: 'Getting the <code>if</code> guard backwards in the <code>show</code>. <code>Store.set σ y v</code> is <code>fun z => if z = y then v else σ z</code>, so applying it at <code>x</code> gives <code>if x = y then …</code> — queried variable on the left, updated one on the right. Write <code>show (if y = x then σ x else σ x) = 3</code> and Lean refuses: <br><code>\'show\' tactic failed, pattern (if y = x then σ x else σ x) = 3 is not definitionally equal to target σ.set y (σ x) x = 3</code>. <br>Equality on <code>Var</code> is symmetric; <code>show</code> compares terms, and <code>x = y</code> is not the term <code>y = x</code>.',
      variants: 'Drop the second assignment and you are back at <code>assign_constant</code>. <br><br>Change the second command to <code>y := 5</code> and the side condition becomes real: <code>x := 3 ;; y := 5</code> needs <code>x ≠ y</code>, because with <code>x = y</code> the postcondition asserts <code>3 = 5</code>. Theorem and refutation are both in the aside above — that is the honest version of the hypothesis you were tempted to add. <br><br>Reverse the program to <code>y := x ;; x := 3</code> and it fails, but <i>not</i> for an aliasing reason, so do not use it as the counterexample. After the copy, <code>y</code> holds the initial value of <code>x</code>, about which <code>emp</code> says nothing; the second assignment then fixes <code>x</code> and leaves <code>y</code> alone. So <code>σ y = 3</code> is unprovable whenever <code>x ≠ y</code> — take <code>x := 0</code>, <code>y := 1</code>, initial store <code>fun _ => 0</code>. In the <i>aliased</i> case the triple is true again, for the trivial reason that there is only one variable. Adding <code>x ≠ y</code> makes that program worse, not better. <br><br>Change the intermediate assertion to <code>fact (fun σ => σ x = 3)</code> without the <code>emp</code> and the first subgoal still goes through, but the second can no longer produce the <code>emp</code> in the final postcondition: <code>he</code> would have nowhere to come from. That is the general rule for intermediate assertions — they must carry forward everything the tail still needs, ownership included.'
    },

    /* ================================================================
       6 — close
       ================================================================ */

    { t: 'sec', s: 'The rule you cannot write yet' },

    { t: 'p', h: 'Every command specified in this chapter leaves the heap exactly as it found it, and <code>hoare_assign</code> exploits that twice over: the witness heap is the heap you were given, and the precondition is <i>computed</i> from the postcondition by <code>subst</code>. Nothing was chosen. Try the same for <code>x := [l]</code>.' },

    { t: 'p', h: 'The final store is <code>Store.set σ x v</code> where <code>v</code> is whatever the heap holds at <code>l</code> — so the precondition has to say two things that no store rule ever had to. That the cell is <i>there</i>, because <code>Exec.load</code> has no derivation otherwise and the existential would be unprovable. And how much of the heap the specification is allowed to mention. There is no composition that answers the second question: the precondition of a load is not determined by its postcondition, and you have to decide.' },

    { t: 'p', h: 'Everything about the logic follows from that decision. Mention the whole heap and you are back in the world of pairwise disequalities that this course opened by rejecting. Mention <code>l ↦ v</code> and nothing else and you get a rule so weak it appears to specify only programs whose entire memory is one cell. M7 makes the second choice, and states the three heap rules in the smallest form that is true.' },

    { t: 'dod', h: 'You can derive program proofs by composing triples, instead of unfolding <code>Exec</code> every time.' }

  ]
});
