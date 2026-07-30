/* M7 — The small-footprint rules
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m7 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm7',
  num: 'M7',
  phase: 'Phase 2 · Program logic',
  title: 'The small-footprint rules',
  blurb: 'Load, write, and free — each specified using only the memory it actually touches.',

  orient: {
    youWill: [
      'State the three rules that touch memory in the smallest form that is true, and prove each of them from <code>Exec</code> in four lines.',
      'Use an exact precondition the way it is meant to be used: as an equation you delete a variable with.',
      'Choose the cut in a <code>∗</code>-postcondition, and watch Lean hand you two false goals when you choose the other one.',
      'Refute the free rule under the loose reading of <code>↦</code>, on a named heap.',
      'Verify a two-command program with no frame rule, and locate the missing theorem exactly.'
    ],
    needs: [
      '<code>Hoare</code> and <code>hoare_seq</code> from M6.',
      'The six-slot unfolding of <code>∗</code> from M4, and <code>pure</code> against <code>fact</code> from M3.',
      '<code>singleton_same</code>, <code>write_singleton</code>, <code>erase_singleton</code> from M1; <code>disjoint_empty_left</code> and <code>union_empty_left</code> from M2. All five appear verbatim in the solutions.',
      'That <code>Exec.load</code>, <code>Exec.write</code> and <code>Exec.free</code> each carry a premise of the form <code>s.heap l = some v</code>.'
    ],
    payoff: 'These are the last <code>Exec</code> derivations you build in order to verify a program. From M9 on, <code>Exec</code> appearing in a proof means a lemma is missing.'
  },

  blocks: [

    /* ================================================================
       1 — making the choice
       ================================================================ */

    { t: 'h3', s: 'Choose the smallest precondition' },

    { t: 'p', h: 'Take the second option. The precondition of <code>x := [l]</code> is <code>l ↦ v</code> — the heap <i>is</i> that one cell — and the same for the write and the free. Three rules, one cell each.' },

    { t: 'txt',
      src: "  { l ↦ v }      x := [l]      { pure (x = v) ∗ l ↦ v }\n  { l ↦ old }    [l] := e      { l ↦ e }\n  { l ↦ v }      free l        { emp }",
      cap: 'The <code>l ↦ e</code> in the second line is an abuse: <code>e</code> is syntax, not a value. Exercise 2 says what Lean makes you write instead.' },

    { t: 'p', h: 'As stated, those rules really do specify nothing but programs whose entire memory is one cell. What rescues them is a second theorem, proved once, that hangs an untouched remainder on both ends of any such triple. Whether you are willing to bet on that theorem is what decides how you write these three, so look at what the other bet costs.' },

    { t: 'cmp',
      left: { t: 'The rule you would write first', kind: 'bad',
        h: 'Talk about the heap the program actually runs in. The precondition says “<code>h</code> holds <code>old</code> at <code>l</code>, and whatever else”; the postcondition then has to describe that whole heap again, updated. Every rule quantifies over an unknown remainder, so every rule has to say something about it.',
        src: "  { fun _ h => h l = some old  ∧  REST h }\n      [l] := e\n  { fun σ h => h l = some (e.eval σ)  ∧  REST' h }" },
      right: { t: 'The small-footprint rule', kind: 'good',
        h: 'The precondition is <code>l ↦ old</code>, which in this development is the <i>equation</i> <code>h = Heap.singleton l old</code>. There is no remainder to mention, so there is nothing to carry and nothing to re-derive.',
        src: "  { l ↦ old }   [l] := e   { l ↦ e }" } },

    { t: 'p', h: 'That remainder is the whole difficulty. Each rule must state how its command acts on it; the statements differ from rule to rule; and each becomes a fresh obligation at every use, discharged again by hand. Small footprints replace those <i>n</i> statements by a single theorem, and pay for it by forbidding a primitive rule to mention anything outside the memory it touches.' },

    { t: 'p', h: 'The free rule is where that discipline stops being a preference. It is false if <code>↦</code> is read as “at least this cell” — a claim you have so far had to take on trust. <code>Hoare</code> now exists, so exercise 3 turns it into a refutation on a named heap.' },

    { t: 'p', h: 'The load rule is the only one of the three whose postcondition has structure, and both halves of that structure are forced. Reading does not consume, so the cell has to come back. The thing you learned lives in the store, so it has to arrive on a conjunct that owns no memory: <code>pure</code>, not <code>fact</code>. Choose <code>fact</code> and the postcondition stops pinning the final heap at all.' },

    { t: 'detail', title: 'What <code>fact</code> on the left of that <code>∗</code> would cost', tag: 'counterexample', open: false,
      blocks: [
        { t: 'p', h: 'A <code>fact</code> conjunct is satisfied by any heap, so it is free to swallow memory that the other conjunct was supposed to account for. A <code>pure</code> conjunct is not.' },
        { t: 'code', tag: 'illustration',
          src: "-- `fact φ ∗ P` lets the left conjunct silently own a cell.\nexample (l : Loc) (v : Val) (σ : Store) :\n    (fact (fun _ => True) ∗ emp) σ (Heap.singleton l v) :=\n  ⟨Heap.singleton l v, Heap.empty, disjoint_empty_right _,\n   (union_empty_right _).symm, trivial, rfl⟩\n\n-- `pure φ ∗ P` does not: the left heap is forced to be empty.\ntheorem star_emp_forces_empty (φ : Store → Prop) (σ : Store) (h : Heap)\n    (hh : (pure φ ∗ emp) σ h) : h = Heap.empty := by\n  obtain ⟨h₁, h₂, _, hu, ⟨_, he₁⟩, he₂⟩ := hh\n  subst he₁; subst he₂\n  rw [hu, union_empty_left]" },
        { t: 'p', h: 'The first example splits a one-cell heap as <code>Heap.singleton l v</code> on the left and <code>Heap.empty</code> on the right, and <code>fact True</code> accepts it. So a postcondition <code>fact φ ∗ (l ↦ v)</code> would say “the final heap contains that cell somewhere”, not “the final heap is that cell” — the loose reading again, smuggled in through the conjunct nobody was watching. <code>star_emp_forces_empty</code> is used again in exercise 1.' }
      ] },

    /* ================================================================
       2 — the mechanics all three proofs share
       ================================================================ */

    { t: 'h3', s: 'An exact precondition is an equation' },

    { t: 'p', h: '<code>hp : (l ↦ v) σ h</code> becomes <code>h = Heap.singleton l v</code> after one δ-step and two β-steps, and <code>subst</code> looks through both. So the second line of every tactic proof below is <code>subst hp</code>, and after it <code>h</code> no longer exists: every heap in the goal is the literal <code>Heap.singleton l v</code>. That is the mechanical dividend of exactness. A precondition that merely constrained the heap would leave <code>h</code> standing, and every step afterwards would have to reason about it instead of computing with it.' },

    { t: 'detail', title: 'When <code>subst</code> refuses', tag: 'tactic', open: false,
      blocks: [
        { t: 'p', h: '<code>subst</code> needs a bare local variable on one side of the equation and needs it to not occur on the other. Both hold here: <code>h</code> is a variable introduced by <code>intro</code>, and <code>Heap.singleton l v</code> does not mention it. When either fails — the side to eliminate is a compound term, or the variable occurs on both sides — the fallback is <code>cases hp</code>, which matches on <code>Eq.refl</code> and performs the same replacement, leaving the goal under a harmless <code>case refl</code>.' }
      ] },

    { t: 'tbl',
      head: ['Rule', 'Final state you must name', 'Premise of the constructor', 'Postcondition'],
      rows: [
        ['<code>.load x l</code>', '<code>⟨Store.set σ x v, Heap.singleton l v⟩</code>', '<code>singleton_same l v</code>', 'a cut, then <code>Store.set σ x v x = v</code>'],
        ['<code>.write l e</code>', '<code>⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩</code>', '<code>singleton_same l old</code>', '<code>write_singleton</code>'],
        ['<code>.free l</code>', '<code>⟨σ, Heap.erase (Heap.singleton l v) l⟩</code>', '<code>singleton_same l v</code>', '<code>erase_singleton</code>']
      ],
      cap: 'The middle column is read off the <code>Exec</code> constructor: the load sets the store and keeps the heap; the other two keep the store and change the heap.' },

    { t: 'p', h: 'One lemma discharges all three premises, because after <code>subst</code> the cell whose existence <code>Exec</code> demands is exactly the cell the precondition named. Two of the three postconditions are a single M1 citation. Everything else in those two proofs is the anonymous constructor doing bookkeeping, which is why they are five lines and introduce no new tactic.' },

    { t: 'note', kind: 'key', title: 'The layering rule',
      h: 'The write and free rules <i>are</i> <code>write_singleton</code> and <code>erase_singleton</code>, wrapped. If you find yourself writing <code>funext</code> inside a Hoare proof, you are proving a heap lemma in the wrong place: name it, prove it where the other ten live, and cite it. That separation is what keeps the program logic short — and it is the reason M1 looked like a list of trivialities.' },

    { t: 'detail', title: 'The premise is about a projection, so <code>rw</code> cannot see it', tag: 'error', open: false,
      blocks: [
        { t: 'p', h: '<code>Exec.load</code> asks for <code>s.heap l = some v</code> where <code>s</code> is the literal <code>⟨σ, Heap.singleton l v⟩</code>. Handing it <code>singleton_same l v</code> works with nothing in between. Reaching for the same lemma as a rewrite does not:' },
        { t: 'state',
          src: "error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  Heap.singleton ?l ?v ?l\nin the target expression\n  { store := σ, heap := Heap.singleton l v }.heap l = some v\n\nσ : Store\nl : Loc\nv : Val\n⊢ { store := σ, heap := Heap.singleton l v }.heap l = some v",
          cap: '`rw [singleton_same]` on a goal that `exact singleton_same l v` closes without complaint. The pattern is present up to reduction and absent from the syntax.' }
      ] },

    /* ================================================================
       3 — the three rules
       ================================================================ */

    { t: 'sec', s: 'Exercises · the three rules' },

    { t: 'ex',
      id: 'm7-1',
      name: 'hoare_load',
      hard: false,

      why: 'In a <code>∗</code>-goal <i>you</i> supply the cut, and here the cut is not a matter of taste. Reading is not destructive, so the cell must come back; the fact you learned owns nothing, so it must arrive on the empty half. Exactly one split satisfies both, and Lean will show you two false goals if you pick the other.',
      setup: 'You will need <code>singleton_same</code>, <code>disjoint_empty_left</code> and <code>union_empty_left</code>.',
      goal: "theorem hoare_load (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (.load x l)\n      (pure (fun σ => σ x = v) ∗ (l ↦ v))",

      hints: [
        'Open and eliminate: <code>intro σ h hp</code>, <code>subst hp</code>. What is left is one nested tuple.',
        'A load writes the store and leaves the heap alone, so the witness state is <code>⟨Store.set σ x v, Heap.singleton l v⟩</code>, and <code>Exec.load</code> wants <code>singleton_same l v</code> on the nose.',
        'For the <code>∗</code>, ask what the left heap is <i>allowed</i> to be. <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, and the <code>emp</code> pins its heap to <code>Heap.empty</code>. So <code>h₁ := Heap.empty</code> and <code>h₂ := Heap.singleton l v</code>.',
        '<code>refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩</code> leaves one goal, about the store. It displays with <code>fact</code> at the head, so <code>show Store.set σ x v x = v</code> and then <code>simp [Store.set]</code>.'
      ],

      sol: "theorem hoare_load (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l)) (pure (fun σ => σ x = v) ∗ (l ↦ v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩\n  refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩\n  show Store.set σ x v x = v\n  simp [Store.set]",

      expl: 'The whole proof is choosing the cut. The <code>pure</code> conjunct must own the empty heap, so the split is forced. Then <code>disjoint_empty_left</code> and <code>(union_empty_left _).symm</code> discharge the two heap obligations, and one <code>simp</code> finishes the store equation.',

      walk: [
        { tac: 'intro σ h hp',
          h: 'Takes the two quantified components of the state and the precondition. The goal becomes the existential.' },
        { tac: 'subst hp',
          h: 'Eliminates <code>h</code>. From here there is one concrete heap in the problem.' },
        { tac: 'refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩',
          h: 'The inner <code>⟨…⟩</code> is the final <code>State</code>: <code>x</code> now holds <code>v</code>, the heap untouched. The second component is the derivation, whose premise is <code>singleton_same l v</code>. The <code>?_</code> defers the postcondition.' },
        { tac: 'refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩',
          h: 'The cut, in the six-slot order. The <code>.symm</code> is there because <code>union_empty_left</code> reads <code>Heap.union Heap.empty h = h</code> and slot 4 wants it reversed. The nested <code>⟨?_, rfl⟩</code> is <code>pure</code> split into its <code>fact</code> half, deferred, and its <code>emp</code> half — <code>rfl</code>, because the left heap literally is <code>Heap.empty</code>. The last <code>rfl</code> is <code>l ↦ v</code> at the right heap, for the same reason.' },
        { tac: 'show Store.set σ x v x = v',
          h: 'The remaining goal is that equation, but folded behind <code>fact</code> and an unreduced projection. <code>show</code> unfolds both in the display, which is all that was blocking <code>simp</code>.' },
        { tac: 'simp [Store.set]',
          h: 'Unfolds <code>Store.set</code> and decides the <code>if</code>. There is no <code>Store.set_same</code> to cite.' }
      ],

      deep: [
        { t: 'trace', title: 'hoare_load, tactic by tactic',
          start: "x : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.load x l) ((_root_.pure fun σ => σ x = v) ∗ l ↦ v)",
          steps: [
            { tac: 'intro σ h hp',
              state: "x : Var\nl : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.load x l) { store := σ, heap := h } s' ∧ ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) s'.store s'.heap",
              h: '<code>_root_.pure</code> is the printer disambiguating this <code>pure</code> from <code>Pure.pure</code>. Same function.' },
            { tac: 'subst hp',
              state: "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.load x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) s'.store s'.heap",
              h: 'Two hypotheses lighter and one heap more concrete.' },
            { tac: 'refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩',
              state: "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store\n    { store := σ.set x v, heap := Heap.singleton l v }.heap",
              h: 'Only the postcondition is left, applied to the two projections of the state you just named.' },
            { tac: 'refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩',
              state: "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store Heap.empty",
              h: 'Five of six slots supplied outright. Notice the heap argument: <code>Heap.empty</code>. The cut is already committed to.' },
            { tac: 'show Store.set σ x v x = v',
              state: "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ σ.set x v x = v",
              h: 'Readable.' },
            { tac: 'simp [Store.set]', state: 'No goals.', h: '' }
          ],
          done: 'No goals.' },

        { t: 'p', h: 'Where do the six slots come from? Supply none of them and Lean shows you the skeleton, with the two heaps as metavariables the later goals refer to:' },

        { t: 'state',
          src: "case refine_1\n⊢ Heap\n\ncase refine_2\n⊢ Heap\n\ncase refine_3\n⊢ Heap.disjoint ?refine_1 ?refine_2\n\ncase refine_4\n⊢ { store := σ.set x v, heap := Heap.singleton l v }.heap = Heap.union ?refine_1 ?refine_2\n\ncase refine_5\n⊢ _root_.pure (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store ?refine_1\n\ncase refine_6\n⊢ (l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store ?refine_2",
          cap: '`refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩`, hypotheses elided. The first two goals are literally “produce a heap”; the last four constrain the choice.' },

        { t: 'cmp',
          left: { t: 'The forced cut', kind: 'good',
            h: 'Slot 5 becomes <code>pure φ … Heap.empty</code>, whose <code>emp</code> half is <code>rfl</code>; slot 6 becomes <code>(l ↦ v) … (Heap.singleton l v)</code>, also <code>rfl</code>. Only the store fact survives.',
            src: "refine ⟨Heap.empty, Heap.singleton l v,\n        disjoint_empty_left _, (union_empty_left _).symm,\n        ⟨?_, rfl⟩, rfl⟩" },
          right: { t: 'The other cut', kind: 'bad',
            h: 'Swap the heaps. Slots 3 and 4 still go through — the mirror lemmas are just as available — so nothing complains until the conjuncts land. Leave all three as holes and Lean shows the damage.',
            src: "refine ⟨Heap.singleton l v, Heap.empty,\n        disjoint_empty_right _, (union_empty_right _).symm,\n        ⟨?_, ?_⟩, ?_⟩" } },

        { t: 'state',
          src: "case refine_1\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store (Heap.singleton l v)\n\ncase refine_2\n⊢ emp { store := σ.set x v, heap := Heap.singleton l v }.store (Heap.singleton l v)\n\ncase refine_3\n⊢ (l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store Heap.empty",
          cap: 'The swapped cut, hypotheses elided. Goal 1 is fine — `fact` ignores its heap. Goal 2 asks for `Heap.singleton l v = Heap.empty` and goal 3 for `Heap.empty = Heap.singleton l v`. Both are refutable, and they are the two contradictions the counterexamples below turn on.' },

        { t: 'detail', title: 'Two ways to break the load rule', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'You cannot drop the cell from the postcondition. The load leaves the heap alone, so the final heap is still a singleton and cannot satisfy anything ending in <code>emp</code>. This cites <code>star_emp_forces_empty</code> from the aside above; both must be in scope.' },
            { t: 'code', tag: 'illustration',
              src: "theorem load_must_return_the_cell (x : Var) (l : Loc) (v : Val) :\n    ¬ Hoare (l ↦ v) (.load x l) (pure (fun σ => σ x = v) ∗ emp) := by\n  intro hbad\n  obtain ⟨s', hex, hq⟩ := hbad (fun _ => 0) (Heap.singleton l v) rfl\n  cases hex with\n  | load hl =>\n      have hempty : Heap.singleton l v = Heap.empty := star_emp_forces_empty _ _ _ hq\n      have h1 : Heap.singleton l v l = Heap.empty l := by rw [hempty]\n      rw [singleton_same] at h1\n      exact absurd h1 (by simp [Heap.empty])" },
            { t: 'p', h: 'And you cannot weaken the precondition to <code>emp</code>. That failure is of a different kind: the command <i>faults</i>, and the existential in <code>Hoare</code> is what forbids it. The postcondition plays no part, which is why it is an arbitrary <code>Q</code>.' },
            { t: 'code', tag: 'illustration',
              src: "theorem load_from_emp_impossible (x : Var) (l : Loc) (Q : Assertion) :\n    ¬ Hoare emp (.load x l) Q := by\n  intro hbad\n  obtain ⟨s', hex, _⟩ := hbad (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | load hl =>\n      have hne : Heap.empty l = some _ := hl\n      exact absurd hne (by simp [Heap.empty])" },
            { t: 'p', h: 'Only one constructor can conclude <code>Exec (.load x l) _ _</code>, so the single branch hands you its premise — and the premise is the contradiction.' }
          ] }
      ],

      pitfall: 'Dropping the <code>show</code>. <code>simp [Store.set]</code> alone leaves <code>fact (fun σ => σ x = v) (σ.set x v) Heap.empty</code> and warns you that the <code>Store.set</code> argument went unused — a good sign that it never reached the store. <code>fact</code> is a plain <code>def</code>, not a simp lemma, so <code>simp</code> reduces the projections and stops. Putting <code>fact</code> in the simp set also works and is worse: it hides the step that matters.',

      variants: '<b>Swap the conjuncts.</b> <code>(l ↦ v) ∗ pure (fun σ => σ x = v)</code> is equally provable by the mirror cut <code>⟨Heap.singleton l v, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, rfl, ⟨?_, rfl⟩⟩</code>, and the proof is the same length. <b>Weaken <code>pure</code> to <code>fact</code>.</b> Still provable, and strictly weaker: the aside above shows why the postcondition then stops pinning the final heap, at which point the rule is no longer small-footprint. <b>Drop the cell.</b> False; the load does not change the heap. <b>Weaken the precondition to <code>emp</code>.</b> False for the unrelated reason that the command faults. Both refutations are above.'
    },

    { t: 'ex',
      id: 'm7-2',
      name: 'hoare_write',
      hard: false,

      why: 'The value stored is <code>e</code> evaluated in the store, so the postcondition cannot be a bare <code>↦</code> — it has to be a lambda that reads the store it is handed. Getting comfortable with that shape now costs one exercise; meeting it for the first time in the middle of a program proof costs an afternoon.',
      setup: '<code>singleton_same</code> for the premise, <code>write_singleton</code> for the postcondition.',
      goal: "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) (.write l e)\n      (fun σ h => (l ↦ (e.eval σ)) σ h)",

      hints: [
        'Open and eliminate, as before. The only heap left in sight is <code>Heap.singleton l old</code>.',
        'Read the final state off <code>Exec.write</code>: it keeps the store and produces <code>Heap.write s.heap l (e.eval s.store)</code>, which here is <code>⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩</code>.',
        'The premise is about the value that is <i>already</i> there — the cell must exist before you overwrite it. So <code>singleton_same l old</code>, not <code>singleton_same l (e.eval σ)</code>.',
        'What is left is <code>Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l (e.eval σ)</code>, which is <code>write_singleton l old (e.eval σ)</code>. All three components are now terms, so the whole thing is one <code>exact ⟨…, …, …⟩</code>.'
      ],

      sol: "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,\n         Exec.write (singleton_same l old),\n         write_singleton l old (e.eval σ)⟩",

      expl: 'If you proved <code>write_singleton</code> in M1, this is one application. If you did not, you are now doing <code>funext</code> and a case split inside a Hoare proof — the layering violation this chapter is arranged to prevent.',

      walk: [
        { tac: 'intro σ h hp', h: 'Opens the triple.' },
        { tac: 'subst hp', h: 'Replaces <code>h</code> by <code>Heap.singleton l old</code> and clears both names.' },
        { tac: 'exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,',
          h: 'The final state. The store is unchanged; the heap is the singleton with <code>l</code> overwritten by the value of <code>e</code> in <code>σ</code>. It must be spelled exactly as <code>Exec.write</code> produces it, or the next component will not typecheck against it.' },
        { tac: 'Exec.write (singleton_same l old),',
          h: 'The derivation. Its argument is the premise “<code>l</code> already holds something”, and that something is <code>old</code> — the value in the precondition, not the one being written.' },
        { tac: 'write_singleton l old (e.eval σ)⟩',
          h: 'The postcondition, which after reduction is the M1 equation. One lemma, three arguments, no tactic.' }
      ],

      deep: [
        { t: 'trace', title: 'hoare_write, tactic by tactic',
          start: "l : Loc\ne : Atom\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l e) fun σ h => (l ↦ Atom.eval σ e) σ h",
          steps: [
            { tac: 'intro σ h hp',
              state: "l : Loc\ne : Atom\nold : Val\nσ : Store\nh : Heap\nhp : (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap",
              h: 'The postcondition arrives as an unapplied lambda, and stays one until something needs it applied.' },
            { tac: 'subst hp',
              state: "l : Loc\ne : Atom\nold : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old } s' ∧\n      (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap",
              h: '' },
            { tac: 'refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩, ?_, ?_⟩',
              state: "case refine_1\n⊢ Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old }\n    { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }\n\ncase refine_2\n⊢ (fun σ h => (l ↦ Atom.eval σ e) σ h) { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.store\n    { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.heap",
              h: 'Not what the solution does — it supplies both at once — but this is how you find out what you owe. Goal 1 is <code>Exec.write (singleton_same l old)</code>; goal 2 reduces to the M1 equation. Hypotheses elided.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'Why the postcondition is a lambda', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: '<code>e</code> is an <code>Atom</code>, so “<code>l</code> points to <code>e</code>” is not well typed. What is meant is “<code>l</code> points to the value of <code>e</code>”, and that value depends on the store. An <code>Assertion</code> is a function of a store, so the only way to say it is to bind the store and read it: <code>fun σ h => (l ↦ (e.eval σ)) σ h</code>.' },
            { t: 'p', h: 'When <code>e</code> is a constant the dependence is vacuous and the lambda collapses — that is what makes the next exercise a one-liner. When <code>e</code> mentions a variable it does not, and no constant postcondition exists:' },
            { t: 'code', tag: 'illustration',
              src: "theorem copyVar_spec (x : Var) (l : Loc) (old : Val) :\n    Hoare (l ↦ old) (.write l (.var x)) (fun σ h => (l ↦ σ x) σ h) :=\n  hoare_write l (.var x) old" },
            { t: 'p', h: 'The lambda is awkward to feed to the next rule in a sequence, since the next rule wants to match a plain <code>↦</code>. M9 fixes that by naming the value in the precondition instead, and paying for it with a hypothesis that <code>e</code> evaluates to that value.' }
          ] },

        { t: 'detail', title: 'The wrong premise, and what Lean says', tag: 'error', open: false,
          blocks: [
            { t: 'p', h: 'Supply <code>singleton_same l (e.eval σ)</code> — the value being written — instead of <code>singleton_same l old</code>:' },
            { t: 'state',
              src: "error: Application type mismatch: The argument\n  singleton_same l (Atom.eval σ e)\nhas type\n  Heap.singleton l (Atom.eval σ e) l = some (Atom.eval σ e)\nbut is expected to have type\n  { store := σ, heap := Heap.singleton l old }.heap l = some ?m.23\nin the application\n  Exec.write (singleton_same l (Atom.eval σ e))" },
            { t: 'p', h: 'The constructor asked about the heap <i>before</i> the write and you described the heap after. The <code>?m.23</code> is <code>Exec.write</code>’s implicit <code>old</code>, which Lean was willing to infer from your argument — and then the heaps disagreed.' }
          ] }
      ],

      pitfall: 'Proving the heap equation inline. If you skipped <code>write_singleton</code> in M1, the reflex is <code>funext x; by_cases hx : x = l</code> right here, and it works — leaving a proof about the operational semantics with a proof about partial functions embedded in it, ready to be embedded again in the next one. The other reflex, <code>simp</code> on the postcondition, does nothing: <code>Heap.write</code> and <code>Heap.singleton</code> are ordinary <code>def</code>s, and naming them in the bracket puts you back in the <code>funext</code> proof with extra steps.',

      variants: '<b>Weaken the precondition to <code>emp</code>.</b> False, operationally: <code>Exec.write</code> requires <code>s.heap l = some old</code>, so writing to a cell you do not own is a fault. The refutation is <code>load_from_emp_impossible</code> with <code>write</code> substituted throughout — same six lines, same contradiction out of the premise, and again an arbitrary <code>Q</code>. <b>Fix the postcondition to <code>l ↦ 0</code>.</b> False as soon as <code>e</code> is <code>.var x</code> and the store sends <code>x</code> elsewhere. <b>Drop <code>old</code>.</b> You cannot: it is the witness that the cell exists, and it is the only thing the precondition can say, because the write does not care what was there. That indifference is why <code>write_singleton</code> is stated with two unrelated values.'
    },

    { t: 'ex',
      id: 'm7-3',
      name: 'hoare_free',
      hard: false,

      why: 'Mechanically this is the previous exercise with <code>erase</code> for <code>write</code>, and you should finish it by editing three words. It earns its place because it is the rule that is <b>false</b> under any inexact reading of <code>↦</code> — the claim this course has been making since the first chapter, refuted here for the first time by machine.',
      setup: '<code>singleton_same</code> for the premise of <code>Exec.free</code>, <code>erase_singleton</code> for the postcondition.',
      goal: "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) (.free l) emp",

      hints: [
        'Copy the shape of <code>hoare_write</code> and change three words.',
        '<code>Exec.free</code> keeps the store and erases from the heap, so the final state is <code>⟨σ, Heap.erase (Heap.singleton l v) l⟩</code> and the premise is again <code>singleton_same l v</code>.',
        '<code>emp</code> is <code>fun _ h => h = Heap.empty</code>, so what you owe is <code>Heap.erase (Heap.singleton l v) l = Heap.empty</code>. Supply <code>erase_singleton l v</code> with <code>exact</code>; do not try to rewrite with it.'
      ],

      sol: "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) ((.free l)) (emp) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,\n         Exec.free (singleton_same l v),\n         erase_singleton l v⟩",

      expl: 'Three lines, and all the mathematics is in <code>erase_singleton : Heap.erase (Heap.singleton l v) l = Heap.empty</code>. Under an exact <code>↦</code> that equation is available and the rule is trivial. Under a loose one there is no such equation and the rule is false.',

      walk: [
        { tac: 'intro σ h hp', h: 'Opens the triple.' },
        { tac: 'subst hp', h: 'Replaces <code>h</code> by <code>Heap.singleton l v</code> and clears the variable.' },
        { tac: 'exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,',
          h: 'The final state: same store, heap with <code>l</code> removed, spelled as <code>Exec.free</code> produces it.' },
        { tac: 'Exec.free (singleton_same l v),',
          h: 'You may not free a cell you do not own, and this argument is where you prove you own it.' },
        { tac: 'erase_singleton l v⟩',
          h: 'The postcondition. <code>emp s\'.store s\'.heap</code> reduces to the heap equation, which is this lemma at its two arguments.' }
      ],

      deep: [
        { t: 'trace', title: 'hoare_free, tactic by tactic',
          start: "l : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.free l) emp",
          steps: [
            { tac: 'intro σ h hp',
              state: "l : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := h } s' ∧ emp s'.store s'.heap",
              h: '' },
            { tac: 'subst hp',
              state: "l : Loc\nv : Val\nσ : Store\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } s' ∧ emp s'.store s'.heap",
              h: '' },
            { tac: 'refine ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_⟩',
              state: "case refine_1\n⊢ Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } { store := σ, heap := (Heap.singleton l v).erase l }\n\ncase refine_2\n⊢ emp { store := σ, heap := (Heap.singleton l v).erase l }.store\n    { store := σ, heap := (Heap.singleton l v).erase l }.heap",
              h: 'The two components of the <code>exact</code>, separated. Hypotheses elided. Goal 2 <i>is</i> <code>erase_singleton l v</code> once the projection reduces, which is why the lemma goes in with no massaging.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'The refutation: the free rule under a loose <code>↦</code>', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'Replace the exact <code>↦</code> by the “at least this cell” reading and the rule you just proved becomes false:' },
            { t: 'code', tag: 'illustration',
              src: "def pointsToLoose (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v\n\ntheorem loose_free_unsound :\n    ¬ Hoare (pointsToLoose 0 0) (.free 0) emp := by\n  intro hbad\n  obtain ⟨s', hex, hemp⟩ := hbad (fun _ => 0) (fun _ => some 0) rfl\n  cases hex with\n  | free hl =>\n      have he : Heap.erase (fun _ => some 0) 0 = Heap.empty := hemp\n      have h1 : Heap.erase (fun _ => some 0) 0 1 = Heap.empty 1 := by rw [he]\n      rw [erase_other _ 0 1 (by simp)] at h1\n      exact absurd h1 (by simp [Heap.empty])" },
            { t: 'p', h: 'The witness is <code>fun _ => some 0</code>, the heap in which every location holds <code>0</code>. It satisfies the loose precondition at location <code>0</code>. <code>free 0</code> erases location <code>0</code> and nothing else, so location <code>1</code> still holds <code>some 0</code>, and <code>emp</code> is false. Exactness is what makes “the heap afterwards” a <i>function of</i> “the heap beforehand”. Loosely read, <code>free</code> would have to be told what the rest of the heap was — and so the rule would have to mention it.' },
            { t: 'p', h: 'The <code>have he : … := hemp</code> is the ascription trick: <code>hemp</code>’s type is <code>emp {…}.store {…}.heap</code>, which is the equation definitionally and not syntactically, and the <code>rw</code> on the next line needs the syntax.' }
          ] }
      ],

      pitfall: 'Reaching for <code>rw [erase_singleton]</code> instead of <code>exact erase_singleton l v</code>. It half works: <code>rw</code> rewrites inside the state and leaves <code>⊢ emp { store := σ, heap := Heap.empty }.store { store := σ, heap := Heap.empty }.heap</code> unsolved, because the trailing <code>rfl</code> does not unfold <code>emp</code>. A bare <code>rfl</code> on the next line rescues it, but the direct <code>exact</code> was always available. <code>simp [emp]</code> has the same flavour — it turns the goal into the equation you could have supplied.',

      variants: '<b>Make <code>↦</code> inexact.</b> The rule becomes false; <code>loose_free_unsound</code> above is the whole argument, and it is the most important “what breaks” in the chapter. <b>Weaken the precondition to <code>emp</code>.</b> False — <code>Exec.free</code> demands the cell. <b>Strengthen the postcondition to <code>l ↦ v</code>.</b> False, obviously: the cell is gone. Worth writing down anyway, because the corresponding claim for <code>load</code> is <i>true</i>, and that asymmetry is the substructural character of the logic showing through in the one place you can point at it. <b>Free twice.</b> <code>.free l ;; .free l</code> has no triple from <code>l ↦ v</code>: the second <code>Exec.free</code> cannot find the cell. Nothing in this language puts one back until M14.'
    },

    /* ================================================================
       4 — two programs
       ================================================================ */

    { t: 'sec', s: 'Exercises · two programs' },

    { t: 'ex',
      id: 'm7-4',
      name: 'clearCell_spec',
      hard: false,

      why: 'Your first specification of a <i>named program</i> rather than a bare command, and a free lesson in what Lean identifies without being asked. Three separate reductions happen silently between the general write rule and this statement. Had any one of them not, you would need <code>hoare_consequence</code> here and the proof would be five lines instead of one.',
      setup: '<code>hoare_write</code> and nothing else. The proof is a term.',
      goal: "def clearCell (l : Loc) : Cmd := .write l (.const 0)\n\ntheorem clearCell_spec (l : Loc) (old : Val) :\n    Hoare (l ↦ old) (clearCell l) (l ↦ 0)",

      hints: [
        'You do not need <code>by</code>. <code>hoare_write</code> already has the right shape; the only question is what to instantiate it at.',
        'The instance is <code>e := .const 0</code>. Write <code>hoare_write l (.const 0) old</code> and see whether Lean complains.',
        'It does not. If you want to know why, ask directly: <code>example (σ : Store) : (Atom.const 0).eval σ = 0 := rfl</code> and <code>example (l : Loc) : (fun σ h => (l ↦ ((Atom.const 0).eval σ)) σ h) = (l ↦ (0 : Val)) := rfl</code> both compile.'
      ],

      sol: "def clearCell (l : Loc) : Cmd := .write l (.const 0)\n\ntheorem clearCell_spec (l : Loc) (old : Val) : Hoare (l ↦ old) ((clearCell l)) (l ↦ 0) :=\n  hoare_write l (.const 0) old",

      expl: '<code>(Atom.const 0).eval σ</code> reduces to <code>0</code> definitionally, so the specialised postcondition matches on the nose and no <code>hoare_consequence</code> is needed.',

      walk: [
        { tac: 'def clearCell (l : Loc) : Cmd := .write l (.const 0)',
          h: 'The program. Naming it is the point: from here you can state and reuse a specification without re-mentioning the body.' },
        { tac: ':=',
          h: 'No <code>by</code>. A proof that is one application is better as a term — no goal state to inspect, no tactic to fail, and the elaborator reports any mismatch directly.' },
        { tac: 'hoare_write l (.const 0) old',
          h: 'The general rule at <code>e := .const 0</code>. Its type is <code>Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h</code>, which is <i>not</i> the stated goal syntactically. Lean accepts it because the two are definitionally equal, by three separate reductions.' }
      ],

      deep: [
        { t: 'steps', title: 'The three silent identifications',
          items: [
            { k: 'δ — unfold the def',
              h: [
                { t: 'p', h: '<code>clearCell l</code> is a defined constant, and unfolding it gives <code>Cmd.write l (Atom.const 0)</code>. Uncontroversial — but not free in every proof assistant, and <code>rw</code> would not have done it for you.' },
                { t: 'code', tag: 'illustration', src: "example (l : Loc) : clearCell l = Cmd.write l (.const 0) := rfl" }
              ] },
            { k: 'ι — evaluate the match',
              h: [
                { t: 'p', h: '<code>Atom.eval</code> is defined by pattern matching. At a literal constructor it selects a branch and returns <code>0</code>. At a <i>variable</i> <code>e</code> it is stuck, which is why the general rule has to keep the lambda.' },
                { t: 'code', tag: 'illustration', src: "example (σ : Store) : (Atom.const 0).eval σ = 0 := rfl" }
              ] },
            { k: 'η — collapse the lambda',
              h: [
                { t: 'p', h: 'The postcondition is now <code>fun σ h => (l ↦ 0) σ h</code> and the goal wants <code>l ↦ 0</code>. Eta is part of definitional equality in Lean 4, so there is nothing to invoke. Without it you would need <code>funext</code> twice and this exercise would be a genuine proof.' },
                { t: 'code', tag: 'illustration',
                  src: "example (l : Loc) :\n    (fun σ h => (l ↦ ((Atom.const 0).eval σ)) σ h) = (l ↦ (0 : Val)) := rfl" }
              ] }
          ] },

        { t: 'p', h: 'You can watch the elaborator hold off. <code>#check fun (l : Loc) (old : Val) => hoare_write l (.const 0) old</code> prints the type before any of the three reductions:' },

        { t: 'state',
          src: "fun l old =>\n  hoare_write l (Atom.const 0)\n    old : ∀ (l : Loc) (old : Val),\n  Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h",
          cap: 'Against the goal `Hoare (l ↦ old) (clearCell l) (l ↦ 0)`: three differences, all of them definitional.' }
      ],

      pitfall: 'Dropping into <code>by</code> and opening the definitions by hand. <code>rw [clearCell]</code> and <code>simp [clearCell]</code> both work and both leave you at <code>⊢ Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) (l ↦ 0)</code>, no closer to anything. Push to the next reduction and it stops: <code>rw [Atom.eval]</code> fails with <code>Failed to rewrite using equation theorems for &#39;Atom.eval&#39;</code>, because a function defined by pattern matching compiles to a matcher with no single equation. The habit worth forming: when you suspect two statements are definitionally equal, do not guess and do not fight the tactic — ask with <code>example : A = B := rfl</code>. If it compiles you can use one where the other is expected. If it does not, you genuinely need <code>hoare_consequence</code>.',

      variants: '<b>Use a store-dependent atom.</b> Replace <code>.const 0</code> by <code>.var x</code>: the ι-step disappears, the η-step has nothing to collapse, and the best postcondition available is <code>fun σ h => (l ↦ σ x) σ h</code> — <code>copyVar_spec</code> in the previous exercise’s notes. <b>Change the postcondition to <code>l ↦ 1</code>.</b> The term stops typechecking, and no amount of <code>rfl</code> helps; you would need a false lemma. <b>Change the precondition to <code>emp</code>.</b> False: <code>clearCell</code> writes, and writing needs the cell. Nothing in this language allocates until M14.'
    },

    { t: 'ex',
      id: 'm7-5',
      name: 'readAndFree_spec',
      hard: false,

      why: 'Read a cell, then give the memory back, keeping only the knowledge: the postcondition owns nothing and the value survives in a variable. It is also the exercise built to make you want the frame rule. The obvious composition does not typecheck, and finding out exactly why is worth more than the proof.',
      setup: '<code>hoare_seq</code> and the three rules you just proved. You do <b>not</b> have a frame rule.',
      goal: "def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l\n\ntheorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v))",

      hints: [
        'Try the obvious thing first — <code>hoare_seq (hoare_load x l v) (hoare_free l v)</code> — and read the error. The mismatch it reports is the point of the exercise.',
        'Since the triples will not compose, go underneath them: <code>intro σ h hp</code>, <code>subst hp</code>.',
        'Name the final state of the <i>whole program</i>, not of one step: the load sets <code>x</code> to <code>v</code>, the free erases <code>l</code>, giving <code>⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩</code>. Both steps look at the cell before it is freed, so both premises are the same <code>singleton_same l v</code>, and <code>Exec.seq</code> glues the derivations.',
        '<code>pure φ</code> is a conjunction, so once the state is named the goal flattens into three obligations: the execution, the store fact, the heap being empty. <code>refine ⟨⟨…⟩, ?_, ?_, ?_⟩</code> and take them with <code>·</code> bullets. The middle one needs a <code>show</code> first.'
      ],

      sol: "def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l\n\ntheorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩\n  · exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))\n  · show Store.set σ x v x = v\n    simp [Store.set]\n  · exact erase_singleton l v",

      expl: 'Do it once by hand and notice the discomfort. To sequence the two rules you had to abandon them and go back to the operational semantics, because the load’s postcondition <code>pure … ∗ l ↦ v</code> is not the free’s precondition <code>l ↦ v</code>. The closing section says exactly which theorem is missing.',

      walk: [
        { tac: 'intro σ h hp', h: 'Opens the triple.' },
        { tac: 'subst hp', h: 'Replaces <code>h</code> by <code>Heap.singleton l v</code>.' },
        { tac: 'refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩',
          h: 'Names the final state of the two-command program and defers three obligations. Three, not two, because <code>pure φ</code> is a conjunction and the anonymous constructor flattens it into the existential.' },
        { tac: '· exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))',
          h: 'The execution. <code>Exec.seq</code>’s intermediate state is implicit and Lean infers it: <code>⟨Store.set σ x v, Heap.singleton l v⟩</code>, the state after the load. Both premises are the <i>same</i> proof term, because the load did not touch the heap.' },
        { tac: '· show Store.set σ x v x = v',
          h: 'The <code>fact</code> half of <code>pure</code>, made readable.' },
        { tac: 'simp [Store.set]', h: 'Closes it.' },
        { tac: '· exact erase_singleton l v',
          h: 'The <code>emp</code> half. This is the free rule’s content, cited again — and it is the only sense in which this proof reuses <code>hoare_free</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'readAndFree_spec, tactic by tactic',
          start: "x : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (readAndFree x l) (_root_.pure fun σ => σ x = v)",
          steps: [
            { tac: 'intro σ h hp ; subst hp',
              state: "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (readAndFree x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      _root_.pure (fun σ => σ x = v) s'.store s'.heap",
              h: '<code>readAndFree x l</code> is not unfolded in the display. It gets unfolded when <code>Exec.seq</code> is applied, because that constructor’s conclusion has to match <code>Exec (c₁ ;; c₂) _ _</code> and matching reduces the definition.' },
            { tac: 'refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩',
              state: "case refine_1\n⊢ Exec (readAndFree x l) { store := σ, heap := Heap.singleton l v }\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }\n\ncase refine_2\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap\n\ncase refine_3\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
              h: 'Hypotheses elided; they are the same four throughout. Goals 2 and 3 are the two halves of <code>pure</code>.' },
            { tac: '· exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))',
              state: "case refine_2\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap\n\ncase refine_3\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
              h: 'The bullet closed <code>refine_1</code> and handed back the rest. Without bullets the three goals stay in a pile and a stray tactic can act on the wrong one.' },
            { tac: '· show Store.set σ x v x = v',
              state: "case refine_2\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ σ.set x v x = v",
              h: '' },
            { tac: 'simp [Store.set]',
              state: "case refine_3\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
              h: 'The second bullet ends and the display returns to the outer level. One goal left, and it is <code>erase_singleton l v</code>.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'The composition Lean rejects', tag: 'error', open: false,
          blocks: [
            { t: 'p', h: 'Here is what anyone tries first, and the answer:' },
            { t: 'code', tag: 'sketch',
              src: "theorem naive (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=\n  hoare_seq (hoare_load x l v) (hoare_free l v)" },
            { t: 'state',
              src: "error: Application type mismatch: The argument\n  hoare_free l v\nhas type\n  Hoare (l ↦ v) (Cmd.free l) emp\nbut is expected to have type\n  Hoare ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) (Cmd.free l) (_root_.pure fun σ => σ x = v)\nin the application\n  hoare_seq (hoare_load x l v) (hoare_free l v)" },
            { t: 'p', h: '<code>hoare_seq</code>’s intermediate assertion is not yours to pick here: Lean took it from the first argument, so it is the load’s output <code>pure … ∗ l ↦ v</code>, and then demanded a triple for <code>free</code> starting there. What you have starts at <code>l ↦ v</code>. To close the gap you would need a version of <code>hoare_free</code> that carries the extra conjunct along — and there is none.' }
          ] },

        { t: 'detail', title: 'Breaking it two ways', tag: 'counterexample', open: false,
          blocks: [
            { t: 'p', h: 'The postcondition cannot keep the cell, because the program gave it back:' },
            { t: 'code', tag: 'illustration',
              src: "theorem no_cell_in_empty (φ : Store → Prop) (l : Loc) (v : Val) (σ : Store) :\n    ¬ (pure φ ∗ (l ↦ v)) σ Heap.empty := by\n  intro ⟨h₁, h₂, _, hu, ⟨_, he₁⟩, he₂⟩\n  subst he₁; subst he₂\n  rw [union_empty_left] at hu\n  have h1 : Heap.empty l = Heap.singleton l v l := by rw [hu]\n  rw [singleton_same] at h1\n  exact absurd h1 (by simp [Heap.empty])" },
            { t: 'p', h: 'And the two commands do not commute. Reversed, the program faults, so <i>no</i> postcondition is provable — not even <code>aTrue</code>:' },
            { t: 'code', tag: 'illustration',
              src: "theorem free_then_load_faults (x : Var) (l : Loc) (v : Val) :\n    ¬ Hoare (l ↦ v) (.free l ;; .load x l) aTrue := by\n  intro hbad\n  obtain ⟨s', hex, _⟩ := hbad (fun _ => 0) (Heap.singleton l v) rfl\n  cases hex with\n  | seq h1 h2 =>\n      cases h1 with\n      | free hl =>\n          cases h2 with\n          | load hl2 =>\n              have hgone : Heap.erase (Heap.singleton l v) l l = some _ := hl2\n              rw [erase_same] at hgone\n              exact absurd hgone (by simp)" },
            { t: 'p', h: 'Three nested <code>cases</code>, one per constructor in the derivation, and the contradiction falls out of the innermost premise. That is the shape of every “this program faults” argument in the workbook.' }
          ] }
      ],

      pitfall: 'Forgetting the <code>show</code> in the middle bullet and then trusting <code>simp</code>. You get <code>unsolved goals</code> with residue <code>fact (fun σ => σ x = v) (σ.set x v) ((Heap.singleton l v).erase l)</code> and a warning that the <code>Store.set</code> argument was unused. The subtler trap is the count: <b>three</b> holes, not two, because <code>pure φ</code> is <code>aAnd (fact φ) emp</code>. Two holes is also accepted — you then get one goal <code>_root_.pure (fun σ => σ x = v) {…}.store {…}.heap</code> to split by hand. Neither is wrong; what will confuse you is expecting a fixed number of holes. The anonymous constructor takes as many as you give it and nests the rest.',

      variants: '<b>Reverse the commands.</b> <code>.free l ;; .load x l</code> admits no triple at all from <code>l ↦ v</code>. Proved above. <b>Keep the cell in the postcondition.</b> <code>pure (fun σ => σ x = v) ∗ (l ↦ v)</code> is false — the final heap is empty and cannot be split so that one part is a singleton. Also proved above. <b>Drop the pure fact.</b> <code>Hoare (l ↦ v) (readAndFree x l) emp</code> is true and easier; the point of keeping the fact is that it is the only trace of the data that survives, and it costs no memory. <b>Change the precondition to <code>l ↦ w</code> and leave the postcondition saying <code>σ x = v</code>.</b> False whenever <code>w ≠ v</code>, and the failure is not operational — the program runs fine, it just leaves <code>w</code> in <code>x</code>. The <code>v</code> in the postcondition is tied to the <code>v</code> in the precondition by the load rule and by nothing else; the command <code>.load x l</code> does not mention a value. Every data-flow fact in this logic travels through an assertion, never through the syntax of the program.'
    },

    /* ================================================================
       5 — close
       ================================================================ */

    { t: 'sec', s: 'The theorem that is missing' },

    { t: 'p', h: 'Three of the five proofs above differ only in nouns. The fourth is one of them instantiated for free. The fifth repeats their work by hand, because there was no way to reuse the rules already proved.' },

    { t: 'p', h: 'You do have a structural rule that changes assertions: <code>hoare_consequence</code>. And <code>pure φ ∗ (l ↦ v) ⊢ l ↦ v</code> really is provable — <code>star_pure_left</code> turns the star into an <code>aAnd</code>, then <code>and_right</code> projects. So the composition <i>can</i> be made to typecheck:' },

    { t: 'code', tag: 'illustration',
      src: "theorem readAndFree_forgetful (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) emp :=\n  hoare_seq (hoare_consequence (entails_refl _) (hoare_load x l v)\n              (entails_trans (star_pure_left _ _) (and_right _ _)))\n            (hoare_free l v)",
      cap: 'Structural rules only, no <code>Exec</code> — and a postcondition with the fact deleted.' },

    { t: 'p', h: 'That is the whole of what consequence can do for you here. It weakens the load’s output until <code>hoare_free</code> fits, and the only way to make <code>pure φ ∗ (l ↦ v)</code> fit is to throw <code>φ</code> away. Consequence can <b>forget</b> a frame; it cannot carry one. What you want instead is a rule that takes a triple and hangs an untouched <code>R</code> on both ends: <code>Hoare P c Q → Hoare (P ∗ R) c (Q ∗ R)</code>. Try to prove it and see where it stops.' },

    { t: 'code', tag: 'sketch',
      src: "example {P Q R : Assertion} {c : Cmd} (hc : Hoare P c Q) : Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hr⟩\n  obtain ⟨s₁, hex₁, hq₁⟩ := hc σ h₁ hp\n  sorry" },

    { t: 'state',
      src: "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhr : R σ h₂\ns₁ : State\nhex₁ : Exec c { store := σ, heap := h₁ } s₁\nhq₁ : Q s₁.store s₁.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
      cap: 'Everything <code>hc</code> can give you, laid next to what the goal wants.' },

    { t: 'p', h: 'Read the last two lines against each other. <code>hex₁</code> runs <code>c</code> in <code>h₁</code>; the goal runs <code>c</code> in <code>h</code>, which is <code>h₁</code> with <code>h₂</code> alongside. Nothing in the context connects the two derivations, and nothing can: <code>Hoare P c Q</code> quantifies over states satisfying <code>P</code>, so it says nothing whatever about a larger heap.' },

    { t: 'p', h: 'There is a second gap in the same display, smaller and just as real. <code>hr</code> holds <code>R</code> at <code>σ</code>, and the goal needs <code>R</code> at <code>s\'.store</code> — so a command that assigns a variable <code>R</code> talks about will break the rule for reasons that have nothing to do with heaps. Neither gap is a fact about triples. Both are facts about <code>Exec</code>: that running a command in a bigger heap does the same thing and leaves the extra part alone, and that a command does not disturb what it was not asked to touch. They have to be proved one command at a time, because they are false for commands that go looking at memory they were not given.' },

    { t: 'dod', h: 'You can state and prove a small-footprint rule for every command that touches memory, and you know exactly which theorem stands between three rules about one cell and three rules about any heap.' }

  ]
});
