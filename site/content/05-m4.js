/* M4 — Separating conjunction
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m4 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm4',
  num: 'M4',
  phase: 'Phase 1 · Semantic foundations',
  title: 'Separating conjunction',
  blurb: 'The connective. Its definition, its laws, and the proof that ∗ makes assertions a commutative monoid.',

  orient: {
    youWill: [
      'Write the definition of <code>∗</code> and name its six components in order, without looking.',
      'Take a star apart in one <code>intro</code> pattern and build one in one <code>exact ⟨…⟩</code>.',
      'Prove that <code>∗</code> is commutative, associative and monotone, has <code>emp</code> as unit, and distributes over <code>∨</code> and <code>∃</code>.',
      'Derive <code>l₁ ≠ l₂</code> from <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂</code>, and read the machine-checked refutation of <code>P ∗ Q ⊢ P</code>.',
      'Prove a normalisation lemma by composing three earlier ones, with no <code>intro</code> and no heap anywhere in the proof.'
    ],
    needs: [
      'M2’s nine laws by name. They are the only heap-level facts any proof below uses.',
      'M3’s <code>emp</code>, <code>↦</code>, <code>fact</code>, <code>pure</code>, <code>entails_refl</code>, <code>entails_trans</code>, and the habit of applying a proved entailment to a store, a heap and a premise.',
      'The anonymous constructor and its automatic flattening. That one piece of syntax carries this entire chapter.'
    ],
    payoff: 'The frame rule of M8 reads <code>Hoare (P ∗ R) c (Q ∗ R)</code>, and its proof is the move you learn here: destructure the precondition into six components, then rebuild the postcondition from six slots. From M9 on, lining a precondition up with a command’s footprint is a chain of <code>entails_trans</code> through <code>star_assoc_left</code>, <code>star_comm</code> and <code>star_mono_right</code> — this chapter’s lemmas, used as an algebra.'
  },

  blocks: [

    /* ================================================================
       1 — the definition
       ================================================================ */

    { t: 'h3', s: 'The connective' },

    { t: 'p', h: '<code>aAnd P Q</code> evaluates both conjuncts at <code>h</code>. One heap appearing in two places is the thing to remove. Give each conjunct a heap of its own, forbid the two from overlapping, and require that together they are exactly the heap you were handed. An assertion is a function of one heap, so the two pieces cannot be parameters — they live inside the definition.' },

    { t: 'code', src: `def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star` },

    { t: 'anat',
      src: `def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star`,
      parts: [
        { m: 'fun σ h =>', h: '<code>σ</code> is handed to both conjuncts. Only <code>h</code> is taken apart.' },
        { m: '∃ h₁ h₂', h: 'The cut is <b>quantified, not supplied</b>. <code>(P ∗ Q) σ h</code> does not say how to split <code>h</code>; it says some split works. So to <i>prove</i> a star you invent a cut, and to <i>use</i> one you are handed a cut you did not choose. Every proof in this chapter is one of those two sentences, or both in a row.' },
        { m: 'Heap.disjoint h₁ h₂', h: 'The two pieces do not overlap. Take this conjunct out and <code>h₁ = h₂ = h</code> becomes a legal cut of <code>h</code>.' },
        { m: 'h = Heap.union h₁ h₂', h: 'The pieces reassemble to exactly <code>h</code>, and the equation points whole-on-the-left — which is why slot 4 keeps wanting a <code>.symm</code> on an M2 lemma stated the other way.' },
        { m: 'P σ h₁ ∧ Q σ h₂', h: 'Each conjunct is evaluated at its own piece. Two copies of <code>h</code> in <code>aAnd</code> have become <code>h₁</code> and <code>h₂</code> here, and that substitution is the entire content of the connective.' },
        { m: 'infixr:55', h: 'Right-associative, so <code>P ∗ (Q ∗ R)</code> prints as <code>P ∗ Q ∗ R</code> while <code>(P ∗ Q) ∗ R</code> keeps its parentheses. In the associativity exercise the two sides of a symmetric statement therefore look nothing alike.' }
      ] },

    { t: 'svg', src: '\n<svg viewBox="0 0 560 150" role="img" aria-label="P and Q versus P star Q">\n  <g class="dg">\n    <text x="12" y="20" class="dg-lab">P ∧ Q — both describe the whole heap</text>\n    <rect x="12" y="30" width="230" height="36" rx="7" class="dg-box"/>\n    <text x="127" y="53" text-anchor="middle" class="dg-t">h</text>\n    <path class="dg-arr thin" d="M40 76 L 40 66"/><text x="46" y="86" class="dg-note">P sees all of h</text>\n    <path class="dg-arr thin" d="M40 106 L 40 96"/><text x="46" y="116" class="dg-note">Q sees all of h</text>\n\n    <text x="308" y="20" class="dg-lab">P ∗ Q — each owns its own piece</text>\n    <rect x="308" y="30" width="112" height="36" rx="7" class="dg-box a"/>\n    <text x="364" y="53" text-anchor="middle" class="dg-t">h₁</text>\n    <rect x="428" y="30" width="112" height="36" rx="7" class="dg-box b"/>\n    <text x="484" y="53" text-anchor="middle" class="dg-t">h₂</text>\n    <text x="364" y="86" text-anchor="middle" class="dg-note">P owns h₁</text>\n    <text x="484" y="86" text-anchor="middle" class="dg-note">Q owns h₂</text>\n    <text x="424" y="118" text-anchor="middle" class="dg-note">h₁ and h₂ disjoint, h = h₁ ∪ h₂</text>\n  </g>\n</svg>' },

    { t: 'txt', src: '  (10 ↦ 4) ∗ (20 ↦ 7)   the heap is exactly two cells, at 10 and at 20\n  (10 ↦ 4) ∗ (10 ↦ 7)   unsatisfiable — the two halves would have to be\n                        disjoint and both contain location 10' },

    { t: 'p', h: 'The second line is not merely unsatisfied. It entails <code>aFalse</code>, in two lines:' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M4 prelude. Exercise 7 makes this a corollary: <code>two_cells_distinct l l v v</code> concludes <code>fact (fun _ =&gt; l ≠ l)</code>, which is the same contradiction wearing a different hat.',
      src: `theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :
    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩
  subst hp; subst hq
  exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl` },

    { t: 'p', h: 'Read the last line right to left. <code>hd</code> is the disjointness the star handed you; <code>singleton_disjoint_iff</code> turns it into <code>l ≠ l</code>, which is <code>l = l → False</code>; feeding it <code>rfl</code> produces the <code>False</code> the goal wanted. No program, no pointer, no execution — just the monoid.' },

    { t: 'h4', s: 'What the disjointness conjunct is holding up' },

    { t: 'p', h: 'Conjunct 3 looks like hygiene. Take it out and the connective does not get sloppy; it gets <i>duplicating</i>:' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M4 prelude. None of the three names is in the corpus. <code>union_self</code> is unremarkable: at each location the left copy answers first, and it is the same heap.',
      src: `def starNoDisj (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂

theorem union_self (h : Heap) : Heap.union h h = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none h hl]; exact hl
  | some v => rw [union_of_some h hl]

theorem starNoDisj_dup (P : Assertion) : P ⊢ starNoDisj P P :=
  fun _ h hp => ⟨h, h, (union_self h).symm, hp, hp⟩` },

    { t: 'p', h: '<code>hp</code> occurs twice in that term, at the same heap — which is exactly the step <code>and_intro</code> takes and the step <code>∗</code> exists to forbid. Disjointness is what makes the cut <code>⟨h, h, …⟩</code> illegal, and M2’s <code>self_disjoint_empty</code> says the one heap for which it stays legal is <code>Heap.empty</code>.' },

    { t: 'p', h: 'On paper the whole definition is <code>h = h₁ ⊎ h₂</code>, and <code>⊎</code> does three jobs in one symbol: it asserts disjointness, it forms the union, and it names the decomposition. Lean makes those conjuncts 3 and 4 plus the two binders. Three components where paper has one operator — which is why a star carries six things and not four.' },

    /* ================================================================
       2 — the two moves
       ================================================================ */

    { t: 'h3', s: 'Six slots' },

    { t: 'txt', src: '  to PROVE  (P ∗ Q) σ h :\n      supply  ⟨h₁, h₂, hdisj, hunion, hP, hQ⟩\n      i.e. the two pieces, their disjointness, h = h₁ ∪ h₂, and the two facts\n\n  to USE    hstar : (P ∗ Q) σ h :\n      obtain ⟨h₁, h₂, hdisj, hunion, hP, hQ⟩ := hstar' },

    { t: 'p', h: 'The order is the definition read left to right and it never varies. Six names for what is syntactically a two-level <code>∃</code> wrapping a three-level <code>∧</code>: the flattening is free, and you never write the inner brackets.' },

    { t: 'trace', title: 'Destructuring a star, in slow motion',
      start: 'P Q : Assertion\nσ : Store\nh : Heap\nhstar : (P ∗ Q) σ h\n⊢ (Q ∗ P) σ h',
      steps: [
        { tac: 'obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hstar',
          state: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (Q ∗ P) σ h',
          h: 'One hypothesis became six. Two heaps entered the context and <code>h</code> is now tied to them by <code>hu</code>. Nothing is proved — this is the first line of almost every proof in the chapter.' }
      ],
      done: 'The goal is untouched: destructuring a hypothesis never changes it.' },

    { t: 'p', h: 'The goal stays folded as <code>(Q ∗ P) σ h</code>, and <code>exact ⟨…⟩</code> is accepted against it anyway. To <i>see</i> what you owe, ask:' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M4 prelude. The <code>show</code> proves nothing; it makes the obligation readable.',
      src: `example (P : Assertion) : P ⊢ emp ∗ P := by
  intro σ h hp
  show ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ emp σ h₁ ∧ P σ h₂
  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩` },

    { t: 'state', cap: 'The goal after that <code>show</code> — the six slots, spelled out.',
      src: 'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ emp σ h₁ ∧ P σ h₂' },

    { t: 'note', kind: 'tip', title: 'Seeing which slot is failing',
      h: 'Replace <code>exact ⟨a, b, c, d, e, f⟩</code> by <code>refine ⟨a, b, ?_, ?_, ?_, ?_⟩</code> and the four remaining components become four goals, in order. Several traces below do exactly that where the shipped proof supplies the same components inside one <code>exact</code>; each of them says so. Only <b>m4-4</b> is really a <code>refine</code> proof.' },

    { t: 'p', h: 'Every heap-level obligation in the eight exercises is one of M2’s nine laws, applied unchanged. The two refutations in the chapter body reach further back — to <code>singleton_same</code>, <code>singleton_other</code> and <code>union_of_none</code> — because refuting an entailment means evaluating a concrete heap at a concrete location, and the exercises never do that.' },

    /* ================================================================
       3 — emp is the unit
       ================================================================ */

    { t: 'sec', s: 'Exercises · emp is the unit' },

    { t: 'ex',
      id: 'm4-1',
      name: 'star_emp_left / star_emp_right',
      hard: false,

      why: 'Your first two proofs that consume a star, and the shape you will write again: rewrite the goal’s heap with the reassembly equation, collapse it with a unit law, hand over the surviving hypothesis. M9’s <code>moveCell_spec</code> ends with <code>star_emp_left</code> applied to the <code>emp ∗ (dst ↦ a)</code> that freeing a cell leaves behind, and both base cases of M10’s <code>lseg_append</code> and <code>lseg_listRep</code> are this proof written out by hand.',

      setup: 'In scope: everything from M2 and M3, plus <code>star</code>. You want <code>union_empty_left</code> and <code>union_empty_right</code>.',

      goal: 'theorem star_emp_left  (P : Assertion) : emp ∗ P ⊢ P\ntheorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P',

      hints: [
        'The statement unfolds to <code>∀ σ h, (emp ∗ P) σ h → P σ h</code>, so the proof opens with <code>intro</code> taking three things.',
        'Destructure the star in that same <code>intro</code>, with six names. Disjointness is not needed here — put <code>_</code> in its slot.',
        'You hold <code>he : emp σ h₁</code> and <code>hu : h = Heap.union h₁ h₂</code>, and the goal is <code>P σ h</code>. Rewrite the goal’s heap until it becomes <code>h₂</code>.',
        'Three rewrites in one call, in this order: <code>rw [hu, he, union_empty_left]</code>, then <code>exact hp</code>. For <code>star_emp_right</code>, the same with <code>union_empty_right</code> and the last two names swapped.'
      ],

      sol: 'theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩\n  rw [hu, he, union_empty_left]\n  exact hp\n\ntheorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, hp, he⟩\n  rw [hu, he, union_empty_right]\n  exact hp',

      expl: 'The rewrites never touch <code>P</code>. They only change the heap <code>P</code> is applied to: from <code>h</code> to <code>h₁ ∪ h₂</code> to <code>Heap.empty ∪ h₂</code> to <code>h₂</code>, which is where <code>hp</code> already lives.',

      walk: [
        { tac: 'intro σ h ⟨h₁, h₂, _, hu, he, hp⟩', h: 'Store, heap, then the star taken apart in place. Slot 3 is discarded with <code>_</code>; Lean keeps it under the inaccessible name <code>left✝</code> — not a description of the slot, but the field name of the <code>∧</code> it came from, <code>And.left</code>. Three exercises here produce one: from slot 3 twice and from slot 4 once.' },
        { tac: 'rw [hu, he, union_empty_left]', h: 'Three rewrites in the goal. <code>hu</code> replaces <code>h</code> by <code>h₁.union h₂</code>, <code>he</code> replaces <code>h₁</code> by <code>Heap.empty</code>, and the unit law collapses what is left. Note that <code>union_empty_left</code> is handed to <code>rw</code> <b>unapplied</b> even though its <code>h</code> is explicit: <code>rw</code> unifies the lemma’s left-hand side against the goal and discovers <code>?h := h₂</code>. In <i>term</i> position — the very next exercise — the same lemma must be written <code>union_empty_left h</code>, because there is no goal to unify against.' },
        { tac: 'exact hp', h: 'The goal is now literally <code>hp</code>.' },
        { tac: 'theorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by', h: 'The mirror statement.' },
        { tac: 'intro σ h ⟨h₁, h₂, _, hu, hp, he⟩', h: 'Same six slots, but <code>P</code> is now the left conjunct: slot 5 is <code>hp : P σ h₁</code> and slot 6 is <code>he : emp σ h₂</code>. The names swapped; the pattern did not.' },
        { tac: 'rw [hu, he, union_empty_right]', h: '<code>he</code> now rewrites <code>h₂</code>, leaving <code>h₁.union Heap.empty</code>, so it is the other unit law that closes it. Using <code>union_empty_left</code> here fails — see the pitfall.' },
        { tac: 'exact hp', h: 'The goal is <code>P σ h₁</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'star_emp_left, one rewrite at a time',
          start: 'P : Assertion\n⊢ emp ∗ P ⊢ P',
          steps: [
            { tac: 'intro σ h ⟨h₁, h₂, _, hu, he, hp⟩',
              state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ h',
              h: 'The discarded disjointness is present as <code>left✝</code>, and <code>he</code> displays folded as <code>emp σ h₁</code>. Both are display facts; neither changes what the terms are.' },
            { tac: 'rw [hu]',
              state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ (h₁.union h₂)',
              h: 'The goal’s heap is now written in terms of the two pieces.' },
            { tac: 'rw [he]',
              state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ (Heap.empty.union h₂)',
              h: 'The middle rewrite M3 forecast, doing what it was forecast to do.' },
            { tac: 'rw [union_empty_left]',
              state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ h₂',
              h: 'A monoid law, applied inside an assertion. The goal is now <code>hp</code>.' }
          ],
          done: 'No goals.' },

        { t: 'cmp',
          left: { t: 'The naive attempt', kind: 'bad',
                  h: 'Unfold everything and hope. <code>simp</code> does unfold, and leaves you holding the existential you still have to destructure.',
                  tag: 'sketch',
                  src: 'intro σ h hstar\nsimp [star, emp] at hstar\nexact hstar' },
          right: { t: 'What Lean actually says', kind: 'good',
                   h: 'The mismatch is the lesson: <code>simp</code> normalised the hypothesis into something readable and then had nothing left to do. Destructuring is not a preliminary; it is the proof.',
                   tag: 'sketch',
                   src: 'error: Type mismatch\n  hstar\nhas type\n  ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ h₁ = Heap.empty ∧ P σ h₂\nbut is expected to have type\n  P σ h' } }
      ],

      pitfall: 'Getting the arity wrong. Write five names instead of six — <code>⟨h₁, h₂, _, hu, he⟩</code> — and Lean does <b>not</b> complain at the <code>intro</code>. The last name absorbs everything left over, so <code>he</code> silently gets type <code>emp σ h₁ ∧ P σ h₂</code>, and the complaint arrives one line later from the <code>rw</code>: <code>Invalid rewrite argument: Expected an equality or iff proof or definition name, but `he` is a proof of emp σ h₁ ∧ P σ h₂</code>. Whenever an error mentions a <code>∧</code> you did not expect, count the names in your pattern. The error points at the use, never at the pattern that caused it.',

      variants: 'Reverse the unit law: <code>rw [hu, he, union_empty_right]</code> inside <code>star_emp_left</code> fails with <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern Heap.union ?h Heap.empty in the target expression P σ (Heap.empty.union h₂)</code>. The two lemmas say the same thing about the monoid and are not interchangeable syntactically. Drop the <code>emp</code> altogether and the statement becomes <code>Q ∗ P ⊢ P</code>, which is <b>false</b> — refuted by machine right after the next exercise.'
    },

    { t: 'ex',
      id: 'm4-2',
      name: 'star_emp_left_intro / star_emp_right_intro',
      hard: false,

      why: 'Your first proofs that <i>construct</i> a star, so the first time you have to invent the cut — the only genuinely creative act in the chapter. Here the invention is forced, which is why it is the right place to learn the mechanics. Together with the previous exercise these give <code>emp ∗ P ⊣⊢ P</code>.',

      setup: 'You need <code>disjoint_empty_left</code>, <code>disjoint_empty_right</code>, <code>union_empty_left</code>, <code>union_empty_right</code>. No tactic beyond <code>intro</code> and <code>exact</code>.',

      goal: 'theorem star_emp_left_intro  (P : Assertion) : P ⊢ emp ∗ P\ntheorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp',

      hints: [
        'The star is now the goal, so there is nothing to destructure: after <code>intro σ h hp</code> you owe a six-component tuple.',
        'Which cut? You have one heap and one conjunct that only <code>Heap.empty</code> can satisfy. The split is forced.',
        'Fill the slots in order: the two heaps, <code>disjoint_empty_left h</code>, the equation <code>h = Heap.union Heap.empty h</code>, a proof of <code>emp σ Heap.empty</code> — which is <code>rfl</code> — and then <code>hp</code>.',
        'Slot 4 is the trap. Your lemma says <code>Heap.union Heap.empty h = h</code>; the slot wants it the other way round. Apply <code>.symm</code>.'
      ],

      sol: 'theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by\n  intro σ h hp\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩\n\ntheorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by\n  intro σ h hp\n  exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩',

      expl: 'Slots 1 and 2 are the choice; slots 3 and 4 are M2; slots 5 and 6 are the two assertions at their own pieces. Getting the direction of slot 4 right is most of the friction in these proofs, and reading the slot beats guessing.',

      walk: [
        { tac: 'intro σ h hp', h: 'Three introductions and no destructuring: the hypothesis <code>P σ h</code> is atomic. The goal becomes <code>(emp ∗ P) σ h</code>.' },
        { tac: 'exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩', h: 'All six slots at once. Nothing on the left, everything on the right; disjointness of the empty heap from anything; the reassembly equation, flipped; <code>rfl</code> for <code>emp σ Heap.empty</code>, which is <code>Heap.empty = Heap.empty</code>; and the hypothesis unchanged.' },
        { tac: 'theorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by', h: '<code>emp</code> on the right now.' },
        { tac: 'intro σ h hp', h: 'Identical opening.' },
        { tac: 'exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩', h: 'Every slot mirrored: the heaps swap, both M2 lemmas become their right-handed versions, and <code>hp</code> trades places with <code>rfl</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'The four obligations, exposed with refine',
          start: 'P : Assertion\n⊢ P ⊢ emp ∗ P',
          steps: [
            { tac: 'intro σ h hp',
              state: 'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ (emp ∗ P) σ h',
              h: 'Folded. You cannot read the obligations off it yet.' },
            { tac: 'show ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ emp σ h₁ ∧ P σ h₂',
              state: 'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ emp σ h₁ ∧ P σ h₂',
              h: 'A no-op logically; the difference between guessing and reading.' },
            { tac: 'refine ⟨Heap.empty, h, ?_, ?_, ?_, ?_⟩',
              state: 'case refine_1\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ Heap.empty.disjoint h\n\ncase refine_2\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ h = Heap.empty.union h\n\ncase refine_3\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ emp σ Heap.empty\n\ncase refine_4\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ P σ h',
              h: 'Four goals in slot order. Committing the two heaps is what turned one abstract goal into four concrete ones, and <code>refine_2</code> is where the <code>.symm</code> lives.' }
          ],
          done: 'Each goal closed by the corresponding component of the shipped one-line exact.' },

        { t: 'steps', title: 'Choosing a cut, in general',
          items: [
            { k: 'Start from the conjunct that constrains the heap most', h: '<code>emp</code> forces <code>Heap.empty</code>; <code>l ↦ v</code> forces <code>Heap.singleton l v</code>; <code>fact φ</code> forces nothing.' },
            { k: 'Give the rest to the other side', h: 'Here <code>emp</code> takes nothing, so <code>P</code> takes all of <code>h</code>. In M8 the constrained side is the footprint of a command and the other side is the frame <code>R</code>; <code>hoare_frame</code> makes exactly this choice.' },
            { k: 'Then slots 3 and 4 are pure monoid facts', h: 'Once the heaps are fixed, no assertion appears in either obligation.' }
          ] },

        { t: 'detail', title: 'One of these .symm’s is optional and the other is not', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'M2 proved <code>union_empty_left</code> by <code>funext l; rfl</code> and <code>union_empty_right</code> by a case split, because <code>Heap.union</code> matches on its first argument. Eta makes that asymmetry survive to the function level:' },
            { t: 'code', tag: 'illustration',
              src: `example (h : Heap) : Heap.union Heap.empty h = h := rfl   -- accepted` },
            { t: 'p', h: 'So slot 4 of <code>star_emp_left_intro</code> could equally be <code>rfl</code>, or <code>union_empty_left h</code> with no <code>.symm</code>. The second of those looks like a type error and is not: the slot asks for <code>@Eq Heap h (Heap.union Heap.empty h)</code> and you offer <code>@Eq Heap (Heap.union Heap.empty h) h</code>, which are different types that both reduce to <code>@Eq Heap h h</code>. The <code>.symm</code> is there for uniformity with its mirror image.' },
            { t: 'p', h: 'In <code>star_emp_right_intro</code> nothing of the sort is available: the <code>match</code> is stuck on the variable <code>h</code>, so no reduction happens. <code>rfl</code> in slot 4 is rejected with <code>Application type mismatch: The argument rfl has type ?m.17 = ?m.17 but is expected to have type h = h.union Heap.empty</code>, and dropping the <code>.symm</code> gives <code>Application type mismatch: The argument union_empty_right h has type h.union Heap.empty = h but is expected to have type h = h.union Heap.empty</code>. The first says nothing proves this by computation; the second says this proves it backwards.' },
            { t: 'p', h: 'The moral is not to memorise which one is definitional. It is that when an equation slot rejects your term, the only question worth asking first is whether the two types are the same equation read backwards. In this chapter they usually are.' }
          ] }
      ],

      pitfall: 'Forgetting <code>.symm</code> on slot 4. The error ends <code>in the application And.intro (union_empty_right h)</code>, naming an <code>And.intro</code> you never wrote — that is the anonymous constructor showing its underlying form. Read past it to the two types.',

      variants: 'Swap slots 5 and 6 and the error is immediate: <code>Application type mismatch: The argument hp has type P σ h but is expected to have type emp σ Heap.empty</code>. The two assertions are pinned to different pieces and cannot trade places. Swap slots <i>1 and 2</i> instead — <code>⟨h, Heap.empty, …⟩</code> in <code>star_emp_left_intro</code> — and <code>refine</code> shows two impossible obligations at once, <code>⊢ emp σ h</code> and <code>⊢ P σ Heap.empty</code>. That failure is the useful one: it shows the cut is forced rather than conventional.'
    },

    /* ================================================================
       4 — no projection
       ================================================================ */

    { t: 'h3', s: 'No projection' },

    { t: 'p', h: 'M3 asked for a connective under which <code>P ∗ emp ⊢ P</code> holds and <code>P ∗ Q ⊢ P</code> fails. Exercise 1 was the first half. The second half is not an exercise, because there is nothing to prove — only something to refute:' },

    { t: 'code', tag: 'illustration',
      cap: 'Compiles against the M4 prelude. Forgetting a conjunct would mean leaking its memory.',
      src: `theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by
  intro hcontra
  have hs : ((0 ↦ 4) ∗ (1 ↦ 7)) (fun _ => 0)
      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) :=
    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩
  have h := hcontra (fun _ => 0) _ hs
  have h1 : Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7) 1
      = Heap.singleton 0 4 1 := by rw [h]
  rw [union_of_none _ (singleton_other 0 1 4 (by simp)), singleton_same,
      singleton_other 0 1 4 (by simp)] at h1
  exact absurd h1 (by simp)` },

    { t: 'p', h: 'The witness is a two-cell heap. If the entailment held, that heap would have to <i>be</i> the one-cell heap <code>Heap.singleton 0 4</code>, and evaluating both at location 1 gives <code>some 7 = none</code>. Two details in the middle are worth reading twice. <code>hs</code> is a six-slot tuple whose slots 4, 5 and 6 are all <code>rfl</code>, because the heap was <i>written</i> as the union of the two singletons and <code>l ↦ v</code> is an equation. And the long <code>rw … at h1</code> is three lookups: the left piece answers <code>none</code> at location 1 so the union defers to the right piece, which answers <code>some 7</code>, while the right-hand side <code>Heap.singleton 0 4 1</code> is <code>none</code>.' },

    { t: 'note', kind: 'warn', title: 'The consequence you will feel in M7',
      h: 'You can never drop an unused conjunct from a precondition. If a command needs <code>l ↦ v</code> and your precondition is <code>l ↦ v ∗ R</code>, you do not weaken to <code>l ↦ v</code> and proceed — you apply the <b>frame rule</b>, which carries <code>R</code> through to the postcondition. The missing projection is what forces the frame rule to exist and what makes it sound.' },

    /* ================================================================
       5 — commutativity
       ================================================================ */

    { t: 'sec', s: 'Exercises · commutativity' },

    { t: 'ex',
      id: 'm4-3',
      name: 'star_comm',
      hard: false,

      why: 'One direction gives both, since applying it twice gives <code>⊣⊢</code>. It is also the cheapest demonstration of what disjointness buys: the same two heaps, reassembled in the other order, give the same heap — and that sentence is false without <code>hd</code>. Every reordering of a precondition in M9 is this lemma underneath.',

      setup: '<code>union_comm</code> takes the disjointness proof as an argument: <code>union_comm hd : Heap.union h₁ h₂ = Heap.union h₂ h₁</code>.',

      goal: 'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P',

      hints: [
        'Destructure with the usual six names, then build the goal from the same six things rearranged. Nothing new is created.',
        'Slots 1 and 2 swap, and so do 5 and 6. Only slots 3 and 4 have work in them.',
        'Slot 3 is <code>disjoint_symm hd</code>. Slot 4 needs <code>h = Heap.union h₂ h₁</code> from <code>hu : h = Heap.union h₁ h₂</code>: rewrite with <code>hu</code>, then with <code>union_comm hd</code>. A tactic block may sit inside a term slot as <code>by …</code>.'
      ],

      sol: 'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩',

      expl: 'One line of real content: <code>by rw [hu, union_comm hd]</code>. That is where the commutativity half of the partial commutative monoid is spent, and it is the only place in the proof that <code>hd</code> is used for anything.',

      walk: [
        { tac: 'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩', h: 'All six components kept: unlike the unit laws, this one needs the disjointness, so slot 3 gets a real name.' },
        { tac: 'exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩', h: 'Slots 1, 2, 5, 6 are the given data with left and right exchanged. Slot 3 flips the disjointness. Slot 4 opens tactic mode inside the tuple, where the goal is <code>h = h₂.union h₁</code>: <code>rw [hu]</code> makes it <code>h₁.union h₂ = h₂.union h₁</code> and <code>rw [union_comm hd]</code> closes it. Hoisting that into a <code>have</code> before the <code>exact</code> works identically and costs a line; from M7 on these tuples get long and the equation slot is almost always a one-liner.' }
      ],

      deep: [
        { t: 'trace', title: 'star_comm with the inline by-block pulled out',
          start: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (Q ∗ P) σ h',
          steps: [
            { tac: 'refine ⟨h₂, h₁, disjoint_symm hd, ?_, hq, hp⟩',
              state: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ h = h₂.union h₁',
              h: 'Five slots close instantly and the leftover goal is the heap equation. Same proof as the shipped one: <code>?_</code> here, <code>by …</code> there.' },
            { tac: 'rw [hu]',
              state: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ h₁.union h₂ = h₂.union h₁',
              h: 'A monoid law standing alone, with every trace of <code>∗</code> stripped off it.' },
            { tac: 'rw [union_comm hd]',
              state: 'No goals.',
              h: 'The left-hand side becomes <code>h₂.union h₁</code>, the two sides coincide, and <code>rw</code>’s trailing step finishes.' }
          ],
          done: 'No goals.' },

        { t: 'p', h: 'Where the information goes: slots 1, 2, 5, 6 are a permutation and cost nothing, slot 3 costs one lemma, and slot 4 spends the only disjointness in the proof. The theorem is that one <code>rw</code>.' }
      ],

      pitfall: 'Writing <code>by rw [hu]</code> and stopping there, on the theory that the two unions are obviously the same heap. They are not <i>syntactically</i> the same, so Lean reports <code>unsolved goals … ⊢ h₁.union h₂ = h₂.union h₁</code>. That residue is the theorem; if it looks like nothing needs doing, you have found the exact spot where a paper proof waves its hands.',

      variants: 'Drop <code>hd</code> and the lemma is <b>false</b>, not merely unprovable: with <code>h₁ = Heap.singleton 0 4</code> and <code>h₂ = Heap.singleton 0 7</code> the two unions disagree at location 0, because M2’s union is left-biased. Overlap is where the bias becomes visible and disjointness is what hides it. Replace <code>disjoint_symm hd</code> by <code>hd</code> and slot 3 mismatches: <code>h₂.disjoint h₁</code> and <code>h₁.disjoint h₂</code> are different propositions, each implying the other.'
    },

    /* ================================================================
       6 — associativity
       ================================================================ */

    { t: 'sec', s: 'Exercises · associativity' },

    { t: 'txt', src: '  (P ∗ Q) ∗ R                     P ∗ (Q ∗ R)\n\n   ┌────────┬────┐                 ┌────┬────────┐\n   │ hP  hQ │ hR │      ═══>       │ hP │ hQ  hR │\n   └────────┴────┘                 └────┴────────┘\n     h = (hP ∪ hQ) ∪ hR              h = hP ∪ (hQ ∪ hR)' },

    { t: 'p', h: 'The heaps do not move; the brackets do. So the heap equation is <code>union_assoc</code> and generates nothing to discharge, and all the work is in the disjointness: you extract <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code> from <code>(hP ∪ hQ) ⊥ hR</code>, and you reassemble <code>hP ⊥ (hQ ∪ hR)</code> from <code>hP ⊥ hQ</code> and <code>hP ⊥ hR</code>. One <code>.mp</code>, one <code>.mpr</code>, and the three pairwise facts in between.' },

    { t: 'ex',
      id: 'm4-4',
      name: 'star_assoc_left / star_assoc_right',
      hard: true,

      why: 'This is what lets you stop thinking about heaps and start thinking about a <i>list</i> of owned resources. Without it every later proof is a parenthesisation nightmare; with it, <code>star_swap_middle</code> and everything in M9 and M10 is bracket-shuffling by lemma name.',

      setup: '<code>disjoint_union_left</code> and <code>disjoint_union_right</code> are both <code>↔</code>, so you reach for <code>.mp</code> and <code>.mpr</code>. The heap equation is <code>union_assoc</code>, which takes no hypothesis.',

      goal: 'theorem star_assoc_left  (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R',

      hints: [
        'The hypothesis is a star whose left conjunct is itself a star. Nest the pattern: the fifth slot of the outer <code>⟨…⟩</code> is where the inner one goes.',
        'You now hold two heap equations, <code>hu₁ : h = hPQ.union hR</code> and <code>hu₂ : hPQ = hP.union hQ</code>. Eliminate the intermediate heap with <code>subst hu₂</code>.',
        '<code>hd₁</code> then reads <code>(hP.union hQ).disjoint hR</code>, which is the left-hand side of <code>disjoint_union_left</code>. Split the result with <code>obtain</code>.',
        'Declare the new cut with <code>refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩</code>. The first hole is <code>rw [hu₁, union_assoc]</code>; the second is the inner star, <code>exact ⟨hQ, hR, hQR, rfl, hq, hr⟩</code>.'
      ],

      sol: 'theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩\n  subst hu₂\n  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁\n  refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩\n  · rw [hu₁, union_assoc]\n  · exact ⟨hQ, hR, hQR, rfl, hq, hr⟩\n\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by\n  intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩\n  subst hu₂\n  obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁\n  refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩\n  rw [hu₁, union_assoc]',

      expl: 'Read the <code>refine</code> as a declaration: the new cut is <code>hP</code> on the left and <code>hQ ∪ hR</code> on the right. Everything after it discharges four obligations — the assembled disjointness, the re-bracketed heap, <code>P</code> unchanged, and the inner star, whose own equation slot is <code>rfl</code> because the heap you chose for it <i>is</i> <code>hQ.union hR</code>, syntactically.',

      walk: [
        { tac: 'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩', h: 'Both levels at once. Slot 5 of the outer pattern would hold a proof of <code>(P ∗ Q) σ hPQ</code>, so it is destructured with six more names. Three heaps that matter, one about to disappear, two disjointness facts, two equations.' },
        { tac: 'subst hu₂', h: '<code>hu₂ : hPQ = hP.union hQ</code>, so <code>subst</code> eliminates the variable <code>hPQ</code> everywhere and discards the equation. <code>hd₁</code> and <code>hu₁</code> are rewritten silently; the goal is untouched, since <code>hPQ</code> never occurred in it.' },
        { tac: 'obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁', h: 'The extraction step. <code>hd₁ : (hP.union hQ).disjoint hR</code> becomes <code>hPR : hP.disjoint hR</code> and <code>hQR : hQ.disjoint hR</code>.' },
        { tac: 'refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩', h: 'The new cut. Slot 2 is written out because Lean has no way to guess it. Slot 3 assembles <code>hP ⊥ (hQ ∪ hR)</code> from the two halves with the backward direction. Slots 4 and 6 become holes.' },
        { tac: '· rw [hu₁, union_assoc]', h: 'First hole: <code>h = hP.union (hQ.union hR)</code>. <code>hu₁</code> rewrites <code>h</code> to the left-bracketed union, <code>union_assoc</code> re-brackets it, and both sides then coincide.' },
        { tac: '· exact ⟨hQ, hR, hQR, rfl, hq, hr⟩', h: 'Second hole: <code>(Q ∗ R) σ (hQ.union hR)</code>. Six slots, with <code>rfl</code> in the equation and the two assertion proofs unchanged.' },
        { tac: 'theorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by', h: 'The converse: the same three moves in a mirror. The only asymmetry is which <code>disjoint_union_*</code> is used in which direction.' },
        { tac: 'intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩', h: 'The nesting is in slot 6 now, because the inner star is on the right.' },
        { tac: 'subst hu₂', h: 'Eliminates <code>hQR</code> in favour of <code>hQ.union hR</code>.' },
        { tac: 'obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁', h: '<code>hd₁ : hP.disjoint (hQ.union hR)</code> has the union on the right, so it is the other lemma that applies.' },
        { tac: 'refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩', h: 'One hole only; the inner star is short enough to inline, again with <code>rfl</code> in its equation slot. The argument order <code>⟨hPR, hd₂⟩</code> matches the conjunction on the right of that lemma.' },
        { tac: 'rw [hu₁, union_assoc]', h: 'The lone remaining goal. No bullet is needed when exactly one goal is left.' }
      ],

      deep: [
        { t: 'trace', title: 'star_assoc_left, tactic by tactic',
          start: 'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R',
          steps: [
            { tac: 'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩',
              state: 'P Q R : Assertion\nσ : Store\nh hPQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhu₁ : h = hPQ.union hR\nhP hQ : Heap\nhd₂ : hP.disjoint hQ\nhu₂ : hPQ = hP.union hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\n⊢ (P ∗ Q ∗ R) σ h',
              h: 'Read the goal carefully: <code>P ∗ Q ∗ R</code> is <code>P ∗ (Q ∗ R)</code>. Look back at the starting state — the source bracketing on the left of the turnstile kept its parentheses and the target on the right lost them.' },
            { tac: 'subst hu₂',
              state: 'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\n⊢ (P ∗ Q ∗ R) σ h',
              h: '<code>hPQ</code> and <code>hu₂</code> are gone, and the two hypotheses that mentioned <code>hPQ</code> have moved to the bottom — <code>subst</code> re-asserts everything it rewrites, so positions change. Nothing was lost.' },
            { tac: 'obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁',
              state: 'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (P ∗ Q ∗ R) σ h',
              h: 'All three pairwise disjointnesses are now in the context. That is the entire content of the hypothesis; from here the proof is assembly.' },
            { tac: 'refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩',
              state: 'case refine_1\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ h = hP.union (hQ.union hR)\n\ncase refine_2\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (Q ∗ R) σ (hQ.union hR)',
              h: 'Two goals, and they are the two halves of the picture: re-bracket the heap, rebuild the inner star. Everything about <code>P</code> was discharged by passing <code>hp</code> directly.' }
          ],
          done: 'No goals, after rw [hu₁, union_assoc] and exact ⟨hQ, hR, hQR, rfl, hq, hr⟩.' },

        { t: 'detail', title: 'subst, and when it refuses', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: '<code>subst h</code> wants an equation with a <b>local variable on one side</b> that does not occur on the other. <code>hu₂ : hPQ = hP.union hQ</code> qualifies. <code>hu₁ : h = hPQ.union hR</code> qualifies too, eliminating <code>h</code> instead: add <code>subst hu₁</code> after <code>subst hu₂</code>, the goal becomes <code>(P ∗ Q ∗ R) σ ((hP.union hQ).union hR)</code>, and the proof finishes with <code>rw [union_assoc]</code> alone. Which heap to eliminate is your choice; doing it once is worth the minute.' },
            { t: 'p', h: 'What <code>subst</code> refuses is an equation between two compound terms, because there is no variable to eliminate. On <code>he : h₁.union h₂ = h₂.union h₁</code> it reports <code>Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)</code>. That message means you wanted <code>rw</code>.' },
            { t: 'p', h: 'In <b>m4-7</b> you will <code>subst</code> a hypothesis of type <code>(l ↦ v) σ h₁</code>, which is only definitionally an equation between heaps. It goes through for the same reason <code>rw [he]</code> went through in <b>m4-1</b>.' }
          ] }
      ],

      pitfall: 'Reaching for the wrong member of the <code>disjoint_union_*</code> pair. In <code>star_assoc_left</code> the hypothesis has the union on the <b>left</b> of the disjointness, so it is <code>disjoint_union_left</code>. Using the other one gives <code>Application type mismatch: The argument hd₁ has type (hP.union hQ).disjoint hR but is expected to have type Heap.disjoint ?m.122 (Heap.union ?m.123 ?m.124)</code> — three separate holes, arbitrarily numbered, describing a shape with the union on the right. The name says which side of <code>Heap.disjoint</code> the union sits on, not which side of the goal you are working on.',

      variants: 'Delete <code>subst hu₂</code> and carry <code>hPQ</code> through by hand with <code>rw [hu₂] at hd₁ hu₁</code>. It works, and you must remember both places; forget one and you are left with a goal about a heap that no longer relates to anything. Then the interesting one: remove disjointness from <code>∗</code> altogether and associativity <b>survives</b>, because <code>union_assoc</code> needs no hypothesis. What dies is commutativity. The two laws fail for genuinely different reasons, and the M2 signatures say so if you look.'
    },

    /* ================================================================
       7 — monotonicity and distribution
       ================================================================ */

    { t: 'sec', s: 'Exercises · monotonicity and distribution' },

    { t: 'ex',
      id: 'm4-5',
      name: 'star_mono',
      hard: false,

      why: 'This is what lets you improve one side of a specification without touching the other. The frame rule of M8 is stated with an arbitrary <code>R</code>, and rewriting one side of a star underneath that frame is what <code>star_mono_left</code> and <code>star_mono_right</code> are for: M9’s <code>copyCell_spec</code> uses <code>star_mono_right _ (star_comm …)</code> to swap two cells inside a bigger precondition, and M10’s <code>lseg_append</code> uses <code>star_mono_right</code> twice per inductive step to push the induction hypothesis into the tail of a list. Without it each of those steps is a fresh semantic proof.',

      setup: 'You want <code>entails_refl</code>. This is the one law in the chapter whose proof uses no lemma about heaps at all.',

      goal: 'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\'',

      hints: [
        'Keep the cut you were given and push each entailment into its own piece. The heap does not change at all.',
        'After the six-name destructuring the goal wants <code>P\' σ h₁</code> and <code>Q\' σ h₂</code>, and you hold <code>hp : P σ h₁</code>, <code>hq : Q σ h₂</code> and two entailments. Apply them.',
        'Slot 5 is <code>hpq σ h₁ hp</code> and slot 6 is <code>hrs σ h₂ hq</code> — at the piece where the assertion actually holds, not at <code>h</code>.',
        'For the two specialisations, feed <code>entails_refl</code> to the side you are not changing.'
      ],

      sol: 'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\' := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩\n\ntheorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=\n  star_mono h (entails_refl Q)\n\ntheorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=\n  star_mono (entails_refl P) h',

      expl: 'Slots 1–4 are copied across verbatim; only 5 and 6 change, by one function application each. <code>∗</code> touches the heap, the entailments touch the assertions, and the two never meet.',

      walk: [
        { tac: 'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩', h: 'All six components kept, because four of them are reused unchanged.' },
        { tac: 'exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩', h: 'The cut, its disjointness and its equation are the ones you were handed. The two entailments are applied at their own pieces.' },
        { tac: 'theorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=', h: 'Term mode, no <code>by</code>. <code>Q</code> is explicit while <code>P</code> and <code>P\'</code> are implicit: you know the entailment and want to say which frame you are holding fixed, so <code>star_mono_left R h</code> reads the way you use it.' },
        { tac: 'star_mono h (entails_refl Q)', h: 'The identity entailment on the right unifies <code>Q\'</code> with <code>Q</code>, and the conclusion collapses to what was wanted.' },
        { tac: 'theorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=', h: 'Mirror image, with <code>P</code> explicit for the same reason.' },
        { tac: 'star_mono (entails_refl P) h', h: 'Identity on the left. Two one-line derivations rather than two more semantic proofs.' }
      ],

      deep: [
        { t: 'trace', title: 'star_mono, with the two obligations exposed',
          start: 'P P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\n⊢ P ∗ Q ⊢ P\' ∗ Q\'',
          steps: [
            { tac: 'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩',
              state: 'P P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (P\' ∗ Q\') σ h',
              h: 'Two entailments in the context, one goal at <code>h</code>.' },
            { tac: 'refine ⟨h₁, h₂, hd, hu, ?_, ?_⟩',
              state: 'case refine_1\nP P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ P\' σ h₁\n\ncase refine_2\nP P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ Q\' σ h₂',
              h: 'Each residual goal is localised to its own piece, and that localisation is the theorem: the entailment about <code>P</code> is used at <code>h₁</code> and never has to know that <code>h₂</code> exists.' }
          ],
          done: 'Closed by hpq σ h₁ hp and hrs σ h₂ hq — which the shipped proof supplies inside one exact, in these two slots.' },

        { t: 'dl', items: [
          { k: '<code>star_mono hpq hrs</code>', h: 'Both sides change. Rare in use, but it is the one that gets proved.' },
          { k: '<code>star_mono_left R h</code>', h: 'Improve the left conjunct, keep the frame <code>R</code>.' },
          { k: '<code>star_mono_right P h</code>', h: 'Keep the footprint, improve the frame.' }
        ] },

        { t: 'p', h: 'With <code>entails_trans</code>, monotonicity is what lets you rewrite <i>inside</i> a star instead of taking one apart. Exercise <b>m4-8</b> is that observation cashed in.' },

        { t: 'detail', title: 'What monotone does not give you', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Monotonicity implies congruence for <code>⊣⊢</code>: apply <code>star_mono_left</code> twice and both directions come out. What it does not give you is anything anti-monotone, and in particular no rule takes <code>P ∗ Q ⊢ R</code> to <code>P ⊢ R</code>.' },
            { t: 'p', h: 'The magic wand of M11 is the adjoint that repairs exactly this: <code>P ∗ Q ⊢ R</code> if and only if <code>P ⊢ Q −∗ R</code>. Monotonicity of <code>∗</code> is what makes that adjunction well behaved.' }
          ] }
      ],

      pitfall: 'Forgetting that an entailment eats three arguments. <code>hpq h₁ hp</code> gives <code>Application type mismatch: The argument h₁ has type Heap but is expected to have type Store</code> — the complaint is about the <i>first</i> argument, which is easy to misread as a complaint about <code>h₁</code>. <code>hpq σ h hp</code>, with the whole heap instead of the piece, fails at the third instead: <code>The argument hp has type P σ h₁ but is expected to have type P σ h</code>.',

      variants: 'Reverse one hypothesis — try to prove <code>P ∗ Q ⊢ P\' ∗ Q\'</code> from <code>P\' ⊢ P</code> — and you are stuck at slot 5 with an entailment pointing the wrong way. No amount of heap manipulation helps, because the heap was never the obstacle. Drop monotonicity entirely and the frame rule still holds, but every use of it in M9 would need the precondition to match the command’s footprint <i>syntactically</i>, which is the pain this lemma removes.'
    },

    { t: 'ex',
      id: 'm4-6',
      name: 'star_or_left / star_exists_left',
      hard: false,

      why: 'The existential one is used in every proof about linked lists, because recursive predicates are quantified over the next pointer: M10 defines <code>listRep (x :: xs) p</code> as <code>aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next</code>, so an <code>∃</code> sits under every cons. <code>star_exists_left</code> is what pulls it to the front of a bigger star, and it is the first line of the inductive step in both <code>lseg_append</code> and <code>lseg_listRep</code>.',

      setup: '<code>aOr P Q</code> is <code>fun σ h =&gt; P σ h ∨ Q σ h</code>, and <code>aExists P</code> is <code>fun σ h =&gt; ∃ x, P x σ h</code>.',

      goal: 'theorem star_or_left (P Q R : Assertion) :\n    (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R)\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q)',

      hints: [
        'Both are destructure-then-rebuild with the same cut. You never touch <code>hd</code> or <code>hu</code>.',
        'For <code>star_or_left</code>, slot 5 has type <code>aOr P Q σ h₁</code>, which is definitionally a disjunction. Split it with <code>rcases hpq with hp | hq</code>.',
        'The goal is definitionally <code>(P ∗ R) σ h ∨ (Q ∗ R) σ h</code>, so each branch closes with <code>Or.inl</code> or <code>Or.inr</code> applied to a full six-slot tuple.',
        'For <code>star_exists_left</code>, nest <code>⟨x, hp⟩</code> in slot 5. The goal is an <code>∃</code>, so its tuple starts with the witness: seven components, the first being <code>x</code>.'
      ],

      sol: 'theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩\n  rcases hpq with hp | hq\n  · exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩\n  · exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by\n  intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩\n  exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩',

      expl: 'The cut is unchanged in both. In <code>star_or_left</code> the two branches differ in two tokens; in <code>star_exists_left</code> the witness travels from the hypothesis to the goal and nothing else happens.',

      walk: [
        { tac: 'intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩', h: 'Slot 5 is called <code>hpq</code> because it holds the disjunction, not a proof of <code>P</code>.' },
        { tac: 'rcases hpq with hp | hq', h: 'The bar separates <i>alternatives</i>, so this splits the goal in two. In the first branch <code>hp : P σ h₁</code>, in the second <code>hq : Q σ h₁</code> — both at <code>h₁</code>, since the cut did not move. Lean labels the branches <code>inl</code> and <code>inr</code>.' },
        { tac: '· exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩', h: 'The goal unfolds to a disjunction; <code>Or.inl</code> commits to the left one, whose content is <code>(P ∗ R) σ h</code>, and the tuple supplies the old cut with <code>hp</code> in slot 5.' },
        { tac: '· exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩', h: 'Two tokens different. That is the visible form of “<code>∗</code> did not care which disjunct held”.' },
        { tac: 'theorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) : …', h: '<code>α : Sort u</code> rather than <code>Type</code>, so the index may itself be a proposition. Free, and occasionally useful.' },
        { tac: 'intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩', h: 'The nested pattern takes <code>aExists P σ h₁</code> apart, binding the witness and <code>hp : P x σ h₁</code> in one go.' },
        { tac: 'exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩', h: 'Seven slots: witness first, then the usual six. It is the <i>same</i> <code>x</code> you received, which is the whole content of the lemma.' }
      ],

      deep: [
        { t: 'trace', title: 'star_or_left: the split, and why both branches look alike',
          start: 'P Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhpq : aOr P Q σ h₁\nhr : R σ h₂\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
          steps: [
            { tac: 'rcases hpq with hp | hq',
              state: 'case inl\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhr : R σ h₂\nhp : P σ h₁\n⊢ aOr (P ∗ R) (Q ∗ R) σ h\n\ncase inr\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhr : R σ h₂\nhq : Q σ h₁\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
              h: 'Two contexts identical but for one hypothesis. Note that <code>hpq</code> displayed as an application of a <code>def</code> with no visible <code>∨</code>, and <code>rcases</code> split it anyway.' }
          ],
          done: 'Each branch closed by Or.inl / Or.inr applied to the unchanged cut.' },

        { t: 'trace', title: 'star_exists_left: the witness travels, the heap does not',
          start: 'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nx : α\nhp : P x σ h₁\nhq : Q σ h₂\n⊢ aExists (fun x => P x ∗ Q) σ h',
          steps: [
            { tac: 'refine ⟨x, ?_⟩',
              state: 'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nx : α\nhp : P x σ h₁\nhq : Q σ h₂\n⊢ (fun x => P x ∗ Q) x σ h',
              h: 'Supplying the witness leaves an unreduced beta-redex in the goal: Lean does not beta-reduce for display. <code>exact ⟨h₁, h₂, hd, hu, hp, hq⟩</code> is checked up to definitional equality and goes through as if the goal read <code>(P x ∗ Q) σ h</code>. If the redex bothers you, <code>show (P x ∗ Q) σ h</code> replaces it, and Lean accepting that <code>show</code> is itself the proof that the two are the same goal.' }
          ],
          done: 'No goals, after exact ⟨h₁, h₂, hd, hu, hp, hq⟩. The shipped proof writes the witness and those six slots as one seven-component tuple; the refine here only exposes where the redex comes from.' },

        { t: 'p', h: 'The converse of <code>star_or_left</code> is also true and just as short, so <code>∗</code> genuinely distributes over <code>∨</code>:' },

        { t: 'code', tag: 'illustration',
          cap: 'Compiles against the M4 prelude. A case split on the outer disjunction rather than the inner one.',
          src: `theorem star_or_left_conv (P Q R : Assertion) :
    aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by
  intro σ h hor
  rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩
  · exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩` },

        { t: 'detail', title: 'The ∀ case, and why it only goes one way', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The forward direction is as easy as the existential one: introduce the quantified variable after destructuring and hand it to the hypothesis.' },
            { t: 'code', tag: 'illustration',
              src: `def aForall {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∀ x, P x σ h

theorem star_forall_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :
    aForall P ∗ Q ⊢ aForall (fun x => P x ∗ Q) := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩ x
  exact ⟨h₁, h₂, hd, hu, hp x, hq⟩` },
            { t: 'p', h: 'The converse fails, and the reason is the existential hiding inside <code>∗</code>. <code>aForall (fun x =&gt; P x ∗ Q)</code> says that for each <code>x</code> there is <i>some</i> cut; the cut may depend on <code>x</code>. <code>aForall P ∗ Q</code> demands a single cut that works for every <code>x</code> at once. Quantifier order, nothing more.' },
            { t: 'p', h: 'Here is the counterexample. Index by <code>Bool</code>, let <code>Pcx false</code> own cell 0 and <code>Pcx true</code> own cell 1, and take <code>aTrue</code> on the right to absorb whatever is left over. On the two-cell heap the left-hand side holds — cut one way for <code>false</code>, the other way for <code>true</code> — while the right-hand side would force one heap to be both singletons.' },
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M4 prelude. A refutation, not a failed proof attempt.',
              src: `def Pcx : Bool → Assertion
  | false => (0 ↦ 4)
  | true  => (1 ↦ 7)

theorem star_forall_right_fails :
    ¬ (aForall (fun x => Pcx x ∗ aTrue) ⊢ aForall Pcx ∗ aTrue) := by
  intro hcontra
  have hlhs : aForall (fun x => Pcx x ∗ aTrue) (fun _ => 0)
      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) := by
    intro x
    cases x with
    | false =>
        exact ⟨Heap.singleton 0 4, Heap.singleton 1 7,
          singleton_disjoint 4 7 (by simp), rfl, rfl, trivial⟩
    | true =>
        refine ⟨Heap.singleton 1 7, Heap.singleton 0 4,
          singleton_disjoint 7 4 (by simp), ?_, rfl, trivial⟩
        exact union_comm (singleton_disjoint 4 7 (by simp))
  obtain ⟨h₁, h₂, _, _, hall, _⟩ := hcontra _ _ hlhs
  have e0 : h₁ = Heap.singleton 0 4 := hall false
  have e1 : h₁ = Heap.singleton 1 7 := hall true
  have : Heap.singleton 0 4 0 = Heap.singleton 1 7 0 := by rw [← e0, ← e1]
  rw [singleton_same, singleton_other 1 0 7 (by simp)] at this
  exact absurd this (by simp)` },
            { t: 'p', h: 'The last four lines are the argument: <code>hall</code> gives two equations for <code>h₁</code>, so the two singletons are equal, and location 0 says <code>some 4 = none</code>. Two pieces of syntax appear here for the first time. <code>trivial</code> closes <code>aTrue σ h₂</code>, which is the slot where <code>aTrue</code> earns its keep — it absorbs a heap without saying anything about it. And <code>singleton_disjoint 4 7 (by simp)</code> passes the <i>values</i> explicitly while the locations are implicit, because M2 declared it that way for the sake of the other direction; <code>by simp</code> decides <code>0 ≠ 1</code> on numerals outright.' }
          ] }
      ],

      pitfall: 'Expecting <code>rcases</code> to fail because the hypothesis “is not an <code>Or</code>”. Its type displays as <code>aOr P Q σ h₁</code>, an opaque-looking application, and it is tempting to <code>unfold aOr</code> first. Not needed: <code>rcases</code> reduces the type to weak head normal form before matching. The same goes for <code>obtain</code> on <code>aExists</code> and for <code>subst</code> and <code>rw</code> on <code>emp</code> and <code>↦</code>.',

      variants: 'There is no <code>star_or_right</code> in the corpus because <code>star_comm</code> and <code>star_or_left</code> give it in two lines. Replace <code>∨</code> by <code>∧</code> and the forward statement <code>(aAnd P Q) ∗ R ⊢ aAnd (P ∗ R) (Q ∗ R)</code> is still true: both conjuncts hold at the same <code>h₁</code>, so you hand the same four slots to each half. Its converse is <b>false</b>, and the witness is already above — take <code>P = 0 ↦ 4</code>, <code>Q = 1 ↦ 7</code>, <code>R = aTrue</code> and the two-cell heap. <code>(P ∗ R)</code> holds by cutting one way, <code>(Q ∗ R)</code> by cutting the other, but <code>(aAnd P Q) ∗ R</code> needs one <code>h₁</code> equal to both singletons. That is literally the contradiction <code>star_forall_right_fails</code> derives, which is no coincidence: <code>∧</code> is a two-element <code>∀</code>. Two stars may hold with <i>different</i> cuts, and nothing forces them to agree.'
    },

    /* ================================================================
       8 — non-aliasing
       ================================================================ */

    { t: 'sec', s: 'Exercises · ownership implies non-aliasing' },

    { t: 'ex',
      id: 'm4-7',
      name: 'two_cells_distinct',
      hard: false,

      why: '<b>The punchline of Phase 1.</b> The precondition of a two-cell program already contains the non-aliasing information, so you never hypothesise it. Classical treatments of pointer programs carry side conditions like “assuming <code>x</code> and <code>y</code> do not alias”; here that assumption is a consequence of the precondition, which means it can neither be forgotten nor discharged separately. M10 cashes it in at once: <code>node_cells_distinct</code>, which says a two-field node has <code>p ≠ p + 1</code>, is <code>two_cells_distinct p (p + 1) x next</code> — one application, no proof.',

      setup: 'You need <code>singleton_disjoint_iff</code>, and nothing else. The conclusion is <code>fact</code>, not <code>pure</code>.',

      hints: [
        'The only thing in the hypothesis that could produce a disequality is the disjointness in slot 3. Name it, and discard slot 4 — the conclusion never mentions <code>h</code>.',
        'Slots 5 and 6 say the two pieces are literal singletons. Substitute them, so that <code>hd</code> becomes a statement about <code>Heap.singleton l₁ v₁</code> and <code>Heap.singleton l₂ v₂</code>.',
        '<code>subst hp; subst hq</code> — two on one line, separated by a semicolon. Then <code>hd</code> is exactly the left-hand side of <code>singleton_disjoint_iff</code>, and <code>.mp</code> finishes it.'
      ],

      goal: 'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)',

      sol: 'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩\n  subst hp; subst hq\n  exact (singleton_disjoint_iff v₁ v₂).mp hd',

      expl: 'All the work was done in M2. The star hands you <code>hd</code>, the two <code>subst</code>s turn it into disjointness of two singletons, and <code>singleton_disjoint_iff</code> converts that to <code>l₁ ≠ l₂</code>. The conclusion is <code>fact</code> because you are reading a fact off a heap you still hold; <code>pure</code> would additionally claim you own nothing, which is false and looks reasonable.',

      walk: [
        { tac: 'intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩', h: 'Slot 3 is the one that matters, so it gets a name; slot 4 is discarded.' },
        { tac: 'subst hp', h: '<code>hp : (l₁ ↦ v₁) σ h₁</code> is definitionally <code>h₁ = Heap.singleton l₁ v₁</code>. <code>subst</code> sees through <code>pointsTo</code> and eliminates <code>h₁</code>, so every occurrence — including the one inside <code>hd</code> — becomes the explicit singleton.' },
        { tac: 'subst hq', h: 'Same for <code>h₂</code>. Afterwards <code>hd</code> mentions no heap variables at all.' },
        { tac: 'exact (singleton_disjoint_iff v₁ v₂).mp hd', h: 'The iff from M2, forward direction. The goal <code>fact (fun x =&gt; l₁ ≠ l₂) σ h</code> unfolds to exactly its conclusion, so <code>exact</code> takes it. The <i>values</i> are written out and the locations are not because M2 declared it <code>singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val)</code>, and explicit arguments must be supplied positionally even when inferable — <code>singleton_disjoint_iff.mp hd</code> is <code>Unknown constant `singleton_disjoint_iff.mp`</code> while <code>(singleton_disjoint_iff _ _).mp hd</code> is fine. M2 chose that split for the other direction, where <code>.mpr</code> is applied to a proof of <code>l₁ ≠ l₂</code> that mentions no values at all.' }
      ],

      deep: [
        { t: 'trace', title: 'two_cells_distinct — watch hd get more concrete',
          start: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nleft✝ : h = h₁.union h₂\nhp : (l₁ ↦ v₁) σ h₁\nhq : (l₂ ↦ v₂) σ h₂\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
          steps: [
            { tac: 'subst hp',
              state: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh h₂ : Heap\nhq : (l₂ ↦ v₂) σ h₂\nhd : (Heap.singleton l₁ v₁).disjoint h₂\nleft✝ : h = (Heap.singleton l₁ v₁).union h₂\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
              h: '<code>h₁</code> has vanished from the context, replaced everywhere by the singleton — including inside <code>hd</code>, the only place it mattered. The discarded slot 4 was rewritten too, under its inaccessible name.' },
            { tac: 'subst hq',
              state: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nleft✝ : h = (Heap.singleton l₁ v₁).union (Heap.singleton l₂ v₂)\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
              h: '<code>hd</code> is now literally the left-hand side of an M2 lemma.' },
            { tac: 'show l₁ ≠ l₂',
              state: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nleft✝ : h = (Heap.singleton l₁ v₁).union (Heap.singleton l₂ v₂)\n⊢ l₁ ≠ l₂',
              h: 'Not in the shipped proof, and worth typing once to watch the <code>fact</code> costume come off.' }
          ],
          done: 'No goals, after exact (singleton_disjoint_iff v₁ v₂).mp hd.' },

        { t: 'detail', title: 'Exactness is not what makes this theorem true', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The natural reading of the proof is “exact ownership gives you non-aliasing”. It is wrong, and worth breaking, because the correct version points at something you need in M8. Replace <code>pointsTo</code> by the “at least this” reading and non-aliasing <b>survives</b> — disjointness alone is enough:' },
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M4 prelude. The weaker points-to still forces the locations apart.',
              src: `def pointsToAtLeast (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v

theorem two_cells_distinct_atleast (l₁ l₂ : Loc) (v₁ v₂ : Val) :
    pointsToAtLeast l₁ v₁ ∗ pointsToAtLeast l₂ v₂ ⊢ fact (fun _ => l₁ ≠ l₂) := by
  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩ heq
  subst heq
  rcases hd l₁ with hn | hn
  · rw [hp] at hn; exact absurd hn (by simp)
  · rw [hq] at hn; exact absurd hn (by simp)` },
            { t: 'p', h: 'That is the pitfall below, done deliberately: the extra <code>heq</code> in the pattern works because the goal unfolds to <code>l₁ = l₂ → False</code>, and <code>hd l₁</code> then contradicts <code>hp</code> in one branch and <code>hq</code> in the other. Five lines instead of three, and no exactness anywhere.' },
            { t: 'p', h: 'What exactness is load-bearing for is the <i>absence</i> of weakening. Under the loose reading, <code>l ↦ v ∗ Q ⊢ l ↦ v</code> becomes provable for every <code>Q</code>, because the left piece’s cell survives into the union:' },
            { t: 'code', tag: 'illustration',
              cap: 'Compiles against the M4 prelude. Drop exactness and ownership becomes forgettable.',
              src: `theorem atleast_star_weakening (l : Loc) (v : Val) (Q : Assertion) :
    pointsToAtLeast l v ∗ Q ⊢ pointsToAtLeast l v := by
  intro σ h ⟨h₁, h₂, _, hu, hp, _⟩
  subst hu
  exact union_of_some h₂ hp` },
            { t: 'p', h: 'Three lines, because M1 already had the lemma. Compare <code>no_star_weakening</code> earlier in the chapter, which refutes the same shape for the exact points-to. So the slogan to keep is not that exactness gives you non-aliasing — disjointness gives you that — but that <b>exactness gives you the absence of weakening</b>: a resource you cannot silently forget. That absence is what forces the frame rule to exist.' }
          ] }
      ],

      pitfall: 'Proving the goal “directly” with <code>intro heq</code>, on the grounds that <code>l₁ ≠ l₂</code> is an implication into <code>False</code>. It works, and you then rediscover by hand the contradiction that <code>singleton_disjoint_iff</code> already packages. The habit to build is to look for the M2 lemma whose left-hand side matches a hypothesis you hold, rather than reasoning from the definitions.',

      variants: 'State the same thing with <code>aAnd</code> and it becomes <b>false</b>: at <code>l₁ = l₂</code> and <code>v₁ = v₂</code> both conjuncts describe the same one-cell heap perfectly well. M3’s <code>pointsTo_value_unique</code> pushes the other way in that setting, concluding <code>v₁ = v₂</code>. So the theorem is about <code>∗</code>, and <code>∧</code> kills it. What it is <i>not</i> about is exactness, as the aside above machine-checks. The single moving part is slot 3.'
    },

    /* ================================================================
       9 — the normalisation library
       ================================================================ */

    { t: 'sec', s: 'Exercises · a small normalisation library' },

    { t: 'p', h: 'Here the chapter changes character. Everything so far was proved by opening <code>star</code> up and moving heaps around; from here you compose lemmas you already have. If you find yourself typing <code>intro σ h ⟨…⟩</code> for something like <code>star_swap_middle</code>, stop — you are redoing settled work.' },

    { t: 'ex',
      id: 'm4-8',
      name: 'star_swap_middle, star_rotate_left/right, star_pure_left/right',
      hard: false,

      why: '<code>star_swap_middle</code> is what an algebra is for: built <i>from</i> associativity and commutativity rather than proved from scratch. The <code>pure</code> pair is how a side condition gets moved in and out of a separating conjunction, and you will meet its shape again rather than the lemma itself — M9 proves <code>pure_star_regroup : pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R</code>, which is <code>star_pure_left</code> with a frame threaded through, by the four moves you are about to write.',

      setup: 'You have <code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>star_comm</code>, <code>star_mono_left</code> and <code>entails_trans</code>. <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so destructuring it gives a <i>pair</i> in slot 5: the proposition, and the emptiness of the heap.',

      goal: 'theorem star_swap_middle  (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R)\ntheorem star_rotate_left  (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R\ntheorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)\n\ntheorem star_pure_left  (φ : Store → Prop) (P : Assertion) : pure φ ∗ P ⊢ aAnd (fact φ) P\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) : aAnd (fact φ) P ⊢ pure φ ∗ P',

      hints: [
        'The two <code>rotate</code> lemmas are renamings of the associativity lemmas. Write them in term mode with no <code>by</code>.',
        '<code>star_swap_middle</code>: rotate left, swap the first two with <code>star_mono_left … (star_comm …)</code>, rotate back. Write the three intermediate assertions down before you type any lemma names.',
        'For <code>star_pure_left</code>: slot 5 is itself a pair, so write <code>⟨hφ, he⟩</code> there. Then <code>subst</code> the emptiness, rewrite the goal’s heap, and pair up what is left.',
        'For <code>star_pure_right</code>: the cut is forced, <code>Heap.empty</code> on the left. Slot 5 must prove <code>pure φ σ Heap.empty</code>, which is a pair, <code>⟨hφ, rfl⟩</code>.'
      ],

      sol: 'theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=\n  entails_trans (star_assoc_right P Q R)\n    (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))\n\ntheorem star_rotate_left (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=\n  star_assoc_right P Q R\n\ntheorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) :=\n  star_assoc_left P Q R\n\ntheorem star_pure_left (φ : Store → Prop) (P : Assertion) :\n    pure φ ∗ P ⊢ aAnd (fact φ) P := by\n  intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩\n  subst he\n  rw [hu, union_empty_left]\n  exact ⟨hφ, hp⟩\n\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) :\n    aAnd (fact φ) P ⊢ pure φ ∗ P := by\n  intro σ h ⟨hφ, hp⟩\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩',

      expl: '<code>star_swap_middle</code> is three lemmas glued by two <code>entails_trans</code>, with no <code>intro</code>, no heap and no <code>⟨…⟩</code> in it. When your separation-logic proofs start looking like that, you have stopped grinding semantics and started using the logic.',

      walk: [
        { tac: 'entails_trans (star_assoc_right P Q R)', h: 'Step one: <code>P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R</code>. Re-bracket so that the two assertions you want to exchange sit inside one sub-star.' },
        { tac: '(entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))', h: 'Steps two and three, nested. <code>star_comm P Q</code> swaps them and <code>star_mono_left R</code> lifts that entailment to hold underneath the frame <code>R</code>, giving <code>(P ∗ Q) ∗ R ⊢ (Q ∗ P) ∗ R</code>; then <code>star_assoc_left Q P R</code> re-brackets to the shape the statement wants.' },
        { tac: 'theorem star_rotate_left … := star_assoc_right P Q R', h: 'A renaming, worth having because at the point of use “rotate” describes what you are doing to a precondition while “assoc” names a law.' },
        { tac: 'theorem star_rotate_right … := star_assoc_left P Q R', h: 'Note the crossing: <code>rotate_left</code> is <code>assoc_right</code>, because one name describes the movement and the other the destination bracketing.' },
        { tac: 'intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩', h: 'Slot 5 has type <code>pure φ σ h₁</code>, which is a conjunction, hence the nested pair: the proposition and the emptiness of <code>h₁</code>. Slot 3 is discarded — two heaps one of which is empty are automatically disjoint, so it carries nothing.' },
        { tac: 'subst he', h: 'Eliminates <code>h₁</code>, so <code>hu</code> becomes <code>h = Heap.empty.union h₂</code> and <code>hφ</code> is restated at <code>Heap.empty</code>.' },
        { tac: 'rw [hu, union_empty_left]', h: 'The goal’s heap shrinks from <code>h</code> to <code>h₂</code> — the piece <code>P</code> owns, which is the point: <code>pure</code> contributed nothing.' },
        { tac: 'exact ⟨hφ, hp⟩', h: 'An <code>aAnd</code> is a pair. <code>hφ : fact φ σ Heap.empty</code> is accepted against <code>fact φ σ h₂</code> because <code>fact</code> never reads its heap argument, so the two types are definitionally equal.' },
        { tac: 'intro σ h ⟨hφ, hp⟩', h: 'The converse. An ordinary conjunction, so two names.' },
        { tac: 'exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩', h: 'Slots 1–4 are exactly <b>m4-2</b>. Slot 5 supplies the two halves of <code>pure</code>: <code>hφ</code> and <code>rfl</code>. Slot 6 is <code>hp</code>, still holding the entire heap.' }
      ],

      deep: [
        { t: 'steps', title: 'star_swap_middle as a chain — write the intermediate assertions first',
          items: [
            { k: 'Start', h: '<code>P ∗ (Q ∗ R)</code>' },
            { k: '<code>star_assoc_right P Q R</code>', h: '<code>(P ∗ Q) ∗ R</code> — bring <code>P</code> and <code>Q</code> next to each other inside one bracket.' },
            { k: '<code>star_mono_left R (star_comm P Q)</code>', h: '<code>(Q ∗ P) ∗ R</code> — swap them without disturbing <code>R</code>. The only step that does work, and it does it by reusing <code>star_comm</code> at a smaller scope.' },
            { k: '<code>star_assoc_left Q P R</code>', h: '<code>Q ∗ (P ∗ R)</code> — re-bracket back.' },
            { k: 'Glue', h: 'Two <code>entails_trans</code>, nested to the right.' }
          ] },

        { t: 'state', cap: 'The three steps as Lean sees them, written out with have. Note P ∗ Q ∗ R is P ∗ (Q ∗ R).',
          src: 'P Q R : Assertion\ns1 : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R\ns2 : (P ∗ Q) ∗ R ⊢ (Q ∗ P) ∗ R\ns3 : (Q ∗ P) ∗ R ⊢ Q ∗ P ∗ R\n⊢ P ∗ Q ∗ R ⊢ Q ∗ P ∗ R' },

        { t: 'trace', title: 'star_pure_left, tactic by tactic',
          start: 'φ : Store → Prop\nP : Assertion\n⊢ _root_.pure φ ∗ P ⊢ aAnd (fact φ) P',
          steps: [
            { tac: 'intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩',
              state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhφ : fact φ σ h₁\nhe : emp σ h₁\nhp : P σ h₂\n⊢ aAnd (fact φ) P σ h',
              h: 'Seven names for a star whose left conjunct is a conjunction: the nested pattern in slot 5 produced two hypotheses where the six-slot pattern would have produced one. The flattening goes as deep as you write brackets.' },
            { tac: 'subst he',
              state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₂ : Heap\nhp : P σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhφ : fact φ σ Heap.empty\n⊢ aAnd (fact φ) P σ h',
              h: 'Watch <code>hφ</code>: it is now stated at <code>Heap.empty</code>, and that will not matter, because <code>fact</code> discards its heap argument. This is the mechanism the whole <code>pure</code> pair runs on.' },
            { tac: 'rw [hu, union_empty_left]',
              state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₂ : Heap\nhp : P σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhφ : fact φ σ Heap.empty\n⊢ aAnd (fact φ) P σ h₂',
              h: 'Both remaining obligations now live at <code>h₂</code>, and both are in the context.' }
          ],
          done: 'No goals, after exact ⟨hφ, hp⟩.' },

        { t: 'trace', title: 'star_pure_right — the forced cut',
          start: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh : Heap\nhφ : fact φ σ h\nhp : P σ h\n⊢ (_root_.pure φ ∗ P) σ h',
          steps: [
            { tac: 'refine ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ?_, hp⟩',
              state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh : Heap\nhφ : fact φ σ h\nhp : P σ h\n⊢ _root_.pure φ σ Heap.empty',
              h: 'One obligation, and it is the interesting one: <code>pure φ</code> must hold at the <b>empty</b> heap. It unfolds to <code>fact φ σ Heap.empty ∧ Heap.empty = Heap.empty</code>, so <code>⟨hφ, rfl⟩</code> closes it, with <code>hφ</code> transporting from <code>h</code> for free.' }
          ],
          done: 'No goals, after exact ⟨hφ, rfl⟩. The shipped proof writes that pair inline in slot 5; the hole here only exposes what slot 5 was asking for.' },

        { t: 'cmp',
          left: { t: 'star_swap_middle from scratch', kind: 'bad',
                  h: 'Destructure two nested stars, produce three heaps, derive three pairwise disjointness facts, choose a new cut, and prove <code>h = hQ ∪ (hP ∪ hR)</code> from <code>h = hP ∪ (hQ ∪ hR)</code> with two <code>union_assoc</code> and one <code>union_comm</code> carrying the right disjointness proof. Fifteen lines, every one of which can go wrong.' },
          right: { t: 'Composing three lemmas', kind: 'good',
                   h: 'Three lines, no heaps. Every heap-level fact it needs was proved and named two chapters ago. This is the working style of every chapter from M9 on.',
                   tag: 'sketch',
                   src: 'entails_trans (star_assoc_right P Q R)\n  (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))' } }
      ],

      pitfall: 'Mixing up which rotate is which. <code>star_rotate_left</code> has the <i>right</i>-associated assertion as its hypothesis and is defined as <code>star_assoc_right</code>. Assume the names line up and you build a term whose type is the converse of what you need, and the error surfaces at the <code>entails_trans</code> that consumes it rather than at the definition. Write the intermediate assertions down first, then pick names.',

      variants: 'Replace <code>pure φ</code> by <code>fact φ</code> in <code>star_pure_left</code> and it becomes <b>false</b>: without the <code>emp</code> component you never learn that <code>h₁</code> is empty, <code>hu</code> gives you nothing, and <code>P σ h</code> is out of reach from <code>hp : P σ h₂</code>. The refutation is <code>no_star_weakening</code>’s argument with the same numbers — take <code>φ</code> trivially true and <code>P = 1 ↦ 7</code>, and let <code>fact φ</code> hold at the cell at <code>0</code> in the two-cell heap. In the other direction <code>star_pure_right</code> with <code>fact</code> stays true, since you may always cut off <code>Heap.empty</code>, but it is useless: <code>fact φ ∗ P</code> does not pin the cut, so nothing can be recovered from it. That asymmetry is exactly which of the two embeddings pairs with which connective.'
    },

    /* ================================================================
       10 — close
       ================================================================ */

    { t: 'sec', s: 'What you now have' },

    { t: 'tbl',
      cap: '“Next appearance” means an actual later use in the development. The ones that never come back are marked as such, which is worth knowing too.',
      head: ['Law', 'Lemma(s)', 'Next appearance'],
      rows: [
        ['unit', '<code>star_emp_left</code>', 'M9 <code>moveCell_spec</code> — <code>free</code> leaves <code>emp ∗ (dst ↦ a)</code>'],
        ['unit, converses', '<code>star_emp_right</code>, <code>star_emp_*_intro</code>', 'not reused — they exist to make <code>⊣⊢</code> true, and to teach the construction side'],
        ['commutative', '<code>star_comm</code>', 'M4 <code>star_swap_middle</code>; M9 <code>copyCell_spec</code>, twice'],
        ['associative', '<code>star_assoc_left/right</code>', 'M9 <code>copyCell_spec</code>; M10 <code>lseg_append</code> and <code>lseg_listRep</code>, twice each'],
        ['monotone', '<code>star_mono</code>, <code>star_mono_left/right</code>', 'M9 <code>copyCell_spec</code>; M10, four times in the two list proofs'],
        ['distributes over <code>∃</code>', '<code>star_exists_left</code>', 'M10 — opens the <code>∃ next</code> under every cons'],
        ['distributes over <code>∨</code>', '<code>star_or_left</code>', 'not reused — but it is what makes case analysis under <code>∗</code> legal at all'],
        ['non-aliasing', '<code>two_cells_distinct</code>', 'M10 <code>node_cells_distinct</code> — one application, no proof'],
        ['normalisation', '<code>star_swap_middle</code>, <code>star_rotate_*</code>, <code>star_pure_*</code>', 'the <i>shape</i> returns as M9’s <code>pure_star_regroup</code>; the lemmas are your own toolkit'],
        ['<i>no</i> weakening', '<code>no_star_weakening</code> (illustration)', 'M8 — why the frame rule carries <code>R</code> rather than dropping it']
      ] },

    { t: 'p', h: 'The theorem all of this was for is M8’s:' },

    { t: 'code', tag: 'sketch',
      cap: 'Five names on that statement. <code>∗</code> is the only one that exists.',
      src: `theorem hoare_frame {P Q R : Assertion} {c : Cmd}
    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :
    Hoare (P ∗ R) c (Q ∗ R)` },

    { t: 'p', h: 'Every law in this chapter chooses its own cut, or is handed one and keeps it. The frame rule does neither: <code>c</code> chooses. Running the command turns <code>P</code>’s piece into <code>Q</code>’s piece and must leave <code>R</code>’s piece exactly as it was — and nothing in M4 can say what “leave as it was” means, because nothing in M4 runs. <code>hlocal</code> and <code>hpres</code> are the two conditions that will say it, and both are conditions on a command.' },

    { t: 'p', h: 'So M5 builds the language: what a command is, and what relation takes one state to another when you run one. It does not mention <code>∗</code> once. The two threads meet in M6 and M7, where a triple is defined over that relation and its rules are stated with the connective you have just finished.' },

    { t: 'dod', h: '<code>∗</code> is associative, commutative, monotone, distributes over <code>∨</code> and <code>∃</code>, has <code>emp</code> as unit, and admits no projection. Assertions with <code>∗</code> and <code>emp</code> are a commutative monoid, and you have the assertion-level core of separation logic.' }

  ]
});
