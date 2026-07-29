/* M4 — Separating conjunction
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  id: 'm4',
  num: 'M4',
  phase: 'Phase 1 · Semantic foundations',
  title: 'Separating conjunction',
  blurb: 'The connective. Its definition, its laws, and the proof that ∗ makes assertions a commutative monoid.',

  orient: {
    youWill: [
      'Read and write the definition of <code>∗</code> and say, without hesitating, what its six components are.',
      'Take a star hypothesis apart in one <code>intro</code> pattern, and build a star goal in one <code>exact ⟨…⟩</code>.',
      'Prove that <code>∗</code> is commutative, associative, monotone, has <code>emp</code> as unit, and distributes over <code>∨</code> and <code>∃</code>.',
      'Derive <code>l₁ ≠ l₂</code> from <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂</code> — non-aliasing as a <i>theorem</i>, not a hypothesis.',
      'Chain lemmas with <code>entails_trans</code> so that later proofs never touch a heap again.'
    ],
    needs: [
      'M2: <code>Heap.disjoint</code>, <code>Heap.union</code>, and the lemmas <code>disjoint_symm</code>, <code>disjoint_empty_left/right</code>, <code>union_empty_left/right</code>, <code>union_assoc</code>, <code>union_comm</code>, <code>disjoint_union_left/right</code>, <code>singleton_disjoint_iff</code>.',
      'M3: <code>Assertion</code>, <code>Entails</code> (<code>⊢</code>), <code>emp</code>, <code>pointsTo</code> (<code>↦</code>), <code>fact</code>, <code>pure</code>, <code>entails_refl</code>, <code>entails_trans</code>.',
      'M0: the anonymous constructor <code>⟨…⟩</code> and its automatic flattening. That one piece of syntax carries this entire chapter.'
    ],
    payoff: 'Everything from M7 onward is stated in terms of <code>∗</code>. The frame rule of M8 reads <code>Hoare (P ∗ R) c (Q ∗ R)</code>, and its proof is the move you learn here and nothing else: <code>obtain ⟨hP, hR, hd, hu, hp, hr⟩</code> on the precondition, then a six-slot <code>refine</code> to rebuild the postcondition. From M9 on, lining a precondition up with a command’s footprint is a chain of <code>entails_trans</code> through <code>star_assoc_left</code>, <code>star_comm</code> and <code>star_mono_right</code> — this chapter’s lemmas, used as an algebra.'
  },

  blocks: [
    /* ─────────────────────────────────────────────  The idea  ───────── */
    {t: 'h3', s: 'The idea'},

    {t: 'p', h: 'M2 built a partial commutative monoid out of heaps. M3 built assertions and the ordinary connectives. This chapter is the join: <b>every PCM induces one new connective</b>, and that connective is what separation logic is about. Everything else in the course is downstream of the three lines below.'},

    {t: 'code', src: 'def star (P Q : Assertion) : Assertion :=\n  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂\ninfixr:55 " ∗ " => star'},

    {t: 'anat',
     src: 'def star (P Q : Assertion) : Assertion :=\n  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂\ninfixr:55 " ∗ " => star',
     parts: [
       {m: 'fun σ h =>', h: '<code>Assertion</code> is <code>Store → Heap → Prop</code>, so defining a new assertion means producing a function of a store and a heap. <code>σ</code> is passed through untouched: <code>∗</code> splits the <i>heap</i> and never the store. Variables are not a resource in this logic.'},
       {m: '∃ h₁ h₂', h: 'The cut is <b>existentially quantified</b>, not given. This is the single most important design decision in the chapter. <code>(P ∗ Q) σ h</code> does not say “here is how to split <code>h</code>”; it says “<i>some</i> split works”. Consequence: to <i>prove</i> a star you must invent the split; to <i>use</i> one you receive a split you did not choose and must work with it as given.'},
       {m: 'Heap.disjoint h₁ h₂', h: 'The two pieces do not overlap. Without this the connective would be useless — <code>P</code> and <code>Q</code> could both claim the same cell, and “separating” would separate nothing.'},
       {m: 'h = Heap.union h₁ h₂', h: 'The pieces reassemble to exactly <code>h</code>. Note the <b>direction</b>: whole on the left, union on the right. Lean will not silently flip an equation for you, and this is the single most common source of friction below — all three <code>.symm</code>s in the solutions of this chapter exist only because of this orientation.'},
       {m: 'P σ h₁ ∧ Q σ h₂', h: 'Each conjunct is evaluated at its <i>own</i> piece. Compare <code>aAnd P Q = fun σ h => P σ h ∧ Q σ h</code>, where both are evaluated at the same <code>h</code>. That one substitution is the whole difference between <code>∧</code> and <code>∗</code>.'},
       {m: 'infixr:55', h: '<code>∗</code> is right-associative with precedence 55. Two consequences you will see in every goal display: <code>P ∗ (Q ∗ R)</code> prints as <code>P ∗ Q ∗ R</code> with no parentheses, while <code>(P ∗ Q) ∗ R</code> keeps them; and since <code>↦</code> is <code>infix:60</code> and <code>⊢</code> is <code>infix:40</code>, the expression <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂ ⊢ P</code> parses as <code>((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) ⊢ P</code> with no help from you.'}
     ]},

    {t: 'p', h: 'In words: <b><code>(P ∗ Q) σ h</code> holds when you can cut <code>h</code> into two disjoint pieces, one satisfying <code>P</code> and the other satisfying <code>Q</code>.</b>'},

    {t: 'svg', src: '\n<svg viewBox="0 0 560 150" role="img" aria-label="P and Q versus P star Q">\n  <g class="dg">\n    <text x="12" y="20" class="dg-lab">P ∧ Q — both describe the whole heap</text>\n    <rect x="12" y="30" width="230" height="36" rx="7" class="dg-box"/>\n    <text x="127" y="53" text-anchor="middle" class="dg-t">h</text>\n    <path class="dg-arr thin" d="M40 76 L 40 66"/><text x="46" y="86" class="dg-note">P sees all of h</text>\n    <path class="dg-arr thin" d="M40 106 L 40 96"/><text x="46" y="116" class="dg-note">Q sees all of h</text>\n\n    <text x="308" y="20" class="dg-lab">P ∗ Q — each owns its own piece</text>\n    <rect x="308" y="30" width="112" height="36" rx="7" class="dg-box a"/>\n    <text x="364" y="53" text-anchor="middle" class="dg-t">h₁</text>\n    <rect x="428" y="30" width="112" height="36" rx="7" class="dg-box b"/>\n    <text x="484" y="53" text-anchor="middle" class="dg-t">h₂</text>\n    <text x="364" y="86" text-anchor="middle" class="dg-note">P owns h₁</text>\n    <text x="484" y="86" text-anchor="middle" class="dg-note">Q owns h₂</text>\n    <text x="424" y="118" text-anchor="middle" class="dg-note">h₁ and h₂ disjoint, h = h₁ ∪ h₂</text>\n  </g>\n</svg>'},

    {t: 'p', h: 'Contrast with <code>∧</code>. In <code>P ∧ Q</code> both conjuncts talk about the <i>same</i> heap. In <code>P ∗ Q</code> they talk about <i>complementary</i> heaps. So'},

    {t: 'txt', src: '  (10 ↦ 4) ∗ (20 ↦ 7)   the heap is exactly two cells, at 10 and at 20\n  (10 ↦ 4) ∗ (10 ↦ 7)   unsatisfiable — the two halves would have to be\n                        disjoint and both contain location 10'},

    {t: 'p', h: '“Unsatisfiable” is a claim, so prove it. This is not an exercise; it is a two-line consequence of M2 that you can read now, and it is the first time the logic <i>refutes</i> something for you rather than merely describing it.'},

    {t: 'code', tag: 'illustration',
     cap: 'Two cells at the same location: not merely unlikely, but absurd.',
     src: 'theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :\n    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩\n  subst hp; subst hq\n  exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl'},

    {t: 'p', h: 'Read the last line right to left: <code>hd</code> is the disjointness the star handed you; <code>singleton_disjoint_iff</code> turns it into <code>l ≠ l</code>, which is by definition <code>l = l → False</code>; feeding it <code>rfl</code> produces the <code>False</code> the goal wanted. Nothing about programs, nothing about pointers — just the monoid.'},

    {t: 'cmp',
     left:  {t: 'What a mathematician writes', kind: 'good',
             h: '“Let <code>h = h₁ ⊎ h₂</code> with <code>P(h₁)</code> and <code>Q(h₂)</code>.” The symbol <code>⊎</code> quietly does three jobs at once: it asserts disjointness, it forms the union, and it names the decomposition. On paper that is fine, because you can see all three at a glance.'},
     right: {t: 'What Lean needs',
             h: 'A total function <code>Heap.union</code> that is defined even for overlapping heaps (M2 made it left-biased for exactly this reason), a <i>separate</i> proposition <code>Heap.disjoint h₁ h₂</code>, and a <i>separate</i> equation <code>h = Heap.union h₁ h₂</code>. Three components where paper has one operator. That is why every star carries six things and not four.',
             tag: 'sketch',
             src: '∃ h₁ h₂, Heap.disjoint h₁ h₂\n        ∧ h = Heap.union h₁ h₂\n        ∧ P σ h₁ ∧ Q σ h₂'}},

    {t: 'detail', title: 'Why not define ∗ using Heap.splits?', tag: 'aside', open: false,
     blocks: [
       {t: 'p', h: 'M2 already defined <code>Heap.splits whole left right := Heap.disjoint left right ∧ whole = Heap.union left right</code>, which packages exactly the two middle components. So why does <code>star</code> not say <code>∃ h₁ h₂, Heap.splits h h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>?'},
       {t: 'p', h: 'It could, and the two definitions are trivially interprovable. The reason the workbook spells it out is <b>the shape of the anonymous constructor</b>. With the flat version, <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code> destructures a star in one pattern with six names. With <code>Heap.splits</code> in the middle you would write <code>⟨h₁, h₂, ⟨hd, hu⟩, hp, hq⟩</code> — an extra bracket level in every single proof in this chapter and in M7–M13. Lean flattens nested right-associated <code>∧</code> and <code>∃</code> automatically; it does not flatten a named structure.'},
       {t: 'p', h: 'The rejected alternative that <i>would</i> break things is making <code>union</code> partial — say <code>Heap.union (h₁ h₂ : Heap) (hd : Heap.disjoint h₁ h₂) : Heap</code>. Then the heap in <code>h = Heap.union h₁ h₂ hd</code> mentions a <i>proof</i>, so two heaps built from the same pieces with different disjointness proofs are only equal up to proof irrelevance, and every rewrite drags the proof term along. M2 chose totality plus a side hypothesis for precisely this reason, and M4 is where you collect the dividend.'}
     ]},

    {t: 'note', kind: 'key', title: 'The one thing to remember',
     h: 'Non-aliasing is <b>derived</b>, not assumed. Writing <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂</code> already <i>proves</i> <code>l₁ ≠ l₂</code>. That single fact is why separation logic scales: the side conditions that used to be hypotheses have become theorems about your precondition.'},

    /* ────────────────────────────  Proving and consuming  ───────────── */
    {t: 'h3', s: 'How to prove and consume a star'},

    {t: 'p', h: 'This is entirely mechanical, and knowing the two moves is 80% of writing these proofs.'},

    {t: 'txt', src: '  to PROVE  (P ∗ Q) σ h :\n      supply  ⟨h₁, h₂, hdisj, hunion, hP, hQ⟩\n      i.e. the two pieces, their disjointness, h = h₁ ∪ h₂, and the two facts\n\n  to USE    hstar : (P ∗ Q) σ h :\n      obtain ⟨h₁, h₂, hdisj, hunion, hP, hQ⟩ := hstar'},

    {t: 'p', h: 'The six slots are always in the same order, because they are the six components of the definition read left to right. Learn them once:'},

    {t: 'dl', items: [
      {k: '1 · <code>h₁</code>', h: 'The heap the <i>left</i> conjunct owns. When proving, this is a heap you choose; when using, a heap you are given.'},
      {k: '2 · <code>h₂</code>', h: 'The heap the <i>right</i> conjunct owns.'},
      {k: '3 · <code>hd : Heap.disjoint h₁ h₂</code>', h: 'Prints in the goal as <code>h₁.disjoint h₂</code> — Lean uses dot notation for anything in the <code>Heap</code> namespace applied to a <code>Heap</code>. Same proposition, shorter display.'},
      {k: '4 · <code>hu : h = Heap.union h₁ h₂</code>', h: 'Prints as <code>h = h₁.union h₂</code>. The <b>whole is on the left</b>. Every <code>.symm</code> in the solutions below is a consequence of this orientation.'},
      {k: '5 · <code>hp : P σ h₁</code>', h: 'The left conjunct, at the left piece.'},
      {k: '6 · <code>hq : Q σ h₂</code>', h: 'The right conjunct, at the right piece.'}
    ]},

    {t: 'p', h: 'Two syntactic points that the workbook uses constantly and never announces. First, <code>intro σ h ⟨…⟩</code> is <code>intro σ h hstar</code> followed by <code>obtain ⟨…⟩ := hstar</code>, fused into one line; <code>intro</code> accepts a destructuring pattern wherever it accepts a name. Second, the pattern has six names for a statement that is <i>syntactically</i> a two-level existential wrapping a three-level conjunction — <code>⟨…⟩</code> flattens right-nested <code>∃</code> and <code>∧</code> automatically, so you never write the inner brackets.'},

    {t: 'trace', title: 'Destructuring a star, in slow motion',
     start: 'P Q : Assertion\nσ : Store\nh : Heap\nhstar : (P ∗ Q) σ h\n⊢ (Q ∗ P) σ h',
     steps: [
       {tac: 'obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hstar',
        state: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (Q ∗ P) σ h',
        h: 'One hypothesis became six. Two new heaps entered the context, and <code>h</code> is now related to them by <code>hu</code>. Nothing has been proved yet — this is pure bookkeeping, and it is the first line of almost every proof in this chapter.'}
     ],
     done: 'The goal is untouched: destructuring the hypothesis never changes the goal.'},

    {t: 'p', h: 'The goal side is the mirror image. Notice above that the goal still displays as <code>(Q ∗ P) σ h</code> — folded, with <code>star</code> not unfolded. Lean is perfectly happy to accept <code>exact ⟨…⟩</code> against it anyway, because <code>star</code> is a <code>def</code> and the anonymous constructor elaborates up to definitional unfolding. If you want to <i>see</i> what you owe, ask:'},

    {t: 'code', tag: 'illustration',
     cap: 'show does nothing logically; it makes the obligation visible.',
     src: 'example (P : Assertion) : P ⊢ emp ∗ P := by\n  intro σ h hp\n  show ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ emp σ h₁ ∧ P σ h₂\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩'},

    {t: 'state', cap: 'The goal after that show — the six slots, spelled out.',
     src: 'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ emp σ h₁ ∧ P σ h₂'},

    {t: 'p', h: 'Every proof below is: destructure the hypothesis, shuffle the heaps, reassemble the goal. The <i>only</i> creativity is choosing how to cut the heap in the goal.'},

    {t: 'note', kind: 'tip', title: 'The tactic that makes the six slots visible',
     h: 'When you cannot see which of the six components is failing, replace <code>exact ⟨a, b, c, d, e, f⟩</code> by <code>refine ⟨a, b, ?_, ?_, ?_, ?_⟩</code>. <code>refine</code> is <code>exact</code> with holes: every <code>?_</code> becomes a separate goal, named <code>case refine_1</code>, <code>case refine_2</code>, and so on, in order. You then attack them one at a time with <code>·</code> bullets. Five of the traces below — in <b>m4-2</b>, <b>m4-3</b>, <b>m4-5</b>, <b>m4-6</b> and <b>m4-8</b> — use this trick purely to expose intermediate states. In each of those the shipped proof supplies exactly the same components inside one <code>exact</code>; the trace says so where it happens. Only <b>m4-4</b> really is a <code>refine</code> proof.'},

    {t: 'detail', title: 'Reading Lean’s goal display in this chapter', tag: 'aside', open: false,
     blocks: [
       {t: 'p', h: 'Four printing conventions will otherwise trip you up. None of them changes the mathematics; all of them change what you see.'},
       {t: 'dl', items: [
         {k: '<code>h₁.disjoint h₂</code>', h: 'is <code>Heap.disjoint h₁ h₂</code>. Lean prints <code>Namespace.f x …</code> as <code>x.f …</code> whenever <code>x</code> has type <code>Namespace</code>. Your source may say either; the display always says the short one.'},
         {k: '<code>P ∗ Q ∗ R</code>', h: 'is <code>P ∗ (Q ∗ R)</code>, because <code>∗</code> is <code>infixr</code>. The <i>other</i> bracketing prints as <code>(P ∗ Q) ∗ R</code>. So in the associativity exercise the two sides of the goal look asymmetric even though the statement is symmetric.'},
         {k: '<code>left✝</code>', h: 'is the name Lean invents when you write <code>_</code> in a destructuring pattern. The dagger marks it <i>inaccessible</i>: it is in the context, it is being used to typecheck the term, but you cannot refer to it by name. The word <code>left</code> is not a description of where the slot was — it is the <i>field name</i> of the <code>∧</code> that slot came from, <code>And.left</code>. That is why the discarded component shows up as <code>left✝</code> in <b>m4-1</b> (slot 3), in <b>m4-7</b> (slot 4) and in <b>m4-8</b> (slot 3) alike. If you find you need it after all, go back and give it a real name.'},
         {k: '<code>_root_.pure φ</code>', h: 'is our <code>pure</code> from M3. The prefix appears because Lean’s own <code>Pure.pure</code> (the monad operation) is also in scope, so the pretty-printer disambiguates. Nothing is wrong; do not go looking for a second definition.'}
       ]}
     ]},

    {t: 'p', h: 'Finally, the toolbox. Every heap-level obligation in the eight exercises below is discharged by one of these eight rows, and by nothing else. (The refutations in the chapter body reach a little further into M1 — <code>singleton_same</code>, <code>singleton_other</code>, <code>union_of_none</code> — because refuting an entailment means evaluating a concrete heap at a concrete location, which the exercises never do.) If a proof below is not going through, the question to ask is “which row of this table am I missing?”'},

    {t: 'tbl',
     cap: 'The M2 lemmas that do all the heap work in M4.',
     head: ['Lemma', 'Statement', 'Used for'],
     rows: [
       ['<code>disjoint_symm</code>', '<code>Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁</code>', 'commutativity'],
       ['<code>union_comm hd</code>', '<code>Heap.union h₁ h₂ = Heap.union h₂ h₁</code>, given <code>hd</code>', 'commutativity — the one place disjointness is <i>needed</i>'],
       ['<code>union_assoc</code>', '<code>(h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃)</code>, <b>no hypothesis</b>', 'associativity'],
       ['<code>disjoint_union_left</code>', '<code>(h₁ ∪ h₂) ⟂ h₃ ↔ h₁ ⟂ h₃ ∧ h₂ ⟂ h₃</code>', 'taking apart / building up disjointness when re-bracketing'],
       ['<code>disjoint_union_right</code>', '<code>h₁ ⟂ (h₂ ∪ h₃) ↔ h₁ ⟂ h₂ ∧ h₁ ⟂ h₃</code>', 'the mirror image'],
       ['<code>union_empty_left / right</code>', '<code>Heap.empty ∪ h = h</code>, <code>h ∪ Heap.empty = h</code>', 'the unit laws'],
       ['<code>disjoint_empty_left / right</code>', '<code>Heap.empty ⟂ h</code>, <code>h ⟂ Heap.empty</code>', 'the unit laws'],
       ['<code>singleton_disjoint_iff v₁ v₂</code>', '<code>Heap.singleton l₁ v₁ ⟂ Heap.singleton l₂ v₂ ↔ l₁ ≠ l₂</code>', 'non-aliasing']
     ]},

    {t: 'note', kind: 'info', title: 'Notation in the prose only',
     h: 'The symbol <code>⟂</code> in that table — and in the prose of this chapter wherever a line of disjointness reasoning would otherwise not fit — is shorthand for <code>Heap.disjoint</code>. It is <b>not</b> Lean notation and does not exist in the development: in Lean you always write <code>Heap.disjoint h₁ h₂</code>, and Lean prints it back as <code>h₁.disjoint h₂</code>. Likewise <code>∪</code> in the prose is <code>Heap.union</code>.'},

    /* ──────────────────────────────  emp is the unit  ───────────────── */
    {t: 'sec', s: 'Exercises · emp is the unit'},

    {t: 'ex',
     id: 'm4-1',
     name: 'star_emp_left / star_emp_right',
     hard: false,

     why: 'Your first two proofs that <i>consume</i> a star. They are also the first place you learn something that is easy to miss: the <code>emp</code> conjunct is not a fact about <code>P</code> — it is a <b>heap equation</b> in disguise, and it is only useful once you rewrite with it. The three-tactic pattern <code>subst</code> the emptiness, <code>rw [hu, union_empty_left]</code>, finish is one you will write again: M9’s <code>moveCell_spec</code> ends with <code>star_emp_left</code> applied to the <code>emp ∗ (dst ↦ a)</code> that freeing a cell leaves behind, and both base cases of M10’s <code>lseg_append</code> and <code>lseg_listRep</code> are this proof written out by hand.',

     setup: 'In scope: everything from M2 and M3, plus <code>star</code>. You will want <code>union_empty_left</code> and <code>union_empty_right</code>. Recall <code>emp : Assertion := fun _ h => h = Heap.empty</code>.',

     goal: 'theorem star_emp_left  (P : Assertion) : emp ∗ P ⊢ P\ntheorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P',

     hints: [
       'The statement is an <code>Entails</code>, which unfolds to <code>∀ σ h, (emp ∗ P) σ h → P σ h</code>. So the proof opens with <code>intro</code> taking three things: the store, the heap, and the star hypothesis.',
       'Destructure the star hypothesis in the same <code>intro</code>, with six names. You do not need the disjointness component here — pass <code>_</code> in its slot.',
       'Look at what the <code>emp</code> slot gives you: <code>he : emp σ h₁</code>, which <i>is</i> the equation <code>h₁ = Heap.empty</code>. And <code>hu : h = Heap.union h₁ h₂</code>. The goal is <code>P σ h</code>; rewrite the <code>h</code> in the goal until it becomes <code>h₂</code>.',
       'Three rewrites in one call, in this order: <code>rw [hu, he, union_empty_left]</code>. Then <code>exact hp</code>. For <code>star_emp_right</code> the same, with <code>union_empty_right</code> and the last two names swapped.'
     ],

     sol: 'theorem star_emp_left (P : Assertion) : emp ∗ P ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, he, hp⟩\n  rw [hu, he, union_empty_left]\n  exact hp\n\ntheorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by\n  intro σ h ⟨h₁, h₂, _, hu, hp, he⟩\n  rw [hu, he, union_empty_right]\n  exact hp',

     expl: '<code>he : h₁ = Heap.empty</code> and <code>hu : h = Heap.union h₁ h₂</code>. Rewriting with both turns the goal’s heap into <code>Heap.union Heap.empty h₂</code>, which <code>union_empty_left</code> simplifies to <code>h₂</code> — exactly where <code>P</code> holds.',

     walk: [
       {tac: 'intro σ h ⟨h₁, h₂, _, hu, he, hp⟩', h: 'Introduces the store <code>σ</code>, the heap <code>h</code>, and then destructures the star hypothesis into its six components in place. The third slot — disjointness — is discarded with <code>_</code>, because the unit law does not need it. Lean keeps it in the context under the inaccessible name <code>left✝</code>.'},
       {tac: 'rw [hu, he, union_empty_left]', h: 'Three rewrites, left to right, all in the goal. <code>hu</code> replaces <code>h</code> by <code>h₁.union h₂</code>; <code>he</code> replaces <code>h₁</code> by <code>Heap.empty</code>; <code>union_empty_left</code> collapses <code>Heap.empty.union h₂</code> to <code>h₂</code>. The goal ends as <code>P σ h₂</code>. Note that <code>union_empty_left</code> is handed to <code>rw</code> with <b>no argument</b>, even though its statement is <code>union_empty_left (h : Heap) : Heap.union Heap.empty h = h</code> with <code>h</code> explicit. Inside <code>rw</code> you give a lemma unapplied: Lean unifies its left-hand side <code>Heap.union Heap.empty ?h</code> against the goal and discovers <code>?h := h₂</code> for you. In <i>term</i> position — the very next exercise — the same lemma has to be fully applied, <code>union_empty_left h</code>, because there is no goal to unify against.'},
       {tac: 'exact hp', h: '<code>hp : P σ h₂</code> is literally the goal. Done.'},
       {tac: 'theorem star_emp_right (P : Assertion) : P ∗ emp ⊢ P := by', h: 'The mirror statement. Everything that follows is the same proof with left and right exchanged.'},
       {tac: 'intro σ h ⟨h₁, h₂, _, hu, hp, he⟩', h: 'Same six slots — but now <code>P</code> is the <i>left</i> conjunct, so slot 5 is <code>hp : P σ h₁</code> and slot 6 is <code>he : emp σ h₂</code>. The names swapped; the pattern did not.'},
       {tac: 'rw [hu, he, union_empty_right]', h: 'Now <code>he</code> rewrites <code>h₂</code> to <code>Heap.empty</code>, leaving <code>h₁.union Heap.empty</code>, and it is <code>union_empty_right</code> that collapses it. Using <code>union_empty_left</code> here fails — see the pitfall.'},
       {tac: 'exact hp', h: 'The goal is now <code>P σ h₁</code>, which is <code>hp</code>.'}
     ],

     deep: [
       {t: 'trace', title: 'star_emp_left, one rewrite at a time',
        start: 'P : Assertion\n⊢ emp ∗ P ⊢ P',
        steps: [
          {tac: 'intro σ h ⟨h₁, h₂, _, hu, he, hp⟩',
           state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ h',
           h: 'Note <code>left✝</code>: that is the discarded disjointness, present but unnameable. Note also that <code>he</code> displays as <code>emp σ h₁</code>, <i>not</i> as <code>h₁ = Heap.empty</code> — Lean does not unfold <code>emp</code> for display.'},
          {tac: 'rw [hu]',
           state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ (h₁.union h₂)',
           h: 'The goal’s heap is now written in terms of the two pieces. This is the move: you never change <code>P</code>, you only rewrite the heap it is applied to.'},
          {tac: 'rw [he]',
           state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ (Heap.empty.union h₂)',
           h: 'Here is the part worth pausing on. <code>rw</code> needs an equation, and <code>he</code>’s type <i>displays</i> as <code>emp σ h₁</code>. <code>rw</code> unfolds the definition of <code>emp</code> to find the underlying <code>h₁ = Heap.empty</code>, and uses that. You are allowed to rewrite with a hypothesis whose type is only <i>definitionally</i> an equation.'},
          {tac: 'rw [union_empty_left]',
           state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhe : emp σ h₁\nhp : P σ h₂\n⊢ P σ h₂',
           h: 'The unit law of the monoid, applied inside an assertion. Now the goal is exactly <code>hp</code>.'}
        ],
        done: 'No goals.'},

       {t: 'trace', title: 'star_emp_right — the same, mirrored',
        cap: 'The starting pane is the state after the same six-name intro, not the state at the theorem; only slots 5 and 6 differ from the trace above.',
        start: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhe : emp σ h₂\n⊢ P σ h',
        steps: [
          {tac: 'rw [hu, he, union_empty_right]',
           state: 'P : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhe : emp σ h₂\n⊢ P σ h₁',
           h: 'Compare the two contexts: slots 5 and 6 have swapped types. That is the entire difference between the two theorems, and it is why the last rewrite has to be the other unit law.'}
        ],
        done: 'No goals.'},

       {t: 'cmp',
        left:  {t: 'The naive attempt', kind: 'bad',
                h: 'Unfold everything with <code>simp</code> and hope. It does unfold — but it leaves you exactly where you started, holding an existential you still have to destructure. <code>simp</code> is not a substitute for knowing which of the six components you need.',
                tag: 'sketch',
                src: 'intro σ h hstar\nsimp [star, emp] at hstar\nexact hstar'},
        right: {t: 'What Lean actually says', kind: 'good',
                h: 'The <code>Type mismatch</code> is the point: <code>simp</code> normalised the hypothesis into a readable existential and then had nothing left to do. Destructuring is not optional; it is the proof.',
                tag: 'sketch',
                src: 'error: Type mismatch\n  hstar\nhas type\n  ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ h₁ = Heap.empty ∧ P σ h₂\nbut is expected to have type\n  P σ h'}},

       {t: 'detail', title: 'Why the disjointness is genuinely unnecessary here', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'It is worth noticing which lemmas need <code>hd</code> and which do not, because that distinction <i>is</i> the “partial” in partial commutative monoid. <code>union_empty_left</code> and <code>union_empty_right</code> are unconditional: <code>Heap.empty ∪ h = h</code> for every <code>h</code>, disjoint or not, because the empty heap overlaps nothing. So the unit laws for <code>∗</code> inherit that and use only slots 4, 5, 6.'},
          {t: 'p', h: 'Contrast <code>star_comm</code> two exercises down, whose whole content is the one place <code>hd</code> cannot be avoided. If you ever find yourself unable to finish one of these proofs, a good diagnostic question is: <i>am I using disjointness, and should I be?</i>'}
        ]}
     ],

     pitfall: 'Getting the arity wrong. If you write five names instead of six — <code>⟨h₁, h₂, _, hu, he⟩</code> — Lean does <b>not</b> complain at the <code>intro</code> line. The last name simply absorbs everything that is left, so <code>he</code> silently gets type <code>emp σ h₁ ∧ P σ h₂</code> instead of <code>emp σ h₁</code>, and the complaint arrives one line later, from the <code>rw</code>: <code>Invalid rewrite argument: Expected an equality or iff proof or definition name, but `he` is a proof of emp σ h₁ ∧ P σ h₂</code>. Whenever an error mentions a <code>∧</code> you did not expect, count the names in your pattern. The error always points at the <i>use</i>, never at the pattern that caused it.',

     variants: 'Reverse the unit: <code>rw [hu, he, union_empty_right]</code> inside <code>star_emp_left</code> fails with <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern Heap.union ?h Heap.empty in the target expression P σ (Heap.empty.union h₂)</code>. The two unit lemmas are <i>not</i> interchangeable at the syntactic level even though they say the same thing about the monoid. Drop the <code>emp</code> entirely and the statement becomes <code>Q ∗ P ⊢ P</code>, which is <b>false</b> — that is the substructural point M3 made when it contrasted <code>and_left</code> with the star, and there is a machine-checked refutation later in this chapter.'
    },

    {t: 'ex',
     id: 'm4-2',
     name: 'star_emp_left_intro / star_emp_right_intro',
     hard: false,

     why: 'The converses. Together with the previous exercise these give <code>emp ∗ P ⊣⊢ P</code>. More importantly they are your first proofs that <i>construct</i> a star, which means you must invent the cut yourself — the only genuinely creative act in the whole chapter. Here the invention is easy (put nothing on one side), which is exactly why it is the right place to learn the mechanics.',

     setup: 'You need <code>disjoint_empty_left</code>, <code>disjoint_empty_right</code>, <code>union_empty_left</code>, <code>union_empty_right</code> — all from M2. No tactics beyond <code>intro</code> and <code>exact</code>.',

     goal: 'theorem star_emp_left_intro  (P : Assertion) : P ⊢ emp ∗ P\ntheorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp',

     hints: [
       'Now the star is the <i>goal</i>, not the hypothesis. So there is nothing to destructure: after <code>intro σ h hp</code> you owe a six-component tuple.',
       'Which cut? You have exactly one heap, <code>h</code>, and one of the two conjuncts is <code>emp</code>, which can only be satisfied by <code>Heap.empty</code>. So the split is forced: <code>Heap.empty</code> and <code>h</code>, in the order matching the goal.',
       'Fill the slots in order: the two heaps, then <code>disjoint_empty_left h</code>, then the equation <code>h = Heap.union Heap.empty h</code>, then a proof of <code>emp σ Heap.empty</code>, then <code>hp</code>. Slot 5 is <code>rfl</code>, because <code>emp σ Heap.empty</code> unfolds to <code>Heap.empty = Heap.empty</code>.',
       'Slot 4 is the trap. Your lemma says <code>Heap.union Heap.empty h = h</code>; the goal wants <code>h = Heap.union Heap.empty h</code>. Apply <code>.symm</code>: <code>(union_empty_left h).symm</code>.'
     ],

     sol: 'theorem star_emp_left_intro (P : Assertion) : P ⊢ emp ∗ P := by\n  intro σ h hp\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩\n\ntheorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by\n  intro σ h hp\n  exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩',

     expl: 'Note the <code>.symm</code>: the star wants <code>h = Heap.union h₁ h₂</code> whereas your lemma states <code>Heap.union Heap.empty h = h</code>. Getting equation directions right is most of the friction in these proofs; it is worth reading the goal carefully rather than guessing.',

     walk: [
       {tac: 'intro σ h hp', h: 'Three introductions and no destructuring, because the hypothesis <code>P σ h</code> is atomic. The goal becomes <code>(emp ∗ P) σ h</code>.'},
       {tac: 'exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, rfl, hp⟩', h: 'All six slots at once. Slots 1–2 choose the cut: nothing on the left, everything on the right. Slot 3 is disjointness of the empty heap from anything. Slot 4 is the reassembly equation, flipped with <code>.symm</code>. Slot 5 proves <code>emp σ Heap.empty</code>, which is definitionally <code>Heap.empty = Heap.empty</code>, hence <code>rfl</code>. Slot 6 is the hypothesis, unchanged.'},
       {tac: 'theorem star_emp_right_intro (P : Assertion) : P ⊢ P ∗ emp := by', h: 'The mirror statement: <code>emp</code> now on the right.'},
       {tac: 'intro σ h hp', h: 'Identical opening.'},
       {tac: 'exact ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, hp, rfl⟩', h: 'Every slot is the mirror of the previous proof: the heaps swap, <code>disjoint_empty_left</code> becomes <code>disjoint_empty_right</code>, <code>union_empty_left</code> becomes <code>union_empty_right</code>, and slots 5 and 6 exchange <code>hp</code> with <code>rfl</code>.'}
     ],

     deep: [
       {t: 'trace', title: 'The four obligations, exposed with refine',
        start: 'P : Assertion\n⊢ P ⊢ emp ∗ P',
        steps: [
          {tac: 'intro σ h hp',
           state: 'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ (emp ∗ P) σ h',
           h: 'The goal is still folded. You cannot read the obligations off it yet.'},
          {tac: 'show ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ emp σ h₁ ∧ P σ h₂',
           state: 'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ emp σ h₁ ∧ P σ h₂',
           h: '<code>show</code> replaces the goal by a definitionally equal one. Logically a no-op; visually the difference between guessing and reading.'},
          {tac: 'refine ⟨Heap.empty, h, ?_, ?_, ?_, ?_⟩',
           state: 'case refine_1\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ Heap.empty.disjoint h\n\ncase refine_2\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ h = Heap.empty.union h\n\ncase refine_3\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ emp σ Heap.empty\n\ncase refine_4\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ P σ h',
           h: 'Four goals, in slot order. <code>refine_1</code> is <code>disjoint_empty_left h</code>; <code>refine_2</code> is where the <code>.symm</code> lives; <code>refine_3</code> is <code>rfl</code>; <code>refine_4</code> is <code>hp</code>. Committing the two heaps in slots 1 and 2 is what turned the abstract goal into four concrete ones.'}
        ],
        done: 'Each goal closed by the corresponding component of the shipped one-line exact.'},

       {t: 'detail', title: 'A Lean subtlety: one of these .symm’s is optional and the other is not', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'M2 observed that <code>union_empty_left</code> is “pointwise <code>rfl</code>” while <code>union_empty_right</code> needs a case split, because <code>Heap.union</code> matches on its first argument. That asymmetry survives all the way up to the function level, thanks to eta:'},
          {t: 'code', tag: 'illustration',
           src: 'example (h : Heap) : Heap.union Heap.empty h = h := rfl   -- accepted'},
          {t: 'p', h: 'So in <code>star_emp_left_intro</code> the whole slot could equally well be <code>rfl</code>, or <code>union_empty_left h</code> with no <code>.symm</code> at all. Both were tried; both are accepted. The reason the un-flipped lemma is accepted is worth spelling out, because it looks like a type error and is not: slot 4 asks for <code>@Eq Heap h (Heap.union Heap.empty h)</code> and you are offering <code>@Eq Heap (Heap.union Heap.empty h) h</code>. Those are two <i>different</i> types — but <code>Heap.union Heap.empty h</code> is definitionally <code>h</code>, so both reduce to <code>@Eq Heap h h</code> and Lean accepts the swap. The <code>.symm</code> is there for uniformity with its mirror image.'},
          {t: 'p', h: 'In <code>star_emp_right_intro</code> nothing of the sort is available. <code>Heap.union h Heap.empty = h</code> is <i>not</i> definitional — <code>Heap.union</code> matches on its <b>first</b> argument, which here is the variable <code>h</code>, so the <code>match</code> is stuck and no reduction happens. Putting <code>rfl</code> in slot 4 is rejected with <code>Application type mismatch: The argument rfl has type ?m.17 = ?m.17 but is expected to have type h = h.union Heap.empty in the application And.intro rfl</code>, and dropping the <code>.symm</code> gives the honest complaint <code>Application type mismatch: The argument union_empty_right h has type h.union Heap.empty = h but is expected to have type h = h.union Heap.empty</code>. Read those two errors together: the first says <i>nothing</i> proves this by computation, the second says <i>this</i> proves it backwards.'},
          {t: 'p', h: 'The moral is not “memorise which one is definitional”. It is: when an equation slot rejects your term, read the two types in the error and ask only whether they are the same equation read backwards. Nine times out of ten in this chapter, they are.'}
        ]},

       {t: 'steps', title: 'Choosing a cut, in general',
        items: [
          {k: 'Look at which conjunct pins the heap down', h: '<code>emp</code> forces <code>Heap.empty</code>. <code>l ↦ v</code> forces <code>Heap.singleton l v</code>. <code>fact φ</code> forces nothing at all. Start from the most constrained conjunct.'},
          {k: 'Give the rest to the other side', h: 'Here <code>emp</code> takes nothing, so <code>P</code> takes all of <code>h</code>. In M8 the constrained side will be the footprint of a command and the other side will be the frame <code>R</code>; the proof of <code>hoare_frame</code> makes exactly this choice.'},
          {k: 'Then discharge slots 3 and 4 from M2', h: 'Once the two heaps are fixed, disjointness and the reassembly equation are pure monoid facts with no assertions in them. If you cannot find the lemma, it is in the table above.'}
        ]}
     ],

     pitfall: 'Forgetting <code>.symm</code> on slot 4. The error is <code>Application type mismatch: The argument union_empty_right h has type h.union Heap.empty = h but is expected to have type h = h.union Heap.empty</code>, and it ends <code>in the application And.intro (union_empty_right h)</code> — naming <code>And.intro</code>, which is confusing because you never wrote <code>And.intro</code> — that is the anonymous constructor showing its underlying form. Read past it to the two types.',

     variants: 'Swap slots 5 and 6 in either proof and the error is immediate and informative — in <code>star_emp_left_intro</code>, <code>Application type mismatch: The argument hp has type P σ h but is expected to have type emp σ Heap.empty</code>. The two assertions are pinned to different pieces of the cut, so they cannot trade places. Swap slots 1 and 2 instead — write <code>⟨h, Heap.empty, …⟩</code> in <code>star_emp_left_intro</code> — and <code>refine</code> shows you two impossible obligations at once: <code>⊢ emp σ h</code>, which is <b>false</b> (it would say every heap is empty), and <code>⊢ P σ Heap.empty</code>, which is false for the same reason in the other direction. That failure is the useful one, because it shows the cut really is forced, not merely conventional.'
    },

    /* ─────────────────────────────  commutativity  ──────────────────── */
    {t: 'sec', s: 'Exercises · commutativity'},

    {t: 'p', h: 'Commutativity is the first law where a hypothesis from M2 is genuinely load-bearing. Watch for the single place <code>hd</code> is consumed.'},

    {t: 'ex',
     id: 'm4-3',
     name: 'star_comm',
     hard: false,

     why: 'One direction suffices for both, since applying it twice gives <code>⊣⊢</code>. Beyond that, it is the cheapest possible demonstration of what disjointness <i>buys</i>: the same two heaps, reassembled in the other order, give the same heap — and that sentence is false without <code>hd</code>. Every time you reorder a precondition in M9, this is the lemma underneath.',

     setup: 'You need <code>disjoint_symm</code> and <code>union_comm</code> from M2. Note the shape of <code>union_comm</code>: it <i>takes</i> the disjointness proof as an argument, <code>union_comm hd : Heap.union h₁ h₂ = Heap.union h₂ h₁</code>.',

     goal: 'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P',

     hints: [
       'Destructure the hypothesis with the usual six names, then build the goal with the same six things in a different arrangement. Nothing new is created; everything is permuted.',
       'Slots 1 and 2 of the goal are <code>h₂</code> and <code>h₁</code> — the heaps swap. Slots 5 and 6 swap correspondingly. So the only two slots with real work are 3 and 4.',
       'Slot 3 is <code>disjoint_symm hd</code>. Slot 4 needs <code>h = Heap.union h₂ h₁</code>, and you have <code>hu : h = Heap.union h₁ h₂</code>: rewrite with <code>hu</code>, then with <code>union_comm hd</code>. You can put a whole tactic proof in a term slot by writing <code>by …</code> inside the tuple.'
     ],

     sol: 'theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩',

     expl: 'One line of real content: <code>by rw [hu, union_comm hd]</code>. This is precisely where the <i>commutativity</i> half of the partial commutative monoid is consumed. It also shows why <code>union</code> alone is not enough — the swap is only legal because we are carrying <code>hd</code>.',

     walk: [
       {tac: 'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩', h: 'The standard opening, this time keeping all six components: unlike the unit laws, commutativity needs the disjointness, so slot 3 gets a real name.'},
       {tac: 'exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩', h: 'Slots 1, 2, 5, 6 are the given data with left and right exchanged. Slot 3 flips the disjointness. Slot 4 is an embedded tactic block: <code>by</code> opens tactic mode inside a term, the goal there being <code>h = h₂.union h₁</code>; <code>rw [hu]</code> makes it <code>h₁.union h₂ = h₂.union h₁</code>, and <code>rw [union_comm hd]</code> turns the left side into the right, closing it by <code>rfl</code> automatically.'}
     ],

     deep: [
       {t: 'trace', title: 'star_comm with the inline by-block pulled out',
        start: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (Q ∗ P) σ h',
        steps: [
          {tac: 'refine ⟨h₂, h₁, disjoint_symm hd, ?_, hq, hp⟩',
           state: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ h = h₂.union h₁',
           h: 'Five of the six slots close instantly; the leftover goal is exactly the heap equation. This is the same proof as the shipped one — <code>refine … ?_</code> here, <code>by …</code> there.'},
          {tac: 'rw [hu]',
           state: 'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ h₁.union h₂ = h₂.union h₁',
           h: 'And there is the monoid law, standing alone with no assertions in sight. Everything about <code>∗</code> has been stripped away.'},
          {tac: 'rw [union_comm hd]',
           state: 'No goals.',
           h: '<code>union_comm hd</code> rewrites the left-hand side to <code>h₂.union h₁</code>, at which point both sides are syntactically identical and <code>rw</code> closes the goal with <code>rfl</code> on its own.'}
        ],
        done: 'No goals.'},

       {t: 'p', h: 'Notice what the trace shows about where information is spent. Slots 1, 2, 5, 6 are free — a permutation. Slot 3 costs one lemma. Slot 4 costs the <i>only</i> use of disjointness in the proof. The whole theorem is that one <code>rw</code>.'},

       {t: 'detail', title: 'Why the by-block, and not a have?', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'You could equally write <code>have heq : h = Heap.union h₂ h₁ := by rw [hu, union_comm hd]</code> before the <code>exact</code>, and then pass <code>heq</code>. Same proof, three lines instead of two. The reason the workbook inlines it is that in M7–M13 these tuples get long and the equation slot is almost always a one-liner; hoisting it out every time doubles the length of the development for no gain in clarity.'},
          {t: 'p', h: 'The one time to hoist: when Lean cannot infer the expected type of the <code>by</code> block because the surrounding tuple is still ambiguous. That does not happen here — slots 1 and 2 have already fixed <code>h₂</code> and <code>h₁</code>, so the goal inside <code>by</code> is fully determined.'}
        ]}
     ],

     pitfall: 'Writing <code>by rw [hu]</code> and stopping there, on the theory that the two unions are “obviously the same heap”. They are not <i>syntactically</i> the same, so Lean reports <code>unsolved goals … ⊢ h₁.union h₂ = h₂.union h₁</code>. That residual goal is the theorem; if it looks like nothing needs doing, you have found the exact place where a paper proof would have waved its hands.',

     variants: 'Drop <code>hd</code> from <code>union_comm</code> and the lemma is <b>false</b>, not merely unprovable: take <code>h₁ = Heap.singleton 0 4</code> and <code>h₂ = Heap.singleton 0 7</code>. Then <code>Heap.union h₁ h₂</code> sends <code>0</code> to <code>some 4</code> while <code>Heap.union h₂ h₁</code> sends it to <code>some 7</code>, because M2’s union is <b>left-biased</b>. Overlapping heaps are precisely where left-bias becomes visible, and disjointness is precisely the hypothesis that makes it invisible. Reverse <code>disjoint_symm hd</code> to plain <code>hd</code> and you get a type mismatch on slot 3: you would be claiming <code>h₂.disjoint h₁</code> with a proof of <code>h₁.disjoint h₂</code>, which are different propositions even though each implies the other.'
    },

    /* ─────────────────────────────  associativity  ──────────────────── */
    {t: 'sec', s: 'Exercises · associativity'},

    {t: 'p', h: 'The first proof with real content. Draw the picture before you write Lean:'},

    {t: 'txt', src: '  (P ∗ Q) ∗ R                     P ∗ (Q ∗ R)\n\n   ┌────────┬────┐                 ┌────┬────────┐\n   │ hP  hQ │ hR │      ═══>       │ hP │ hQ  hR │\n   └────────┴────┘                 └────┴────────┘\n     h = (hP ∪ hQ) ∪ hR              h = hP ∪ (hQ ∪ hR)'},

    {t: 'p', h: 'The heaps do not move; only the brackets do. What you must reconstruct are the disjointness proofs on the other side of the equality.'},

    {t: 'steps', title: 'The argument, before any Lean',
     items: [
       {k: 'You are given three pieces and two facts about them', h: 'From the outer star: <code>hPQ ⟂ hR</code> and <code>h = hPQ ∪ hR</code>. From the inner one: <code>hP ⟂ hQ</code> and <code>hPQ = hP ∪ hQ</code>. Substituting the second equation into the first two puts everything in terms of <code>hP</code>, <code>hQ</code>, <code>hR</code>.'},
       {k: 'Take the given disjointness apart', h: '<code>(hP ∪ hQ) ⟂ hR</code> is, by <code>disjoint_union_left</code>, the conjunction of <code>hP ⟂ hR</code> and <code>hQ ⟂ hR</code>. This is the only place information is <i>extracted</i>.'},
       {k: 'Build the disjointness the new bracketing needs', h: 'You must supply <code>hP ⟂ (hQ ∪ hR)</code>, which by <code>disjoint_union_right</code> is <code>hP ⟂ hQ</code> (given) together with <code>hP ⟂ hR</code> (just extracted). This is the only place information is <i>assembled</i>.'},
       {k: 'The heap equation is one lemma', h: '<code>h = (hP ∪ hQ) ∪ hR = hP ∪ (hQ ∪ hR)</code> by <code>union_assoc</code>, which needs <b>no</b> disjointness at all — left-biased union is associative on the nose. All the difficulty of associativity lives in the disjointness bookkeeping, not in the heaps.'},
       {k: 'Rebuild the inner star', h: 'Its two pieces are <code>hQ</code> and <code>hR</code>, its disjointness is <code>hQ ⟂ hR</code>, and its heap equation is <code>rfl</code> — because the heap you chose for it <i>is</i> <code>hQ ∪ hR</code>, syntactically.'}
     ]},

    {t: 'p', h: 'If that reads like M2’s <code>splits_assoc</code>, it is: the two proofs are the same argument with and without assertions wrapped around it. Compare them side by side afterwards — it is a good check on whether you have separated “resource algebra” from “logic” in your head.'},

    {t: 'ex',
     id: 'm4-4',
     name: 'star_assoc_left / star_assoc_right',
     hard: true,

     why: 'This is the theorem that lets you stop thinking about heaps and start thinking about a <i>list</i> of owned resources. Without it, every proof would be a parenthesisation nightmare.',

     setup: 'You need <code>disjoint_union_left</code> and <code>disjoint_union_right</code> (both <code>↔</code>, so use <code>.mp</code> and <code>.mpr</code>) and <code>union_assoc</code>. New tactics here: <code>subst</code>, <code>obtain</code> on a conjunction, and <code>refine</code> with <code>?_</code> holes.',

     goal: 'theorem star_assoc_left  (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R',

     hints: [
       'The hypothesis is a star whose <i>left conjunct is itself a star</i>. You can destructure both levels in a single <code>intro</code> pattern by nesting: the fifth slot of the outer pattern is where the inner <code>⟨…⟩</code> goes.',
       'After destructuring you have two heap equations, <code>hu₁ : h = hPQ.union hR</code> and <code>hu₂ : hPQ = hP.union hQ</code>. Eliminate the intermediate heap: <code>subst hu₂</code> replaces <code>hPQ</code> everywhere by <code>hP.union hQ</code> and deletes both <code>hPQ</code> and <code>hu₂</code> from the context.',
       'Now <code>hd₁</code> reads <code>(hP.union hQ).disjoint hR</code>, which is the left-hand side of <code>disjoint_union_left</code>. Use <code>obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁</code> to get the two halves.',
       'Build the new cut with <code>refine</code>, leaving holes for the two slots that need work: <code>refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩</code>. The first hole is the heap equation, closed by <code>rw [hu₁, union_assoc]</code>; the second is the inner star, closed by <code>exact ⟨hQ, hR, hQR, rfl, hq, hr⟩</code>.'
     ],

     sol: 'theorem star_assoc_left (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by\n  intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩\n  subst hu₂\n  obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁\n  refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩\n  · rw [hu₁, union_assoc]\n  · exact ⟨hQ, hR, hQR, rfl, hq, hr⟩\n\ntheorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by\n  intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩\n  subst hu₂\n  obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁\n  refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩\n  rw [hu₁, union_assoc]',

     expl: 'Read the <code>refine</code> line as “here is the new cut: <code>hP</code> on the left, <code>hQ ∪ hR</code> on the right”. Everything after that is discharging the four obligations of a star: disjointness (from <code>disjoint_union_right</code>), the heap equation (<code>rw [hu₁, union_assoc]</code>), <code>P</code> (unchanged), and the inner star (rebuilt from <code>hQ</code>, <code>hR</code> with <code>rfl</code> for its equation, because <code>hQ ∪ hR</code> is <i>literally</i> the heap we chose). The mirror-image proof does the same with <code>disjoint_union_left</code> / <code>disjoint_union_right</code> swapped.',

     walk: [
       {tac: 'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩', h: 'Both levels at once. The outer pattern has the usual six slots; slot 5 — which would hold a proof of <code>(P ∗ Q) σ hPQ</code> — is itself destructured with six more names. After this line the context holds three heaps that matter (<code>hP</code>, <code>hQ</code>, <code>hR</code>), one that is about to disappear (<code>hPQ</code>), two disjointness facts and two equations.'},
       {tac: 'subst hu₂', h: '<code>hu₂ : hPQ = hP.union hQ</code>. <code>subst</code> eliminates the variable <code>hPQ</code> by replacing it everywhere with the right-hand side, then discards both the variable and the equation. <code>hd₁</code> and <code>hu₁</code> are silently rewritten; the goal is untouched because <code>hPQ</code> does not occur in it. Lean also re-orders the context, moving the rewritten hypotheses to the end.'},
       {tac: 'obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁', h: '<code>disjoint_union_left</code> is an <code>↔</code>; <code>.mp</code> is its forward direction. Applied to <code>hd₁ : (hP.union hQ).disjoint hR</code> it yields a conjunction, which <code>obtain</code> splits into <code>hPR : hP.disjoint hR</code> and <code>hQR : hQ.disjoint hR</code>. This is the extraction step of the argument.'},
       {tac: 'refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩', h: 'The new cut, declared. Slot 1 is <code>hP</code>; slot 2 is <code>hQ ∪ hR</code>, written out explicitly because Lean has no way to guess it. Slot 3 assembles <code>hP ⟂ (hQ ∪ hR)</code> from the two halves using the <i>backward</i> direction <code>.mpr</code>. Slots 4 and 6 are left as holes.'},
       {tac: '· rw [hu₁, union_assoc]', h: 'First hole: <code>h = hP.union (hQ.union hR)</code>. <code>hu₁</code> rewrites <code>h</code> to <code>(hP.union hQ).union hR</code>; <code>union_assoc</code> re-brackets it; both sides then coincide and <code>rw</code> finishes with <code>rfl</code>. The <code>·</code> is a focusing bullet — it selects the first remaining goal and requires you to close it before moving on.'},
       {tac: '· exact ⟨hQ, hR, hQR, rfl, hq, hr⟩', h: 'Second hole: <code>(Q ∗ R) σ (hQ.union hR)</code>. Its six slots are <code>hQ</code>, <code>hR</code>, the extracted <code>hQR</code>, then <code>rfl</code> — because the heap in question is <i>syntactically</i> <code>hQ.union hR</code>, so the equation slot is a reflexivity — and finally the two assertion proofs, unchanged.'},
       {tac: 'theorem star_assoc_right (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by', h: 'The converse. Same argument reflected in a mirror; the only asymmetry is which <code>disjoint_union_*</code> lemma is used in which direction.'},
       {tac: 'intro σ h ⟨hP, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩', h: 'Now the nesting is in slot 6, not slot 5, because the star inside is on the right.'},
       {tac: 'subst hu₂', h: 'Eliminates <code>hQR</code> in favour of <code>hQ.union hR</code>, exactly as before.'},
       {tac: 'obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁', h: 'This time <code>hd₁ : hP.disjoint (hQ.union hR)</code>, so it is <code>disjoint_union_right</code> that applies. The names are chosen to say what they are: <code>hPQ : hP.disjoint hQ</code>, <code>hPR : hP.disjoint hR</code>.'},
       {tac: 'refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩', h: 'One hole only: the inner star is small enough to inline, again with <code>rfl</code> in its equation slot. Slot 3 now assembles <code>(hP ∪ hQ) ⟂ hR</code> with <code>disjoint_union_left.mpr</code> — note the argument order <code>⟨hPR, hd₂⟩</code> matches the conjunction in that lemma’s right-hand side.'},
       {tac: 'rw [hu₁, union_assoc]', h: 'The lone remaining goal <code>h = (hP.union hQ).union hR</code>. No bullet is needed when exactly one goal is left.'}
     ],

     deep: [
       {t: 'trace', title: 'star_assoc_left, tactic by tactic',
        start: 'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R',
        steps: [
          {tac: 'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩',
           state: 'P Q R : Assertion\nσ : Store\nh hPQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhu₁ : h = hPQ.union hR\nhP hQ : Heap\nhd₂ : hP.disjoint hQ\nhu₂ : hPQ = hP.union hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\n⊢ (P ∗ Q ∗ R) σ h',
           h: 'Read the goal carefully: <code>P ∗ Q ∗ R</code> with no parentheses <i>is</i> <code>P ∗ (Q ∗ R)</code>, because <code>∗</code> is right-associative — look at the starting state above, where the source bracketing on the left kept its parentheses and the target on the right lost them. Eleven lines of context, of which the three heaps <code>hP</code>, <code>hQ</code>, <code>hR</code> and the three assertion proofs are the payload and the rest is plumbing.'},
          {tac: 'subst hu₂',
           state: 'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\n⊢ (P ∗ Q ∗ R) σ h',
           h: '<code>hPQ</code> and <code>hu₂</code> are gone. <code>hd₁</code> and <code>hu₁</code> now speak directly about <code>hP.union hQ</code>, and they have been moved to the bottom of the context — <code>subst</code> re-asserts every hypothesis it rewrites, so their position changes. Do not be alarmed by the reshuffle; nothing was lost.'},
          {tac: 'obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁',
           state: 'P Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (P ∗ Q ∗ R) σ h',
           h: 'Now the context contains all three pairwise disjointnesses — <code>hd₂ : hP ⟂ hQ</code>, <code>hPR : hP ⟂ hR</code>, <code>hQR : hQ ⟂ hR</code>. That is the real content of the hypothesis, and from here the proof is assembly.'},
          {tac: 'refine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩',
           state: 'case refine_1\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ h = hP.union (hQ.union hR)\n\ncase refine_2\nP Q R : Assertion\nσ : Store\nh hR hP hQ : Heap\nhd₂ : hP.disjoint hQ\nhp : P σ hP\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : (hP.union hQ).disjoint hR\nhu₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR : hQ.disjoint hR\n⊢ (Q ∗ R) σ (hQ.union hR)',
           h: 'Two goals, and they are exactly the two halves of the picture: re-bracket the heap, and rebuild the inner star. Everything about <code>P</code> has already been discharged by passing <code>hp</code> directly.'}
        ],
        done: 'No goals, after rw [hu₁, union_assoc] and exact ⟨hQ, hR, hQR, rfl, hq, hr⟩.'},

       {t: 'trace', title: 'star_assoc_right — the same three moves, mirrored',
        start: 'P Q R : Assertion\nσ : Store\nh hP hQR : Heap\nhd₁ : hP.disjoint hQR\nhu₁ : h = hP.union hQR\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhu₂ : hQR = hQ.union hR\nhq : Q σ hQ\nhr : R σ hR\n⊢ ((P ∗ Q) ∗ R) σ h',
        cap: 'The state after the nested intro; the theorem opens as ⊢ P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.',
        steps: [
          {tac: 'subst hu₂; obtain ⟨hPQ, hPR⟩ := disjoint_union_right.mp hd₁',
           state: 'P Q R : Assertion\nσ : Store\nh hP : Heap\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : hP.disjoint (hQ.union hR)\nhu₁ : h = hP.union (hQ.union hR)\nhPQ : hP.disjoint hQ\nhPR : hP.disjoint hR\n⊢ ((P ∗ Q) ∗ R) σ h',
           h: 'Identical position to the other direction, up to renaming: three heaps, three pairwise disjointnesses, one equation for <code>h</code>. The goal keeps its parentheses this time, because <code>(P ∗ Q) ∗ R</code> is the <i>left</i>-associated bracketing and <code>∗</code> is <code>infixr</code>.'},
          {tac: 'refine ⟨Heap.union hP hQ, hR, disjoint_union_left.mpr ⟨hPR, hd₂⟩, ?_, ⟨hP, hQ, hPQ, rfl, hp, hq⟩, hr⟩',
           state: 'P Q R : Assertion\nσ : Store\nh hP : Heap\nhp : P σ hP\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : hP.disjoint (hQ.union hR)\nhu₁ : h = hP.union (hQ.union hR)\nhPQ : hP.disjoint hQ\nhPR : hP.disjoint hR\n⊢ h = (hP.union hQ).union hR',
           h: 'A single goal remains: the heap equation, again one <code>union_assoc</code> away. Everything else was discharged inline.'}
        ],
        done: 'No goals, after rw [hu₁, union_assoc].'},

       {t: 'cmp',
        left:  {t: 'M2 · splits_assoc',
                h: 'The same argument with no assertions anywhere. If you compare line for line you will find <code>subst</code>, <code>obtain … disjoint_union_left.mp</code>, <code>refine</code> with <code>disjoint_union_right.mpr</code>, and <code>rw [·, union_assoc]</code> in the same order.',
                tag: 'sketch',
                src: 'obtain ⟨hd₁, he₁⟩ := h1\nobtain ⟨hd₂, he₂⟩ := h2\nsubst he₂\nobtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁\nrefine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR\', rfl⟩⟩\nrw [he₁, union_assoc]'},
        right: {t: 'M4 · star_assoc_left',
                h: 'The assertion-level version. The only new work is threading <code>hp</code>, <code>hq</code>, <code>hr</code> through untouched. This is what “the logic is induced by the PCM” means concretely: the resource reasoning was finished in M2, and M4 only re-packages it.',
                tag: 'sketch',
                src: 'intro σ h ⟨hPQ, hR, hd₁, hu₁, ⟨hP, hQ, hd₂, hu₂, hp, hq⟩, hr⟩\nsubst hu₂\nobtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁\nrefine ⟨hP, Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hp, ?_⟩\n· rw [hu₁, union_assoc]\n· exact ⟨hQ, hR, hQR, rfl, hq, hr⟩'}},

       {t: 'detail', title: 'subst, and when it refuses', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: '<code>subst h</code> requires <code>h</code> to be an equation with a <b>local variable on one side</b> that does not occur on the other. Here <code>hu₂ : hPQ = hP.union hQ</code> qualifies: <code>hPQ</code> is a local, and it does not appear on the right. Lean then eliminates <code>hPQ</code> globally and deletes <code>hu₂</code>.'},
          {t: 'p', h: 'It works equally well on <code>hu₁ : h = hPQ.union hR</code>, eliminating <code>h</code> instead. Add <code>subst hu₁</code> after <code>subst hu₂</code> and the goal becomes <code>(P ∗ Q ∗ R) σ ((hP.union hQ).union hR)</code>; the proof then finishes with <code>rw [union_assoc]</code> in place of <code>rw [hu₁, union_assoc]</code>. Both routes are fine, and it is worth doing once to see that the choice of which heap to eliminate is yours.'},
          {t: 'p', h: 'What <code>subst</code> refuses is an equation between two compound terms, because there is no variable to eliminate. On <code>he : h₁.union h₂ = h₂.union h₁</code> it reports <code>Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)</code>. When you see that message, you wanted <code>rw</code>, not <code>subst</code>.'},
          {t: 'p', h: 'Also worth knowing: <code>subst</code> is happy to see through definitions. In exercise <b>m4-7</b> you will <code>subst</code> a hypothesis of type <code>(l ↦ v) σ h₁</code>, which is only definitionally the equation <code>h₁ = Heap.singleton l v</code>. It works for the same reason <code>rw [he]</code> worked in <b>m4-1</b>.'}
        ]}
     ],

     pitfall: 'Reaching for the wrong member of the <code>disjoint_union_*</code> pair. In <code>star_assoc_left</code> the hypothesis is <code>(hP ∪ hQ) ⟂ hR</code> — a union on the <b>left</b> of the disjointness — so it is <code>disjoint_union_left</code> you need. Using the other one produces <code>Application type mismatch: The argument hd₁ has type (hP.union hQ).disjoint hR but is expected to have type Heap.disjoint ?m.122 (Heap.union ?m.123 ?m.124)</code>. Those are three <i>separate</i> holes — the numbers Lean gives them are arbitrary — and the shape they describe has the union on the right of <code>Heap.disjoint</code>, which is exactly what you do not have. The mnemonic: the <i>name</i> says which side of <code>Heap.disjoint</code> the union sits on, not which side of the goal you are on.',

     variants: 'Delete <code>subst hu₂</code> and try to carry <code>hPQ</code> through. The proof is still possible — you rewrite by hand with <code>rw [hu₂] at hd₁ hu₁</code> — but you must remember to rewrite in <i>both</i> places, and forgetting one leaves a goal mentioning a heap that no longer relates to anything. That is the argument for <code>subst</code>: it cannot forget. More interestingly, remove disjointness from the statement of <code>∗</code> altogether and associativity <b>survives</b>, because <code>union_assoc</code> needs no hypothesis; what dies instead is commutativity. Associativity and commutativity fail for genuinely different reasons, and that asymmetry is visible in the M2 lemma signatures if you look.'
    },

    /* ────────────────────  monotonicity and distribution  ───────────── */
    {t: 'sec', s: 'Exercises · monotonicity and distribution'},

    {t: 'ex',
     id: 'm4-5',
     name: 'star_mono',
     hard: false,

     why: '<code>∗</code> is monotone in both arguments. This is what lets you improve one side of a specification without touching the other — the everyday tool of the rest of the course. Concretely: the frame rule in M8 is stated with an arbitrary frame <code>R</code>, and rewriting one side of a star underneath that frame is what <code>star_mono_left</code> and <code>star_mono_right</code> are for. M9’s <code>copyCell_spec</code> uses <code>star_mono_right _ (star_comm …)</code> to swap two cells inside a bigger precondition, and M10’s <code>lseg_append</code> uses <code>star_mono_right</code> twice per inductive step to push the induction hypothesis into the tail of a list. Without monotonicity every one of those steps would be a fresh semantic proof.',

     setup: 'Recall that <code>Entails P Q</code> unfolds to <code>∀ σ h, P σ h → Q σ h</code>, so an entailment hypothesis <code>hpq : P ⊢ P\'</code> is a <i>function</i>: <code>hpq σ h₁ hp : P\' σ h₁</code>. You will also want <code>entails_refl</code> from M3.',

     goal: 'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\'',

     hints: [
       'Keep the same cut; push each entailment into its own piece. Nothing about the heap changes at all.',
       'After the usual six-name destructuring, the goal needs <code>P\' σ h₁</code> and <code>Q\' σ h₂</code>. You have <code>hp : P σ h₁</code> and <code>hq : Q σ h₂</code>, plus two entailments. Entailments are functions — apply them.',
       'An entailment takes <b>three</b> arguments before it gives you anything: the store, the heap, and the proof. So slot 5 is <code>hpq σ h₁ hp</code> and slot 6 is <code>hrs σ h₂ hq</code>.',
       'For the two specialisations, feed <code>entails_refl</code> to the side you do not want to change: <code>star_mono h (entails_refl Q)</code> and <code>star_mono (entails_refl P) h</code>.'
     ],

     sol: 'theorem star_mono {P P\' Q Q\' : Assertion} (hpq : P ⊢ P\') (hrs : Q ⊢ Q\') :\n    P ∗ Q ⊢ P\' ∗ Q\' := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩\n\ntheorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=\n  star_mono h (entails_refl Q)\n\ntheorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=\n  star_mono (entails_refl P) h',

     expl: 'The two specialisations <code>star_mono_left</code> and <code>star_mono_right</code> are not in the syllabus but you will reach for them constantly; define them now. They are just <code>star_mono</code> with <code>entails_refl</code> on one side.',

     walk: [
       {tac: 'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩', h: 'Standard opening. All six components are kept, because slots 1–4 will be reused verbatim.'},
       {tac: 'exact ⟨h₁, h₂, hd, hu, hpq σ h₁ hp, hrs σ h₂ hq⟩', h: 'Slots 1–4 are copied straight across: the cut, its disjointness and its reassembly equation are exactly the ones you were given. Only slots 5 and 6 change, each by one function application. This is the proof: <code>∗</code> touches the heap and the entailments touch the assertions, and the two never interact.'},
       {tac: 'theorem star_mono_left {P P\' : Assertion} (Q : Assertion) (h : P ⊢ P\') : P ∗ Q ⊢ P\' ∗ Q :=', h: 'A term-mode definition — no <code>by</code>, no tactics. Note that <code>Q</code> is explicit while <code>P</code> and <code>P\'</code> are implicit: you almost always know the entailment and want to say which frame you are keeping fixed, so <code>star_mono_left R h</code> reads well.'},
       {tac: 'star_mono h (entails_refl Q)', h: 'Instantiate the general lemma with the identity entailment on the right. <code>entails_refl Q : Q ⊢ Q</code>, so <code>Q\'</code> unifies with <code>Q</code> and the conclusion collapses to <code>P ∗ Q ⊢ P\' ∗ Q</code>.'},
       {tac: 'theorem star_mono_right (P : Assertion) {Q Q\' : Assertion} (h : Q ⊢ Q\') : P ∗ Q ⊢ P ∗ Q\' :=', h: 'The mirror image, with <code>P</code> explicit for the same reason.'},
       {tac: 'star_mono (entails_refl P) h', h: 'Identity on the left this time. Two one-line derivations instead of two more inductive proofs — this is the habit M2 recommended, applied again.'}
     ],

     deep: [
       {t: 'trace', title: 'star_mono, with the two obligations exposed',
        start: 'P P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\n⊢ P ∗ Q ⊢ P\' ∗ Q\'',
        steps: [
          {tac: 'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩',
           state: 'P P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (P\' ∗ Q\') σ h',
           h: 'Note the two goal-level <code>⊢</code> in the starting state: the outer one is Lean’s turnstile, the inner one is our <code>Entails</code> notation. <code>P ∗ Q ⊢ P\' ∗ Q\'</code> is the <i>proposition</i> being proved, not a sequent.'},
          {tac: 'refine ⟨h₁, h₂, hd, hu, ?_, ?_⟩',
           state: 'case refine_1\nP P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ P\' σ h₁\n\ncase refine_2\nP P\' Q Q\' : Assertion\nhpq : P ⊢ P\'\nhrs : Q ⊢ Q\'\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ Q\' σ h₂',
           h: 'The two residual goals are <code>P\' σ h₁</code> and <code>Q\' σ h₂</code> — each localised to its own piece. That localisation is the entire theorem: the entailment about <code>P</code> is used at <code>h₁</code> and nowhere else, and it never has to know that <code>h₂</code> exists.'}
        ],
        done: 'Closed by hpq σ h₁ hp and hrs σ h₂ hq.'},

       {t: 'h4', s: 'The three lemmas, and when to reach for each'},

       {t: 'dl',
        items: [
          {k: '<code>star_mono hpq hrs</code>', h: 'Both sides change. Rare in practice, but it is the one that is actually proved.'},
          {k: '<code>star_mono_left R h</code>', h: '<code>P ∗ R ⊢ P\' ∗ R</code>. Read it as “improve the left conjunct, keep the frame <code>R</code>”. This is the shape that shows up when you are rewriting a precondition underneath a frame.'},
          {k: '<code>star_mono_right P h</code>', h: '<code>P ∗ Q ⊢ P ∗ Q\'</code>. “Keep the footprint, improve the frame.”'}
        ]},

       {t: 'p', h: 'A remark worth making now because it explains a lot of later proofs: <code>star_mono</code> is why <code>∗</code> behaves like a <i>functor</i> on the preorder of assertions. Combined with <code>entails_trans</code>, it means you can rewrite inside a star the way you would rewrite inside a sum — and exercise <b>m4-8</b> is nothing but that observation cashed in.'},

       {t: 'detail', title: 'What monotone does not give you', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'Monotone is not the same as <i>congruence for equivalence</i>, though it implies it: from <code>P ⊣⊢ P\'</code> you get both directions of <code>P ∗ Q ⊣⊢ P\' ∗ Q</code> by applying <code>star_mono_left</code> twice. What you do <b>not</b> get is anti-monotonicity anywhere, and in particular there is no rule taking <code>P ∗ Q ⊢ R</code> to <code>P ⊢ R</code>. Weakening under <code>∗</code> only ever goes in the direction the arrows point.'},
          {t: 'p', h: 'The magic wand of M11 is exactly the adjoint that repairs this: <code>P ∗ Q ⊢ R</code> if and only if <code>P ⊢ Q −∗ R</code>. Monotonicity of <code>∗</code> is what makes that adjunction well behaved.'}
        ]}
     ],

     pitfall: 'Forgetting that an entailment eats three arguments. Writing <code>hpq h₁ hp</code> instead of <code>hpq σ h₁ hp</code> gives <code>Application type mismatch: The argument h₁ has type Heap but is expected to have type Store</code> — Lean is telling you the very first argument is wrong, which is easy to misread as a problem with <code>h₁</code> itself. Writing <code>hpq σ h hp</code> (the whole heap instead of the piece) fails differently, and the error moves to the third argument: <code>The argument hp has type P σ h₁ but is expected to have type P σ h</code>. The rule is that an entailment must be applied at the heap where the assertion actually holds.',

     variants: 'Weaken the hypotheses to a single entailment <code>P ⊢ P\'</code> and you get <code>star_mono_left</code>, which is strictly less useful but still true. Reverse one hypothesis — try to prove <code>P ∗ Q ⊢ P\' ∗ Q\'</code> from <code>P\' ⊢ P</code> — and you are stuck at slot 5 with an entailment pointing the wrong way; there is no way to turn <code>P σ h₁</code> into <code>P\' σ h₁</code>, and no amount of heap manipulation helps, because the heap was never the obstacle. Drop monotonicity entirely and the frame rule of M8 still holds, but every application of it in M9 would need its precondition to match the command’s footprint <i>syntactically</i> — which is exactly the pain <code>star_mono</code> removes.'
    },

    {t: 'ex',
     id: 'm4-6',
     name: 'star_or_left / star_exists_left',
     hard: false,

     why: '<code>∗</code> distributes over <code>∨</code> and commutes with <code>∃</code>. The existential one is used in <i>every</i> proof about linked lists, because recursive predicates are existentially quantified over the next pointer. M10 defines <code>listRep (x :: xs) p</code> as <code>aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next</code>, so an <code>∃</code> sits under every cons. <code>star_exists_left</code> is what pulls it out to the front of a bigger star, and it is the first line of the inductive step in both <code>lseg_append</code> and <code>lseg_listRep</code>.',

     setup: 'Recall <code>aOr P Q := fun σ h => P σ h ∨ Q σ h</code> and <code>aExists P := fun σ h => ∃ x, P x σ h</code>. New here: <code>rcases … with … | …</code> for case-splitting a disjunction.',

     goal: 'theorem star_or_left (P Q R : Assertion) :\n    (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R)\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q)',

     hints: [
       'Both are “destructure, then rebuild with the same cut”. Nothing moves. In particular you will never touch <code>hd</code> or <code>hu</code> — they are copied across unchanged in every branch.',
       'For <code>star_or_left</code>: after the six-name destructuring, slot 5 has type <code>aOr P Q σ h₁</code>, which is definitionally a disjunction. Split it with <code>rcases hpq with hp | hq</code>, which produces two goals.',
       'The goal <code>aOr (P ∗ R) (Q ∗ R) σ h</code> is definitionally <code>(P ∗ R) σ h ∨ (Q ∗ R) σ h</code>, so you close each branch with <code>Or.inl</code> or <code>Or.inr</code> applied to a full six-slot tuple.',
       'For <code>star_exists_left</code>: nest the destructuring, <code>⟨x, hp⟩</code> in slot 5. The goal is <code>aExists …</code>, i.e. <code>∃ x, …</code>, so its tuple starts with the witness: <code>⟨x, h₁, h₂, hd, hu, hp, hq⟩</code> — seven components, the first being <code>x</code>.'
     ],

     sol: 'theorem star_or_left (P Q R : Assertion) : (aOr P Q) ∗ R ⊢ aOr (P ∗ R) (Q ∗ R) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩\n  rcases hpq with hp | hq\n  · exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩\n  · exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩\n\ntheorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists P ∗ Q ⊢ aExists (fun x => P x ∗ Q) := by\n  intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩\n  exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩',

     expl: 'In <code>star_exists_left</code> the witness <code>x</code> simply travels from the hypothesis to the goal; the heap cut is unchanged. It is worth noting that the reverse direction also holds and is equally easy — unlike the <code>∀</code> case, where only one direction is provable.',

     walk: [
       {tac: 'intro σ h ⟨h₁, h₂, hd, hu, hpq, hr⟩', h: 'Slot 5 is named <code>hpq</code> because it holds the disjunction, not a proof of <code>P</code>.'},
       {tac: 'rcases hpq with hp | hq', h: '<code>rcases</code> is <code>obtain</code>’s pattern language applied to an existing hypothesis; the bar <code>|</code> separates <i>alternatives</i> rather than components, so this splits the goal in two. In the first branch <code>hp : P σ h₁</code>; in the second <code>hq : Q σ h₁</code> — note both live at <code>h₁</code>, since the cut did not change. Lean labels the branches <code>case inl</code> and <code>case inr</code>.'},
       {tac: '· exact Or.inl ⟨h₁, h₂, hd, hu, hp, hr⟩', h: 'The goal <code>aOr (P ∗ R) (Q ∗ R) σ h</code> unfolds to a disjunction; <code>Or.inl</code> selects the left disjunct, whose content is <code>(P ∗ R) σ h</code>, and the tuple provides the same cut as before with <code>hp</code> in slot 5.'},
       {tac: '· exact Or.inr ⟨h₁, h₂, hd, hu, hq, hr⟩', h: 'Identical with <code>Or.inr</code> and <code>hq</code>. The two branches differ in exactly two tokens, which is the visible form of “<code>∗</code> did not care which disjunct held”.'},
       {tac: 'theorem star_exists_left {α : Sort u} (P : α → Assertion) (Q : Assertion) : …', h: 'The existential version. <code>α : Sort u</code> rather than <code>Type</code> so the index may itself be a proposition — occasionally useful, and free.'},
       {tac: 'intro σ h ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩', h: 'The nested <code>⟨x, hp⟩</code> takes apart <code>aExists P σ h₁</code>, binding the witness <code>x</code> and the proof <code>hp : P x σ h₁</code> in one go.'},
       {tac: 'exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩', h: 'Seven slots now: the witness first, then the usual six. The witness is the <i>same</i> <code>x</code> you received — that is the whole content of the lemma. Everything else is copied.'}
     ],

     deep: [
       {t: 'trace', title: 'star_or_left: the split, and why both branches look alike',
        start: 'P Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhpq : aOr P Q σ h₁\nhr : R σ h₂\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
        steps: [
          {tac: 'rcases hpq with hp | hq',
           state: 'case inl\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhr : R σ h₂\nhp : P σ h₁\n⊢ aOr (P ∗ R) (Q ∗ R) σ h\n\ncase inr\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhr : R σ h₂\nhq : Q σ h₁\n⊢ aOr (P ∗ R) (Q ∗ R) σ h',
           h: 'Two contexts identical except for one hypothesis. Note that <code>hpq</code> displayed as <code>aOr P Q σ h₁</code> — an application of a <code>def</code>, not a visible <code>∨</code> — and <code>rcases</code> split it anyway, because it unfolds the definition to find the inductive type underneath. The case names <code>inl</code>/<code>inr</code> come from <code>Or</code>’s constructors.'}
        ],
        done: 'Each branch closed by Or.inl / Or.inr applied to the unchanged cut.'},

       {t: 'trace', title: 'star_exists_left: the witness travels, the heap does not',
        start: 'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nx : α\nhp : P x σ h₁\nhq : Q σ h₂\n⊢ aExists (fun x => P x ∗ Q) σ h',
        steps: [
          {tac: 'refine ⟨x, ?_⟩',
           state: 'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nx : α\nhp : P x σ h₁\nhq : Q σ h₂\n⊢ (fun x => P x ∗ Q) x σ h',
           h: 'Supplying the witness leaves an unreduced beta-redex <code>(fun x => P x ∗ Q) x σ h</code> in the goal. Lean does not beta-reduce for display, but <code>exact ⟨h₁, h₂, hd, hu, hp, hq⟩</code> is checked up to definitional equality, so it goes through as if the goal read <code>(P x ∗ Q) σ h</code>. If the redex bothers you, <code>show (P x ∗ Q) σ h</code> replaces it with the reduced form — and Lean accepts that <code>show</code>, which is itself the proof that the two are the same goal.'}
        ],
        done: 'No goals, after exact ⟨h₁, h₂, hd, hu, hp, hq⟩. The shipped proof writes the witness and those six slots as a single seven-component tuple; the refine here only exists to show where the beta-redex comes from.'},

       {t: 'p', h: 'The converse of <code>star_or_left</code> is also true and just as short, so <code>∗</code> genuinely <i>distributes</i> over <code>∨</code> rather than merely half-distributing:'},

       {t: 'code', tag: 'illustration',
        cap: 'The other direction — a case split on the outer disjunction instead of the inner one.',
        src: 'theorem star_or_left_conv (P Q R : Assertion) :\n    aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by\n  intro σ h hor\n  rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩\n  · exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩\n  · exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩'},

       {t: 'detail', title: 'The ∀ case, and why it only goes one way', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'The forward direction is as easy as the existential one — introduce the universally quantified variable after destructuring and hand it to the hypothesis:'},
          {t: 'code', tag: 'illustration',
           src: 'def aForall {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∀ x, P x σ h\n\ntheorem star_forall_left {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aForall P ∗ Q ⊢ aForall (fun x => P x ∗ Q) := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩ x\n  exact ⟨h₁, h₂, hd, hu, hp x, hq⟩'},
          {t: 'p', h: 'The converse fails, and the reason is exactly the existential quantifier hiding inside <code>∗</code>. <code>aForall (fun x => P x ∗ Q)</code> says: <i>for each</i> <code>x</code> there is <i>some</i> cut making <code>P x</code> and <code>Q</code> true. The cut may depend on <code>x</code>. <code>aForall P ∗ Q</code> demands a <i>single</i> cut that works for every <code>x</code> at once. Quantifier order, nothing more.'},
          {t: 'p', h: 'Here is the counterexample, machine-checked. Index by <code>Bool</code>; let <code>P false</code> own cell 0 and <code>P true</code> own cell 1; take <code>Q = aTrue</code>, which will happily absorb whatever is left over. On the heap containing both cells the left-hand side holds — cut one way for <code>false</code>, the other way for <code>true</code> — while the right-hand side would force one heap to be both singletons at once.'},
          {t: 'code', tag: 'illustration',
           cap: 'A genuine refutation, not a failed proof attempt.',
           src: 'def Pcx : Bool → Assertion\n  | false => (0 ↦ 4)\n  | true  => (1 ↦ 7)\n\ntheorem star_forall_right_fails :\n    ¬ (aForall (fun x => Pcx x ∗ aTrue) ⊢ aForall Pcx ∗ aTrue) := by\n  intro hcontra\n  have hlhs : aForall (fun x => Pcx x ∗ aTrue) (fun _ => 0)\n      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) := by\n    intro x\n    cases x with\n    | false =>\n        exact ⟨Heap.singleton 0 4, Heap.singleton 1 7,\n          singleton_disjoint 4 7 (by simp), rfl, rfl, trivial⟩\n    | true =>\n        refine ⟨Heap.singleton 1 7, Heap.singleton 0 4,\n          singleton_disjoint 7 4 (by simp), ?_, rfl, trivial⟩\n        exact union_comm (singleton_disjoint 4 7 (by simp))\n  obtain ⟨h₁, h₂, _, _, hall, _⟩ := hcontra _ _ hlhs\n  have e0 : h₁ = Heap.singleton 0 4 := hall false\n  have e1 : h₁ = Heap.singleton 1 7 := hall true\n  have : Heap.singleton 0 4 0 = Heap.singleton 1 7 0 := by rw [← e0, ← e1]\n  rw [singleton_same, singleton_other 1 0 7 (by simp)] at this\n  exact absurd this (by simp)'},
          {t: 'p', h: 'The last four lines are the whole argument: <code>hall</code> gives <code>h₁ = singleton 0 4</code> and <code>h₁ = singleton 1 7</code>, so the two singletons are equal; evaluate at location 0 and you get <code>some 4 = none</code>.'},
          {t: 'p', h: 'Five pieces of that snippet are used here for the first time in the chapter. None is deep, but none has been introduced, so:'},
          {t: 'dl', items: [
            {k: '<code>cases x with | false => … | true => …</code>', h: 'Case analysis on an inductive value. The branch labels are the <i>constructor names</i> of <code>Bool</code>, and Lean checks you have covered all of them. It is the tactic form of the pattern match that defines <code>Pcx</code> two lines above.'},
            {k: '<code>trivial</code>', h: 'Closes the goal <code>aTrue σ h₂</code>. <code>aTrue</code> unfolds to <code>fun _ _ => True</code>, and <code>trivial</code> proves <code>True</code>. This is the slot where <code>aTrue</code> earns its keep: it absorbs whatever heap is left over without saying anything about it.'},
            {k: '<code>singleton_disjoint 4 7 (by simp)</code>', h: 'M2’s builder, the <code>.mpr</code> direction of <code>singleton_disjoint_iff</code> under another name. The <i>values</i> <code>4</code> and <code>7</code> are explicit and the locations are implicit, so you pass values and Lean reads the locations off the expected type; <code>by simp</code> discharges the side condition <code>0 ≠ 1</code>, which on numerals <code>simp</code> decides outright.'},
            {k: '<code>hcontra _ _ hlhs</code>', h: 'An entailment eats a store, a heap and a proof (see <b>m4-5</b>). Both <code>_</code>s are determined by the type of <code>hlhs</code>, so there is no need to write the store and the heap out again.'},
            {k: '<code>absurd this (by simp)</code>', h: '<code>absurd : a → ¬a → b</code>. Here <code>this : some 4 = none</code> and <code>by simp</code> supplies <code>¬ (some 4 = none)</code> — two different constructors of <code>Option</code> can never be equal — so the pair produces the <code>False</code> the goal wanted. Note also <code>rw [← e0, ← e1]</code> earlier: the arrow reverses the rewrite, using each equation right to left.'}
          ]}
        ]}
     ],

     pitfall: 'Expecting <code>rcases</code> to fail because the hypothesis “is not an <code>Or</code>”. Its type displays as <code>aOr P Q σ h₁</code>, which looks like an opaque application, and a reader who has been told “<code>rcases</code> works on inductive types” may go hunting for an <code>unfold aOr</code> first. It is not needed: <code>rcases</code> whnf-reduces the type before matching. The same applies to <code>obtain</code> on <code>aExists</code>, and to <code>subst</code>/<code>rw</code> on <code>emp</code> and <code>↦</code>. Definitional transparency is doing a lot of quiet work throughout this chapter.',

     variants: 'There is no <code>star_or_right</code> in the corpus because <code>star_comm</code> plus <code>star_or_left</code> gives it in two lines — derive rather than reprove. Replace <code>∨</code> by <code>∧</code> and the forward statement <code>(aAnd P Q) ∗ R ⊢ aAnd (P ∗ R) (Q ∗ R)</code> is still true — both conjuncts hold at the same <code>h₁</code>, so you hand the same four slots <code>⟨h₁, h₂, hd, hu, …⟩</code> to each half and change only slot 5. Its converse is <b>false</b>, and you already have the witness: take <code>P = 0 ↦ 4</code>, <code>Q = 1 ↦ 7</code>, <code>R = aTrue</code> and the two-cell heap. <code>(P ∗ R)</code> holds there by cutting <code>{0}</code> from <code>{1}</code>; <code>(Q ∗ R)</code> holds by cutting the other way; but <code>(aAnd P Q) ∗ R</code> would need one piece <code>h₁</code> equal to <code>Heap.singleton 0 4</code> and to <code>Heap.singleton 1 7</code> at the same time. That is <i>literally</i> the contradiction derived in <code>star_forall_right_fails</code> above — which is not a coincidence, because <code>∧</code> is a two-element <code>∀</code> and the machine-checked refutation is indexed by <code>Bool</code>. Two stars may hold with <i>different</i> cuts, and nothing forces them to agree.'
    },

    {t: 'p', h: 'Before the last two sections, the promised counterexample. M3 observed, when it introduced <code>and_left</code>, that there is no corresponding rule <code>P ∗ Q ⊢ P</code>. Here is the refutation, so that the claim is not merely an absence:'},

    {t: 'code', tag: 'illustration',
     cap: 'Separating conjunction has no projection. Forgetting a conjunct would mean leaking its memory.',
     src: 'theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by\n  intro hcontra\n  have hs : ((0 ↦ 4) ∗ (1 ↦ 7)) (fun _ => 0)\n      (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) :=\n    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩\n  have h := hcontra (fun _ => 0) _ hs\n  have h1 : Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7) 1\n      = Heap.singleton 0 4 1 := by rw [h]\n  rw [union_of_none _ (singleton_other 0 1 4 (by simp)), singleton_same,\n      singleton_other 0 1 4 (by simp)] at h1\n  exact absurd h1 (by simp)'},

    {t: 'p', h: 'The witness is a two-cell heap. If the entailment held, that heap would have to <i>be</i> the one-cell heap <code>Heap.singleton 0 4</code>; evaluating both at location 1 gives <code>some 7 = none</code>. Nothing subtle happens — but notice that the proof needed a concrete store, a concrete heap and concrete values. Refuting an entailment always does, because an entailment is a <code>∀</code> and its negation is a <code>∃</code>.'},

    {t: 'p', h: 'Two lines of that proof are dense enough to be worth unpacking. <code>hs</code> is a six-slot tuple like every other in this chapter, except that slot 4 is <code>rfl</code>: the heap in the statement was <i>written</i> as <code>Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)</code>, so the reassembly equation holds by reflexivity, and slots 5 and 6 are <code>rfl</code> for the same reason — <code>l ↦ v</code> unfolds to an equation between a heap and a singleton. The store <code>fun _ => 0</code> is arbitrary; nothing in the statement reads it. Then the long <code>rw … at h1</code> is three rewrites, each naming an M1/M2 lemma from outside this chapter’s toolbox: <code>union_of_none _ (singleton_other 0 1 4 …)</code> says the left piece is <code>none</code> at location 1, so the union there is whatever the right piece says; <code>singleton_same</code> evaluates that to <code>some 7</code>; and the second <code>singleton_other 0 1 4 …</code> evaluates the right-hand side <code>Heap.singleton 0 4 1</code> to <code>none</code>. What is left is <code>h1 : some 7 = none</code>, which <code>absurd h1 (by simp)</code> turns into <code>False</code>.'},

    {t: 'note', kind: 'warn', title: 'The consequence you will feel in M7',
     h: 'Because there is no projection, you can never “drop” an unused conjunct from a precondition. If a command needs <code>l ↦ v</code> and your precondition is <code>l ↦ v ∗ R</code>, you do not weaken to <code>l ↦ v</code> and proceed — you apply the <b>frame rule</b>, which carries <code>R</code> through to the postcondition. The absence of weakening is precisely what forces the frame rule to exist, and what makes it sound.'},

    /* ─────────────────────  ownership implies non-aliasing  ─────────── */
    {t: 'sec', s: 'Exercises · ownership implies non-aliasing'},

    {t: 'ex',
     id: 'm4-7',
     name: 'two_cells_distinct',
     hard: false,

     why: '<b>The punchline of Phase 1.</b> The precondition of a two-cell program already contains the non-aliasing information; you never have to hypothesise it. Every classical Hoare-logic treatment of pointer programs carries side conditions like “assuming <code>x</code> and <code>y</code> do not alias”; here that assumption has become a <i>consequence</i> of the precondition, which means it can never be forgotten and never has to be discharged separately. M10 cashes it in immediately: <code>node_cells_distinct</code>, which says a two-field node has <code>p ≠ p + 1</code>, is defined as <code>two_cells_distinct p (p + 1) x next</code> — one application, no proof.',

     setup: 'You need <code>singleton_disjoint_iff</code> from M2, and the fact that <code>l ↦ v</code> is by definition the equation <code>h = Heap.singleton l v</code>. The conclusion uses <code>fact</code>, not <code>pure</code> — see M3 if that distinction is not sharp yet.',

     goal: 'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)',

     hints: [
       'The only thing in the hypothesis that could possibly produce a disequality is the disjointness in slot 3. So name it, and discard the union equation with <code>_</code> — you will not need to know what <code>h</code> is.',
       'Slots 5 and 6 tell you that the two pieces are literal singletons. Substitute them so that <code>hd</code> becomes a statement about <code>Heap.singleton l₁ v₁</code> and <code>Heap.singleton l₂ v₂</code>.',
       '<code>subst hp; subst hq</code> — two <code>subst</code>s on one line, separated by a semicolon. Then <code>hd</code> is exactly the left-hand side of <code>singleton_disjoint_iff</code>, and <code>.mp</code> finishes it.'
     ],

     sol: 'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩\n  subst hp; subst hq\n  exact (singleton_disjoint_iff v₁ v₂).mp hd',

     expl: 'All the work was done in M2. The star gave you <code>hd : Heap.disjoint h₁ h₂</code>; the two <code>subst</code>s turn that into disjointness of two singletons; <code>singleton_disjoint_iff</code> converts it to <code>l₁ ≠ l₂</code>. Note the conclusion is <code>fact</code>, not <code>pure</code>: we are not giving up the heap, we are just reading a fact off it.',

     walk: [
       {tac: 'intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩', h: 'Slot 3 (disjointness) is the one that matters and gets a name; slot 4 (the union equation) is discarded, because the conclusion says nothing about <code>h</code>.'},
       {tac: 'subst hp', h: '<code>hp : (l₁ ↦ v₁) σ h₁</code>, definitionally <code>h₁ = Heap.singleton l₁ v₁</code>. <code>subst</code> sees through <code>pointsTo</code> and eliminates the variable <code>h₁</code>, so every occurrence — including the one inside <code>hd</code> — becomes the explicit singleton.'},
       {tac: 'subst hq', h: 'Same for <code>h₂</code>. After this line <code>hd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)</code>, which is a statement with no free heaps left in it at all.'},
       {tac: 'exact (singleton_disjoint_iff v₁ v₂).mp hd', h: 'The iff from M2, forward direction, applied to <code>hd</code>, yields <code>l₁ ≠ l₂</code>. The goal is <code>fact (fun x => l₁ ≠ l₂) σ h</code>, which unfolds to exactly that, so <code>exact</code> accepts it without any explicit unfolding. Why are the <i>values</i> written out and the locations not? Because M2 declared it <code>singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val)</code>: the locations are implicit and the values explicit. Explicit arguments must be supplied positionally even when they are inferable, so <code>singleton_disjoint_iff.mp hd</code> is a parse error (<code>Unknown constant `singleton_disjoint_iff.mp`</code>) while <code>(singleton_disjoint_iff _ _).mp hd</code> works fine — here <code>hd</code> does determine them. The reason M2 made that choice is the <i>other</i> direction: <code>.mpr</code> is applied to a proof of <code>l₁ ≠ l₂</code>, which mentions no values at all, so there they cannot be inferred and must be given.'}
     ],

     deep: [
       {t: 'trace', title: 'two_cells_distinct — watch hd get more concrete',
        start: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nleft✝ : h = h₁.union h₂\nhp : (l₁ ↦ v₁) σ h₁\nhq : (l₂ ↦ v₂) σ h₂\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
        steps: [
          {tac: 'subst hp',
           state: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh h₂ : Heap\nhq : (l₂ ↦ v₂) σ h₂\nhd : (Heap.singleton l₁ v₁).disjoint h₂\nleft✝ : h = (Heap.singleton l₁ v₁).union h₂\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
           h: 'The variable <code>h₁</code> has vanished from the context entirely, replaced everywhere by the singleton — including inside <code>hd</code>, which is the only place it mattered. Two incidental display facts: the discarded union equation is still there under the inaccessible name <code>left✝</code> and has been rewritten too; and the anonymous binder in the goal prints as <code>fun x =></code> even though the source wrote <code>fun _ =></code>.'},
          {tac: 'subst hq',
           state: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nleft✝ : h = (Heap.singleton l₁ v₁).union (Heap.singleton l₂ v₂)\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
           h: 'Now <code>hd</code> is literally the left-hand side of <code>singleton_disjoint_iff</code>. Everything after this is M2.'},
          {tac: 'show l₁ ≠ l₂',
           state: 'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nleft✝ : h = (Heap.singleton l₁ v₁).union (Heap.singleton l₂ v₂)\n⊢ l₁ ≠ l₂',
           h: 'Optional, and not in the shipped proof — but it is worth doing once to see that the goal really was a disequality wearing a <code>fact</code> costume. This is M0’s advice about <code>show</code> paying off.'}
        ],
        done: 'No goals, after exact (singleton_disjoint_iff v₁ v₂).mp hd.'},

       {t: 'steps', title: 'Where the information actually comes from',
        items: [
          {k: 'The star supplies disjointness for free', h: 'You did not assume <code>l₁ ≠ l₂</code>. You assumed a <i>separating</i> conjunction, and disjointness is one of its six components — component 3, which the previous four exercises never needed.'},
          {k: 'The points-to assertions make the pieces concrete', h: '<code>l ↦ v</code> is <b>exact</b> ownership: the heap <i>is</i> the singleton, not merely contains it. That is what turns <code>hd</code> into a statement about two literal singletons, which is the left-hand side of an M2 lemma. But be careful about what exactness is doing here — it makes the proof <i>short</i>, and it is not what makes the theorem <i>true</i>. See the aside below.'},
          {k: 'M2 converts disjoint singletons to a disequality', h: 'Two singletons are disjoint iff their locations differ. That is the entire mathematical content, and it was proved two chapters ago.'}
        ]},

       {t: 'detail', title: 'Exactness is not what makes this theorem true', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'The natural reading of the proof is “exact ownership gives you non-aliasing”. That reading is wrong, and it is worth breaking, because the correct statement points at something you will need in M8.'},
          {t: 'p', h: 'Replace <code>pointsTo</code> by the “at least this” version and non-aliasing <b>survives</b>. Disjointness alone is enough:'},
          {t: 'code', tag: 'illustration',
           cap: 'The weaker points-to still forces the locations apart.',
           src: 'def pointsToAtLeast (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v\n\ntheorem two_cells_distinct_atleast (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    pointsToAtLeast l₁ v₁ ∗ pointsToAtLeast l₂ v₂ ⊢ fact (fun _ => l₁ ≠ l₂) := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩ heq\n  subst heq\n  rcases hd l₁ with hn | hn\n  · rw [hp] at hn; exact absurd hn (by simp)\n  · rw [hq] at hn; exact absurd hn (by simp)'},
          {t: 'p', h: 'That proof is the pitfall below, done deliberately. The extra <code>heq</code> in the <code>intro</code> pattern works because the goal unfolds to <code>l₁ = l₂ → False</code>; <code>subst heq</code> then eliminates <code>l₂</code> in favour of <code>l₁</code>, and <code>hd l₁ : h₁ l₁ = none ∨ h₂ l₁ = none</code> contradicts <code>hp</code> in the first branch and <code>hq</code> in the second. Five lines instead of three, and no exactness anywhere.'},
          {t: 'p', h: 'What exactness <i>is</i> load-bearing for is the absence of weakening. Under the “at least this” reading, <code>l ↦ v ∗ Q ⊢ l ↦ v</code> becomes provable for every <code>Q</code>, because the left piece’s cell survives into the union:'},
          {t: 'code', tag: 'illustration',
           cap: 'Drop exactness and ownership becomes forgettable. This is what actually breaks.',
           src: 'theorem atleast_star_weakening (l : Loc) (v : Val) (Q : Assertion) :\n    pointsToAtLeast l v ∗ Q ⊢ pointsToAtLeast l v := by\n  intro σ h ⟨h₁, h₂, _, hu, hp, _⟩\n  subst hu\n  exact union_of_some h₂ hp'},
          {t: 'p', h: 'That last proof is three lines because M1 already has the lemma: <code>union_of_some h₂ hp</code> turns <code>hp : h₁ l = some v</code> into <code>Heap.union h₁ h₂ l = some v</code>, which <i>is</i> the goal once <code>pointsToAtLeast</code> is unfolded. Compare it with <code>no_star_weakening</code> earlier in the chapter, which refutes the same shape for the <i>exact</i> points-to. So the slogan to keep is not “exactness gives you non-aliasing” — disjointness gives you that — but <b>exactness gives you the absence of weakening</b>: a resource you cannot silently forget. That absence is what forces the frame rule to exist in M8, and it is the reason M3 chose the exact reading.'}
        ]},

       {t: 'detail', title: 'Why fact and not pure — and why it matters here specifically', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'M3 defined <code>pure φ := aAnd (fact φ) emp</code>. If the conclusion of this theorem were <code>pure (fun _ => l₁ ≠ l₂)</code>, it would additionally assert <code>h = Heap.empty</code> — that after learning the two locations differ you own nothing. That is false, and worse, it is the kind of false statement that typechecks and looks reasonable.'},
          {t: 'p', h: 'The rule of thumb: <code>fact</code> is what you conclude when you are <i>reading</i> information off a heap you still hold; <code>pure</code> is what you write when you want to <i>combine</i> a proposition with a star, because the <code>emp</code> makes the left piece of the cut empty. Exercise <b>m4-8</b> makes that second half precise.'}
        ]}
     ],

     pitfall: 'Trying to prove the goal “directly” with <code>intro heq</code>, on the grounds that <code>l₁ ≠ l₂</code> is an implication into <code>False</code>. It works — the goal <code>fact (fun x => l₁ ≠ l₂) σ h</code> really is an implication after two unfoldings — but you then have to rediscover, by hand, the contradiction that <code>singleton_disjoint_iff</code> already packages. The habit to build is: look for the M2 lemma whose left-hand side matches a hypothesis you already have, rather than reasoning from the definitions.',

     variants: 'Reverse the ownership: state the same thing with <code>aAnd</code> instead of <code>∗</code> and it becomes <b>false</b> — <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)</code> fails at <code>l₁ = l₂</code>, <code>v₁ = v₂</code>, because both conjuncts then describe the same one-cell heap perfectly well. Indeed M3’s <code>pointsTo_value_unique</code> pushes the other way in that setting: from <code>aAnd (l ↦ v₁) (l ↦ v₂)</code> you conclude <code>v₁ = v₂</code>, since both conjuncts pin the same heap to be a singleton. So the theorem really is about <code>∗</code>, and <code>∧</code> kills it. What it is <i>not</i> about is exactness: drop exactness from <code>pointsTo</code> and the statement stays true, as the aside above machine-checks. The single moving part is slot 3 of the star, and nothing else.'
    },

    /* ────────────────────  a small normalisation library  ───────────── */
    {t: 'sec', s: 'Exercises · a small normalisation library'},

    {t: 'p', h: 'Assemble these now; from M9 on you will use them constantly to line up a precondition with the footprint of the next command.'},

    {t: 'p', h: 'This is also the point where the chapter changes character. Everything so far was proved by opening up <code>star</code> and moving heaps around. From here on you should be proving things by <i>composing lemmas you already have</i> — and if you find yourself typing <code>intro σ h ⟨…⟩</code> for something like <code>star_swap_middle</code>, stop: you are re-doing work.'},

    {t: 'ex',
     id: 'm4-8',
     name: 'star_swap_middle, star_rotate_left/right, star_pure_left/right',
     hard: false,

     why: '<code>star_swap_middle</code> should be built <i>from</i> associativity and commutativity, not proved from scratch — that is the point of having an algebra. The <code>pure</code> pair formalises the slogan “<code>pure φ ∗ P ≡ φ ∧ P</code>”, which is how a side condition gets moved in and out of a separating conjunction. You will meet the shape again rather than the lemma: M9 proves <code>pure_star_regroup : pure φ ∗ (P ∗ R) ⊢ (aAnd (fact φ) P) ∗ R</code> — <code>star_pure_left</code> with a frame threaded through — and its proof is the same four moves you are about to write.',

     setup: 'You have <code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>star_comm</code>, <code>star_mono_left</code> and <code>entails_trans</code>. For the <code>pure</code> pair, recall <code>pure φ = aAnd (fact φ) emp</code>, so destructuring it gives you a <i>pair</i> in slot 5: the proposition and the emptiness of the heap.',

     goal: 'theorem star_swap_middle  (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R)\ntheorem star_rotate_left  (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R\ntheorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)\n\ntheorem star_pure_left  (φ : Store → Prop) (P : Assertion) : pure φ ∗ P ⊢ aAnd (fact φ) P\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) : aAnd (fact φ) P ⊢ pure φ ∗ P',

     hints: [
       'The two <code>rotate</code> lemmas are renamings: each is one of the associativity lemmas with its arguments in the obvious order. Write them as term-mode definitions with no <code>by</code> at all.',
       '<code>star_swap_middle</code>: rotate left, swap the first two with <code>star_mono_left … (star_comm …)</code>, rotate right. Chain with <code>entails_trans</code>. Draw the three intermediate assertions before you type anything.',
       'For <code>star_pure_left</code>: destructure as usual, but slot 5 is itself a pair, so write <code>⟨hφ, he⟩</code> there. Then <code>he</code> is the emptiness equation — <code>subst</code> it, rewrite the goal’s heap with <code>hu</code> and <code>union_empty_left</code>, and pair up what is left.',
       'For <code>star_pure_right</code>: you are building a star out of an <code>aAnd</code>, so the cut is forced — <code>Heap.empty</code> on the left, all of <code>h</code> on the right. Slot 5 must prove <code>pure φ σ Heap.empty</code>, which is a pair: <code>⟨hφ, rfl⟩</code>.'
     ],

     sol: 'theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=\n  entails_trans (star_assoc_right P Q R)\n    (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))\n\ntheorem star_rotate_left (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=\n  star_assoc_right P Q R\n\ntheorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) :=\n  star_assoc_left P Q R\n\ntheorem star_pure_left (φ : Store → Prop) (P : Assertion) :\n    pure φ ∗ P ⊢ aAnd (fact φ) P := by\n  intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩\n  subst he\n  rw [hu, union_empty_left]\n  exact ⟨hφ, hp⟩\n\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) :\n    aAnd (fact φ) P ⊢ pure φ ∗ P := by\n  intro σ h ⟨hφ, hp⟩\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩',

     expl: 'Look at <code>star_swap_middle</code>: it is a three-step composition of lemmas with no <code>intro</code> at all. When your separation-logic proofs start looking like this — equational reasoning at the level of assertions — you have crossed the line from “semantic grinding” to “using the logic”.',

     walk: [
       {tac: 'entails_trans (star_assoc_right P Q R)', h: 'Step one of the chain: <code>P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R</code>. Re-bracket so that the two assertions you want to swap are adjacent inside a single sub-star.'},
       {tac: '(entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))', h: 'Steps two and three, nested. <code>star_comm P Q : P ∗ Q ⊢ Q ∗ P</code>; <code>star_mono_left R</code> lifts that entailment to hold underneath the frame <code>R</code>, giving <code>(P ∗ Q) ∗ R ⊢ (Q ∗ P) ∗ R</code>. Then <code>star_assoc_left Q P R</code> re-brackets back: <code>(Q ∗ P) ∗ R ⊢ Q ∗ (P ∗ R)</code>. Composing all three gives the statement.'},
       {tac: 'theorem star_rotate_left … := star_assoc_right P Q R', h: 'A pure renaming. Worth having because at the point of use, “rotate” describes what you are doing to a precondition, while “assoc” describes a law; the same term serves both.'},
       {tac: 'theorem star_rotate_right … := star_assoc_left P Q R', h: 'The mirror renaming. Note the crossing: <code>rotate_left</code> is <code>assoc_right</code> and vice versa, because one name describes the movement and the other the destination bracketing.'},
       {tac: 'intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩', h: 'The <code>pure</code> lemma. Slot 5 has type <code>pure φ σ h₁</code>, which is <code>aAnd (fact φ) emp σ h₁</code>, which is a conjunction — hence the nested <code>⟨hφ, he⟩</code>, giving the proposition and the emptiness of <code>h₁</code>. Slot 3 is discarded: two heaps one of which is empty are automatically disjoint, so it carries no information.'},
       {tac: 'subst he', h: '<code>he : emp σ h₁</code>, i.e. <code>h₁ = Heap.empty</code>. <code>subst</code> eliminates <code>h₁</code>, so <code>hu</code> becomes <code>h = Heap.empty.union h₂</code> and <code>hφ</code> becomes a statement at <code>Heap.empty</code>.'},
       {tac: 'rw [hu, union_empty_left]', h: 'Rewrite the goal’s heap from <code>h</code> to <code>Heap.empty.union h₂</code> to <code>h₂</code>. Now the goal is <code>aAnd (fact φ) P σ h₂</code>. The heap has been reduced to the piece that <code>P</code> owns, which is the whole point: <code>pure</code> contributed nothing.'},
       {tac: 'exact ⟨hφ, hp⟩', h: 'An <code>aAnd</code> is a pair. <code>hφ : fact φ σ Heap.empty</code> is accepted for <code>fact φ σ h₂</code> because <code>fact</code> ignores its heap argument entirely — the two types are definitionally equal.'},
       {tac: 'intro σ h ⟨hφ, hp⟩', h: 'The converse. The hypothesis is an ordinary conjunction, so two names.'},
       {tac: 'exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩', h: 'The cut is forced: <code>pure</code> demands an empty left piece. Slots 1–4 are the same as in <b>m4-2</b>. Slot 5 is where the two halves of <code>pure</code> get supplied: <code>hφ</code> for the proposition and <code>rfl</code> for <code>Heap.empty = Heap.empty</code>. Slot 6 is <code>hp</code>, still holding the entire heap.'}
     ],

     deep: [
       {t: 'steps', title: 'star_swap_middle as a chain — write the intermediate assertions first',
        items: [
          {k: 'Start', h: '<code>P ∗ (Q ∗ R)</code>'},
          {k: '<code>star_assoc_right P Q R</code>', h: '<code>(P ∗ Q) ∗ R</code> — bring <code>P</code> and <code>Q</code> next to each other inside one bracket.'},
          {k: '<code>star_mono_left R (star_comm P Q)</code>', h: '<code>(Q ∗ P) ∗ R</code> — swap them, without disturbing <code>R</code>. This is the only step that does real work, and it does it by <i>reusing</i> <code>star_comm</code> at a smaller scope.'},
          {k: '<code>star_assoc_left Q P R</code>', h: '<code>Q ∗ (P ∗ R)</code> — re-bracket back to the shape the statement wants.'},
          {k: 'Glue', h: 'Two applications of <code>entails_trans</code>, nested to the right. There is no <code>intro</code>, no heap, no <code>⟨…⟩</code> anywhere in the proof.'}
        ]},

       {t: 'state', cap: 'The three steps as Lean sees them, written out with have. Note P ∗ Q ∗ R is P ∗ (Q ∗ R).',
        src: 'P Q R : Assertion\ns1 : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R\ns2 : (P ∗ Q) ∗ R ⊢ (Q ∗ P) ∗ R\ns3 : (Q ∗ P) ∗ R ⊢ Q ∗ P ∗ R\n⊢ P ∗ Q ∗ R ⊢ Q ∗ P ∗ R'},

       {t: 'trace', title: 'star_pure_left, tactic by tactic',
        start: 'φ : Store → Prop\nP : Assertion\n⊢ _root_.pure φ ∗ P ⊢ aAnd (fact φ) P',
        steps: [
          {tac: 'intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩',
           state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhφ : fact φ σ h₁\nhe : emp σ h₁\nhp : P σ h₂\n⊢ aAnd (fact φ) P σ h',
           h: 'The nested pattern in slot 5 produced <i>two</i> hypotheses, <code>hφ</code> and <code>he</code>, where the six-slot pattern would have produced one. Seven names for a star whose left conjunct is a conjunction — the flattening is automatic and goes as deep as you write brackets.'},
          {tac: 'subst he',
           state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₂ : Heap\nhp : P σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhφ : fact φ σ Heap.empty\n⊢ aAnd (fact φ) P σ h',
           h: '<code>h₁</code> is gone. Watch <code>hφ</code>: it is now stated at <code>Heap.empty</code>, which will not matter at all, because <code>fact</code> discards its heap argument. That is the entire reason <code>fact</code> exists as a separate definition from <code>pure</code>.'},
          {tac: 'rw [hu, union_empty_left]',
           state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₂ : Heap\nhp : P σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhφ : fact φ σ Heap.empty\n⊢ aAnd (fact φ) P σ h₂',
           h: 'The goal’s heap has shrunk from <code>h</code> to <code>h₂</code>. Both remaining obligations now live at <code>h₂</code>, and both are in the context.'}
        ],
        done: 'No goals, after exact ⟨hφ, hp⟩.'},

       {t: 'trace', title: 'star_pure_right — the forced cut',
        start: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh : Heap\nhφ : fact φ σ h\nhp : P σ h\n⊢ (_root_.pure φ ∗ P) σ h',
        steps: [
          {tac: 'refine ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ?_, hp⟩',
           state: 'φ : Store → Prop\nP : Assertion\nσ : Store\nh : Heap\nhφ : fact φ σ h\nhp : P σ h\n⊢ _root_.pure φ σ Heap.empty',
           h: 'One obligation left, and it is the interesting one: <code>pure φ</code> must hold at the <b>empty</b> heap. It unfolds to <code>fact φ σ Heap.empty ∧ Heap.empty = Heap.empty</code>, so <code>⟨hφ, rfl⟩</code> closes it — <code>hφ</code> transports from <code>h</code> to <code>Heap.empty</code> for free because <code>fact</code> ignores heaps.'}
        ],
        done: 'No goals, after exact ⟨hφ, rfl⟩. The shipped proof writes that pair inline in slot 5 of a single exact; the hole here only exists to show what slot 5 was actually asking for.'},

       {t: 'detail', title: 'Why _root_.pure appears in every goal here', tag: 'aside', open: false,
        blocks: [
          {t: 'p', h: 'Lean’s core library defines <code>Pure.pure</code>, the monadic <code>pure</code>, and exports it as <code>pure</code>. Our M3 definition also lives at the root namespace under the same name. Both are in scope, so the pretty-printer writes ours as <code>_root_.pure</code> to be unambiguous. Your source can still say plain <code>pure φ</code>: the name is overloaded, Lean elaborates both candidates against the expected type <code>Assertion</code>, and the <code>Pure.pure</code> reading is discarded because there is no <code>Pure</code> instance that would make it an <code>Assertion</code>. Exactly one candidate survives, so there is no ambiguity error.'},
          {t: 'p', h: 'This is worth knowing mostly so that you do not go looking for a mistake when a goal you wrote as <code>pure φ ∗ P</code> comes back as <code>_root_.pure φ ∗ P</code>. Nothing changed.'}
        ]},

       {t: 'cmp',
        left:  {t: 'Proving star_swap_middle from scratch', kind: 'bad',
                h: 'Destructure two nested stars, produce three heaps, derive three pairwise disjointness facts, choose a new cut, prove <code>h = hQ ∪ (hP ∪ hR)</code> from <code>h = hP ∪ (hQ ∪ hR)</code> using <code>union_assoc</code> twice and <code>union_comm</code> once with the right disjointness proof… It is perhaps fifteen lines and every one of them can go wrong.'},
        right: {t: 'Composing three lemmas', kind: 'good',
                h: 'Three lines, no heaps, no <code>intro</code>. Every heap-level fact needed was already proved and named. This is what an algebra is <i>for</i>, and it is the working style of every chapter from M9 onward.',
                tag: 'sketch',
                src: 'entails_trans (star_assoc_right P Q R)\n  (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))'}}
     ],

     pitfall: 'Mixing up which rotate is which. <code>star_rotate_left</code> has the <i>right</i>-associated assertion as its <b>hypothesis</b> and is defined as <code>star_assoc_right</code>; if you assume the names line up you will write a term whose type is the converse of what you need, and the error appears at the <code>entails_trans</code> that consumes it, not at the definition. When chaining, write the intermediate assertions down first — as in the <code>steps</code> block above — and only then pick lemma names.',

     variants: 'Replace <code>pure φ</code> by <code>fact φ</code> in <code>star_pure_left</code> and the statement becomes <b>false</b>. Without the <code>emp</code> component you no longer learn that <code>h₁</code> is empty, so <code>hu</code> gives you nothing, and the goal’s <code>P σ h</code> cannot be reached from <code>hp : P σ h₂</code>. The refutation is not literally <code>no_star_weakening</code>, but it is the same argument with the same numbers: take <code>φ</code> trivially true and <code>P = 1 ↦ 7</code>, and let <code>fact φ</code> own the cell at <code>0</code> in the two-cell heap. Then <code>(fact φ ∗ P)</code> holds there while <code>P</code> itself does not, because <code>P</code> is exact and the heap has two cells — which is the step <code>no_star_weakening</code> machine-checks. In the other direction, <code>star_pure_right</code> with <code>fact</code> in place of <code>pure</code> is still true — you may always cut off <code>Heap.empty</code>, since <code>fact</code> holds at every heap — but it is useless, because <code>fact φ ∗ P</code> does not pin the cut and so nothing can be recovered from it. That asymmetry is precisely M3’s point about which of the two pure-ish embeddings pairs with which connective.'
    },

    /* ────────────────────────────────  close  ───────────────────────── */
    {t: 'sec', s: 'What you now have'},

    {t: 'tbl',
     cap: 'The M4 library, and where each piece is next used. “Next appearance” means an actual later use in the development, not a vague promise — the ones that never come back are marked as such, and that is worth knowing too.',
     head: ['Law', 'Lemma(s)', 'Next appearance'],
     rows: [
       ['unit', '<code>star_emp_left</code>', 'M9 <code>moveCell_spec</code> — <code>free</code> leaves <code>emp ∗ (dst ↦ a)</code>'],
       ['unit, converses', '<code>star_emp_right</code>, <code>star_emp_*_intro</code>', 'not reused — they exist to make <code>⊣⊢</code> true, and to teach the construction side'],
       ['commutative', '<code>star_comm</code>', 'M4 <code>star_swap_middle</code>; M9 <code>copyCell_spec</code>, twice'],
       ['associative', '<code>star_assoc_left/right</code>', 'M9 <code>copyCell_spec</code>; M10 <code>lseg_append</code> and <code>lseg_listRep</code>, twice each'],
       ['monotone', '<code>star_mono</code>, <code>star_mono_left/right</code>', 'M9 <code>copyCell_spec</code>; M10, four times in the two list proofs'],
       ['distributes over <code>∃</code>', '<code>star_exists_left</code>', 'M10 — opens the <code>∃ next</code> under every cons'],
       ['distributes over <code>∨</code>', '<code>star_or_left</code>', 'not reused — but it is the law that makes case analysis under <code>∗</code> legal at all'],
       ['non-aliasing', '<code>two_cells_distinct</code>', 'M10 <code>node_cells_distinct</code> — one application, no proof'],
       ['normalisation', '<code>star_swap_middle</code>, <code>star_rotate_*</code>, <code>star_pure_*</code>', 'the <i>shape</i> returns as M9’s <code>pure_star_regroup</code>; the lemmas themselves are your own toolkit'],
       ['<i>no</i> weakening', '<code>no_star_weakening</code> (illustration)', 'M8 — why the frame rule has to carry <code>R</code> rather than drop it']
     ]},

    {t: 'p', h: 'M5 leaves resource algebra behind and introduces a tiny imperative language with a big-step semantics. Nothing in it mentions <code>∗</code>. The two threads meet in M6 and M7, where a Hoare triple is defined over that semantics and its rules are stated with the connective you built here.'},

    {t: 'dod', h: '<code>∗</code> is associative, commutative, monotone, distributes over <code>∨</code> and <code>∃</code>, and has <code>emp</code> as unit. Assertions with <code>∗</code> and <code>emp</code> form a commutative monoid, induced by the PCM of M2. You now have the assertion-level core of separation logic.'}
  ]
});
