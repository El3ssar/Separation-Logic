/* M2 — Disjointness, union, and the resource monoid
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m2 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm2',
  num: 'M2',
  phase: 'Phase 1 · Semantic foundations',
  title: 'Disjointness, union, and the resource monoid',
  blurb: 'The one heap law that is false as written, the hypothesis that buys it back, and the nine facts every law of ∗ is made of.',

  orient: {
    youWill: [
      'Write <code>Heap.union</code>, watch commutativity fail on two cells at the same address, and read off what the missing hypothesis has to say.',
      'Prove the nine laws that make <code>(Heap, union, empty)</code> a partial commutative monoid, and say for each one whether disjointness is needed — associativity is the interesting answer.',
      'Split on what a heap <i>answers</i> rather than on which location you are at, and know why the equation <code>cases hl :</code> saves is the only handle you get.',
      'Take a disjointness fact apart across a union and build a new one — the two directions that carry every re-bracketing in the rest of the course.',
      'Build proofs as terms: <code>Or.inl rfl</code>, <code>⟨hd, he⟩</code>, and a <code>refine</code> that discharges four obligations and leaves one.'
    ],
    needs: [
      'M1’s four heap operations. Only <code>Heap.empty</code> and <code>Heap.singleton</code> are used by name below, through their lookup equations.',
      '<code>funext</code> followed by a case split as the shape of every heap equality, and the anonymous constructor for <code>∧</code> and <code>∃</code>.'
    ],
    payoff: 'M4 defines <code>∗</code> by quantifying over the two heaps a heap splits into, so each of its laws is one of the nine below with a store and two assertion facts carried alongside. <code>star_comm</code>’s proof is <code>splits_comm</code>’s; <code>star_assoc_left</code>’s is <code>splits_assoc</code>’s. The algebra is settled here or it is settled nowhere.'
  },

  blocks: [

    /* ================================================================
       1 — union, and the law it breaks
       ================================================================ */

    { t: 'h3', s: 'Union, and the law it breaks' },

    { t: 'p', h: 'M1 fixed the shape: total, left-biased, disjointness travelling alongside. Here is the body. Note what it tests — not whether two locations agree, but whether the left heap answers at all.' },

    { t: 'anat',
      src: `def Heap.union (h₁ h₂ : Heap) : Heap :=
  fun l =>
    match h₁ l with
    | some v => some v
    | none   => h₂ l`,
      parts: [
        { m: 'fun l =>', h: 'The result is a <code>Heap</code>, so the body is a lambda. Nothing is allocated and no structure is built; <code>union</code> assembles a function pointwise, exactly as the four M1 operations do.' },
        { m: 'match h₁ l with', h: 'The scrutinee is the <i>left</i> heap. A <code>match</code> waits for a constructor: it reduces when its scrutinee is literally <code>none</code> or <code>some _</code>, and sits there otherwise. This is a different blocker from the one in M0 — no <code>Decidable</code> instance is involved — with the same symptom, and it is why the left unit law will be one <code>rfl</code> and the right unit law a case split.' },
        { m: '| some v => some v', h: 'Left wins. Where the left heap holds a value, the right heap is never consulted. Under a disjointness hypothesis that branch can only fire where the right heap answers <code>none</code>, so the bias is unobservable — but the definition does not know that, and neither does <code>rfl</code>.' },
        { m: '| none   => h₂ l', h: 'Otherwise defer, and defer to whatever is there, <code>none</code> included. Two heaps undefined at <code>l</code> have a union undefined at <code>l</code>.' }
      ],
      cap: 'At each location, the first of the two heaps that answers <code>some</code> supplies the value.' },

    { t: 'p', h: 'Now break commutativity. Put a cell at location <code>0</code> in each of two heaps, holding different values. Reading the union at <code>0</code> one way round gives <code>some 1</code>, the other way round <code>some 2</code>, and two heaps that disagree anywhere are unequal:' },

    { t: 'code', tag: 'illustration',
      cap: 'The refutation shape from the overview, with <code>some</code>’s injectivity doing the last step instead of two distinct constructors.',
      src: `example :
    Heap.union (Heap.singleton 0 1) (Heap.singleton 0 2)
      ≠ Heap.union (Heap.singleton 0 2) (Heap.singleton 0 1) := by
  intro heq
  have h0 := congrFun heq 0
  simp [Heap.union, Heap.singleton] at h0` },

    { t: 'p', h: 'Look at what that used. One shared location was enough. The values had to differ, but the two heaps did not have to be singletons and nothing else about them mattered. (The simp bracket names <code>Heap.union</code> because at this point there is nothing else to name; the lemmas that make the definition opaque again arrive in the second half.)' },

    { t: 'p', h: 'So the hypothesis has to forbid a location being claimed by both sides. Written pointwise, that is: at every location, at least one of the two heaps answers <code>none</code>.' },

    { t: 'anat',
      src: `def Heap.disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ l, h₁ l = none ∨ h₂ l = none`,
      parts: [
        { m: ': Prop', h: 'A <code>def</code>, not a <code>theorem</code>. It proves nothing; it <i>names a proposition</i>, and that name is <b>definitionally equal</b> to its body. That single fact drives every proof in this chapter.' },
        { m: '∀ l,', h: 'Because the body is a <code>∀</code> and the name unfolds definitionally, a goal displayed as <code>Heap.disjoint h₁ h₂</code> yields to <code>intro l</code> with no <code>unfold</code> in front of it. In the other direction a hypothesis <code>hd : Heap.disjoint h₁ h₂</code> <i>is</i> a function, so <code>hd l</code> is already a proof of the disjunction at <code>l</code>. That is how disjointness gets used: one location at a time.' },
        { m: 'h₁ l = none ∨ h₂ l = none', h: 'Note what is not forbidden: both may be <code>none</code>. Disjointness says the domains do not meet, not that together they cover anything. Note also that the body is symmetric in the two heaps — which is why exercise 1 is two lines, while <code>union</code>, whose body is not symmetric, needs exercise 6.' }
      ] },

    { t: 'p', h: 'Goal displays below print <code>Heap.disjoint h₁ h₂</code> as <code>h₁.disjoint h₂</code> and <code>Heap.union h₁ h₂</code> as <code>h₁.union h₂</code>. Same terms; you may type either form.' },

    { t: 'detail', title: 'The hypothesis that is actually weakest', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'Disjointness is stronger than commutativity needs. What the counterexample above required was two <i>different</i> values at a shared location. Heaps that overlap but agree wherever they overlap have equal unions both ways round: at a shared <code>l</code> both sides answer the one value that is there. So the weakest hypothesis making <code>union</code> commutative is compatibility — agreement on the intersection of the domains — and disjointness is a deliberate over-strengthening.' },
        { t: 'p', h: 'The over-strengthening is the subject. Separation logic is not trying to make an operation well defined; it is trying to say who owns what. Under compatibility a cell may sit in both halves of a split, so a write through one half changes the other, and the frame rule stops being sound at exactly the command it exists for. Under disjointness every allocated cell is in one half, and every substructural consequence in the course follows from that.' },
        { t: 'p', h: 'Compatibility is not thrown away for ever — it is what fractional and read-only permissions recover, by making the resource something finer than a cell so that two halves can hold different fractions of it. That is a different monoid, not a different logic, which is the point of the key callout below.' }
      ] },

    { t: 'detail', title: 'What it costs to put the proof in the type', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'The dependent alternative is a legal definition. The problem is not that Lean rejects it, it is what the <i>statements</i> then look like.' },
        { t: 'code', tag: 'illustration',
          src: `def unionD (h₁ h₂ : Heap) (_ : Heap.disjoint h₁ h₂) : Heap :=
  Heap.union h₁ h₂

theorem unionD_assoc (h₁ h₂ h₃ : Heap)
    (d₁₂ : Heap.disjoint h₁ h₂)
    (d₁₂₃ : Heap.disjoint (unionD h₁ h₂ d₁₂) h₃)
    (d₂₃ : Heap.disjoint h₂ h₃)
    (d₁₂₃' : Heap.disjoint h₁ (unionD h₂ h₃ d₂₃)) :
    unionD (unionD h₁ h₂ d₁₂) h₃ d₁₂₃ = unionD h₁ (unionD h₂ h₃ d₂₃) d₁₂₃' :=
  union_assoc h₁ h₂ h₃` },
        { t: 'p', h: 'Four disjointness arguments merely to <i>state</i> associativity, two of them mentioning the operation being defined. The proof stays one line, because <code>unionD a b _</code> is definitionally <code>Heap.union a b</code> — but every later lemma has to be threaded through this, and every rewrite has to produce the right proof term in the right position. Compare the statement you will actually prove in exercise 5: <code>union_assoc (h₁ h₂ h₃ : Heap)</code>, no hypotheses at all.' }
      ] },

    /* ================================================================
       2 — nine laws
       ================================================================ */

    { t: 'h3', s: 'Nine laws' },

    { t: 'p', h: 'A partial commutative monoid: an operation, a compatibility relation saying where it is meant to be used, associativity and commutativity where compatible, and a unit compatible with everything. Here the operation is <code>Heap.union</code>, the unit is <code>Heap.empty</code>, and compatibility is <code>Heap.disjoint</code>. The remaining nine exercises are the axioms.' },

    { t: 'tbl',
      head: ['PCM law', 'here', 'Lean name', 'needs <code>disjoint</code>?'],
      rows: [
        ['<code>e · a = a</code>', '<code>∅ ∪ h = h</code>', '<code>union_empty_left</code>', 'no'],
        ['<code>a · e = a</code>', '<code>h ∪ ∅ = h</code>', '<code>union_empty_right</code>', 'no'],
        ['<code>(a·b)·c = a·(b·c)</code>', '<code>(h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃)</code>', '<code>union_assoc</code>', 'no, unconditionally'],
        ['<code>a · b = b · a</code>', '<code>h₁ ∪ h₂ = h₂ ∪ h₁</code>', '<code>union_comm</code>', 'yes, and false without it'],
        ['<code>a # b ⟹ b # a</code>', 'compatibility is symmetric', '<code>disjoint_symm</code>', '—'],
        ['<code>e # a</code>', 'the unit is compatible with everything', '<code>disjoint_empty_left</code> / <code>_right</code>', '—'],
        ['<code>(a·b) # c ⟺ a # c ∧ b # c</code>', 'compatibility distributes over the operation', '<code>disjoint_union_left</code> / <code>_right</code>', '—'],
        ['<code>l₁ ≠ l₂ ⟹ (l₁ ↦ v₁) # (l₂ ↦ v₂)</code>', 'and conversely', '<code>singleton_disjoint</code> / <code>_iff</code>', '—'],
        ['splitting', 'the three-place relation the whole thing is for', '<code>splits_comm</code> / <code>splits_assoc</code>', '—']
      ],
      cap: 'One law needs the hypothesis. It is not the one people expect.' },

    { t: 'note', kind: 'key', title: 'The one thing to remember',
      h: 'Separating conjunction is not “a connective about heaps”. It is <b>the connective induced by any partial commutative monoid</b>. Replace heaps by file handles, permissions, tokens, ghost state, fractional ownership — every law proved in M4 still holds verbatim, because M4’s proofs use nothing about heaps except the nine facts above. That is how one framework (Iris) talks about all of them at once.' },

    /* ================================================================
       3 — disjointness
       ================================================================ */

    { t: 'sec', s: 'Exercises · disjointness' },

    { t: 'ex',
      id: 'm2-1',
      name: 'disjoint_symm',
      hard: false,
      why: 'Two lines, and the first place a <code>def</code> returning <code>Prop</code> is unfolded without being asked — the move every later proof in this chapter rests on. It is also the lemma that makes <code>disjoint_union_right</code> free rather than a second copy of <code>disjoint_union_left</code>.',
      goal: `theorem disjoint_symm {h₁ h₂ : Heap} :
    Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁`,
      hints: [
        'The conclusion is, once unfolded, a <code>∀</code>. So there are two things to introduce, not one, and you may introduce both without touching the definition.',
        'After <code>intro hd l</code> you hold <code>hd : Heap.disjoint h₁ h₂</code> and <code>l : Loc</code>. What is <code>hd l</code>?',
        'It is a proof of <code>h₁ l = none ∨ h₂ l = none</code>, and the goal at <code>l</code> is that disjunction with the sides swapped. Flipping a disjunction is <code>Or.symm</code>; dot notation writes it <code>(hd l).symm</code>, and the parentheses matter.'
      ],
      hint: '<code>Or.symm</code> applied pointwise. Two lines.',
      sol: `theorem disjoint_symm {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by
  intro hd l
  exact (hd l).symm`,
      expl: '<code>hd l : h₁ l = none ∨ h₂ l = none</code>, and <code>Or.symm</code> flips it. The whole proof is that the body of the definition is a symmetric disjunction.',
      walk: [
        { tac: 'intro hd l', h: 'Two introductions in one tactic. <code>hd</code> is the antecedent of the arrow; <code>l</code> is the bound location, legal because the remaining goal <code>Heap.disjoint h₂ h₁</code> <i>is</i> <code>∀ l, h₂ l = none ∨ h₁ l = none</code>. Watch the display change from the folded name to the disjunction at exactly this step.' },
        { tac: 'exact (hd l).symm', h: '<code>hd l</code> instantiates the hypothesis at the location now in scope. <code>.symm</code> resolves to <code>Or.symm</code> — dot notation looks up the head symbol of the <i>type</i>, which here is <code>Or</code> — and swaps the disjuncts, which is the goal.' }
      ],
      deep: [
        { t: 'trace', title: 'disjoint_symm, tactic by tactic',
          start: `h₁ h₂ : Heap
⊢ h₁.disjoint h₂ → h₂.disjoint h₁`,
          steps: [
            { tac: 'intro hd l',
              state: `h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
⊢ h₂ l = none ∨ h₁ l = none`,
              h: 'This is the step worth staring at. Nothing was rewritten. <code>intro</code> puts the goal into weak head normal form before looking for a binder, which unfolds the <code>def</code>, finds the <code>∀</code>, and introduces it. The hypothesis <code>hd</code> stays folded, because nothing forced it to unfold.' },
            { tac: 'exact (hd l).symm',
              h: '<code>@Or.symm : ∀ {a b : Prop}, a ∨ b → b ∨ a</code>, applied to <code>hd l</code>, is exactly the goal.' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'Why <code>(hd l).symm</code> and not <code>hd.symm l</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Dot notation is resolved from the head constant of the <i>type</i> of the thing before the dot. The type of <code>hd</code> is <code>∀ (l : Loc), h₁ l = none ∨ h₂ l = none</code>, whose head is the function arrow, so <code>hd.symm</code> goes looking for <code>Function.symm</code>:' },
            { t: 'state',
              src: `error(lean.invalidField): Invalid field \`symm\`: The environment does not contain \`Function.symm\`, so it is not possible to project the field \`symm\` from an expression
  hd
of type
  ∀ (l : Loc), h₁ l = none ∨ h₂ l = none` },
            { t: 'p', h: 'Apply first, project second. <code>hd l</code> has head constant <code>Or</code>, so <code>.symm</code> finds <code>Or.symm</code>. The parentheses are load-bearing: <code>hd l.symm</code> parses as <code>hd (l.symm)</code>.' }
          ] }
      ],
      pitfall: 'Flipping the disjunction before introducing the location. <code>apply Or.symm</code> on the goal <code>Heap.disjoint h₂ h₁</code> fails, because at that point the goal is a <code>∀</code> and not an <code>∨</code>. Equally common is <code>exact hd l</code>, which is the disjunction with the sides in the wrong order — and the error then compares two disjunctions that differ only in which heap is named first.',
      variants: 'The statement may as well be an <code>↔</code>: <code>⟨disjoint_symm, disjoint_symm⟩</code> proves <code>Heap.disjoint h₁ h₂ ↔ Heap.disjoint h₂ h₁</code>, a symmetric relation being its own converse.<br><br>Three different <code>.symm</code>s turn up in this chapter and they are three different lemmas: <code>Or.symm</code> here, <code>Eq.symm</code> in exercise 8 to turn a unit law round, and <code>Ne.symm</code> whenever a disequality is oriented against the <code>if</code> in <code>Heap.singleton</code>. The dot picks by the head constant of the type, so you never write the namespace and you also never get to choose.'
    },

    { t: 'ex',
      id: 'm2-2',
      name: 'disjoint_empty_left / right',
      hard: false,
      why: 'The unit of a PCM has to be compatible with everything, and this is that axiom. You need it whenever you manufacture a splitting one of whose halves owns nothing: <code>splits_empty_left</code> below, then M4’s <code>star_emp_left_intro</code> and <code>star_pure_right</code>, M7’s <code>hoare_load</code>, M10’s linked list. It is also the cleanest place in the course to write a proof as a term and see nothing lost.',
      goal: `theorem disjoint_empty_left  (h : Heap) : Heap.disjoint Heap.empty h
theorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty`,
      hints: [
        'There is nothing to case on. The empty heap is undefined at every location, so the same disjunct works everywhere and the proof is a constant function <code>fun _ =&gt; …</code>.',
        '<code>@Or.inl : ∀ {a b : Prop}, a → a ∨ b</code> builds the left disjunct and <code>Or.inr</code> the right. Which you need depends on which argument of <code>Heap.disjoint</code> the empty heap occupies.',
        'What proves <code>Heap.empty l = none</code>? <code>Heap.empty</code> is <code>fun _ =&gt; none</code>, so <code>Heap.empty l</code> reduces to <code>none</code> and both sides are literally the same term.',
        'Left: <code>fun _ =&gt; Or.inl rfl</code>. Right: the same with <code>Or.inr</code>.'
      ],
      hint: 'Give the term directly: <code>fun _ => Or.inl rfl</code>.',
      sol: `theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=
  fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=
  fun _ => Or.inr rfl`,
      expl: '<code>Heap.empty l</code> <i>is</i> <code>none</code>, so <code>rfl</code> proves the disjunct and the proof of the <code>∀</code> is the constant function returning it.',
      walk: [
        { tac: 'fun _ =>', h: 'The statement <code>Heap.disjoint Heap.empty h</code> unfolds to <code>∀ l, Heap.empty l = none ∨ h l = none</code>, and a proof of a <code>∀</code> is a function. The binder is <code>_</code> because the body never mentions the location — the same disjunct is right everywhere.' },
        { tac: 'Or.inl rfl', h: 'The left disjunct is the provable one, so inject on the left. Lean infers <code>Or.inl</code>’s implicit right-hand proposition from the goal.' },
        { tac: 'rfl', h: 'Asked to have type <code>Heap.empty l = none</code>. Lean unfolds <code>Heap.empty</code> to <code>fun _ =&gt; none</code>, beta-reduces, and gets <code>none = none</code>. Definitional equality does that silently; there is no rewriting step to watch.' },
        { tac: 'fun _ => Or.inr rfl', h: 'The mirror image. In <code>disjoint_empty_right</code> the empty heap is the second argument, so the provable disjunct is the right one. Same <code>rfl</code>, other injection.' }
      ],
      deep: [
        { t: 'trace', title: 'The same proof driven by tactics, so the goals are visible',
          start: `h : Heap
⊢ Heap.empty.disjoint h`,
          steps: [
            { tac: 'intro l',
              state: `h : Heap
l : Loc
⊢ Heap.empty l = none ∨ h l = none`,
              h: 'The <code>∀</code> inside the definition, introduced — the tactic counterpart of writing <code>fun _ =&gt;</code>.' },
            { tac: 'left',
              state: `h : Heap
l : Loc
⊢ Heap.empty l = none`,
              h: '<code>left</code> commits to the first disjunct of an <code>∨</code> goal and discards the second; <code>right</code> does the other. It is the tactic counterpart of <code>Or.inl</code>, and there is no going back — choose wrong and you undo.' },
            { tac: 'rfl', h: 'Closed by unfolding <code>Heap.empty</code>.' }
          ],
          done: 'No goals.' },
        { t: 'cmp',
          left: { t: 'Term proof', kind: 'good',
            h: 'One line, no goal states, and it reads as the mathematics: constantly, choose the left disjunct, which holds by computation.',
            src: 'fun _ => Or.inl rfl', tag: 'verified' },
          right: { t: 'Tactic proof',
            h: 'Three tactics, or one <code>simp</code>. Both work. The term is preferred here because it is shorter than the goal state a tactic proof would print.',
            src: `theorem disjoint_empty_left' (h : Heap) : Heap.disjoint Heap.empty h := by
  simp [Heap.disjoint, Heap.empty]`, tag: 'illustration' } }
      ],
      pitfall: 'Picking the wrong injection. <code>disjoint_empty_right</code> with <code>Or.inl rfl</code> asks Lean to prove <code>h l = none</code> for an arbitrary <code>h</code>, which is false — and the complaint arrives at <code>rfl</code> rather than at <code>Or.inl</code>, pointing at the innocent half of the term. Read the statement, find which side the empty heap is on, take the matching injection.',
      variants: 'Ask instead when a heap is disjoint from <i>itself</i>. The disjunction becomes <code>h l = none ∨ h l = none</code>, both sides the same statement, so the same tactic finishes both branches:<br><br><code>theorem self_disjoint_empty {h : Heap} (hd : Heap.disjoint h h) : h = Heap.empty := by funext l; rcases hd l with hl | hl &lt;;&gt; exact hl</code><br><br>No rewriting is needed to match the goal, because <code>Heap.empty l</code> is <code>none</code> definitionally. So <code>Heap.empty</code> is not merely <i>a</i> self-disjoint heap, it is the only one — the strongest thing this chapter proves, and the shortest.'
    },

    { t: 'ex',
      id: 'm2-3',
      name: 'singleton_disjoint (and its converse)',
      hard: false,
      why: 'The ⟸ direction is routine. The ⟹ direction is the first appearance of <b>separation implying non-aliasing</b>: owning two cells separately <i>proves</i> that they are different cells. Small lemma, large moral — it is where every disequality in every later program proof comes from, with no side condition written anywhere.',
      goal: `theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂)

theorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :
    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂`,
      hints: [
        'For the easy direction, fix a location <code>x</code> and ask whether <code>x = l₁</code>. In each case one of the two singletons is provably undefined at <code>x</code>; say which, then commit to that disjunct.',
        'In the branch <code>hx : x = l₁</code> you owe <code>Heap.singleton l₂ v₂ x = none</code>, which is <code>singleton_other l₂ x v₂</code> applied to a proof of <code>x ≠ l₂</code>. You do not have one — derive it. Rewriting <code>x</code> to <code>l₁</code> turns the goal <code>x ≠ l₂</code> into <code>hne</code>.',
        'For the <code>↔</code>: <code>constructor</code> splits it into <code>mp</code> and <code>mpr</code>, and <code>mpr</code> is the theorem you just proved. In <code>mp</code> the conclusion <code>l₁ ≠ l₂</code> unfolds to <code>l₁ = l₂ → False</code>, so <code>intro hd heq</code> takes both hypotheses and leaves <code>False</code>.',
        'With <code>heq : l₁ = l₂</code>, <code>subst heq</code> puts both singletons at the same location. Then <code>hd l₁</code> says one of them is <code>none</code> there while <code>singleton_same</code> says both are <code>some _</code>. Both branches die the same way, so one block handles them together.'
      ],
      hint: 'For ⟸: split on <code>x = l₁</code>. For ⟹: assume <code>l₁ = l₂</code>, substitute, and instantiate the disjointness at <code>l₁</code>; both disjuncts contradict <code>singleton_same</code>.',
      sol: `theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) := by
  intro x
  by_cases hx : x = l₁
  · right
    have : x ≠ l₂ := by rw [hx]; exact hne
    exact singleton_other l₂ x v₂ this
  · left
    exact singleton_other l₁ x v₁ hx

theorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :
    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂ := by
  constructor
  · intro hd heq
    subst heq
    rcases hd l₁ with h | h <;>
      · rw [singleton_same] at h; exact absurd h (by simp)
  · exact singleton_disjoint v₁ v₂`,
      expl: 'Forwards, <code>subst heq</code> puts both singletons at one location, so <code>hd l₁</code> claims one of them is <code>none</code> there — and <code>singleton_same</code> says both are <code>some _</code>. The <code>&lt;;&gt; ·</code> block runs the same three-step contradiction on both disjuncts.',
      walk: [
        { tac: 'intro x', h: 'Unfolds the definition and fixes the location, leaving the disjunction at <code>x</code>.' },
        { tac: 'by_cases hx : x = l₁', h: 'Two goals differing only in <code>hx</code>. The split is on a location equality because that is what <code>Heap.singleton</code>’s body tests; the union proofs later split on something else entirely.' },
        { tac: '· right', h: 'In the <code>pos</code> branch <code>x</code> is <code>l₁</code>, so the left singleton <i>is</i> defined there and only the right disjunct is provable. <code>right</code> commits to it, discarding a false alternative.' },
        { tac: 'have : x ≠ l₂ := by rw [hx]; exact hne', h: 'An anonymous <code>have</code>: no name given, so the fact enters as <code>this</code>. Inside, the goal <code>x ≠ l₂</code> is the application <code>Ne x l₂</code> with <code>x</code> an ordinary argument, so <code>rw [hx]</code> turns it into <code>l₁ ≠ l₂</code>, which is <code>hne</code>. This line is where non-aliasing enters the proof.' },
        { tac: 'exact singleton_other l₂ x v₂ this', h: 'Argument order: the location the singleton lives at first, the probed location second. Here the singleton is at <code>l₂</code> and we are probing <code>x</code>.' },
        { tac: '· left', h: 'The <code>neg</code> branch. Now <code>x ≠ l₁</code>, the left singleton is undefined at <code>x</code>, and the left disjunct is the provable one. <code>hne</code> is never used here — non-aliasing only matters where the cells could collide.' },
        { tac: 'exact singleton_other l₁ x v₁ hx', h: '<code>hx : ¬x = l₁</code> is accepted where <code>x ≠ l</code> is wanted, with no conversion step: <code>Ne</code> is a <i>reducible</i> definition, so <code>exact</code> unfolds it unasked. What the printer shows is no guide to which of the two forms the term actually contains.' },
        { tac: 'constructor', h: 'Second theorem. On an <code>↔</code> goal, <code>constructor</code> applies <code>Iff.intro</code> and leaves two goals, <code>mp</code> and <code>mpr</code>. In the other direction, the two halves of an <code>h : A ↔ B</code> are reached as <code>h.mp : A → B</code> and <code>h.mpr : B → A</code>; you will use those constantly from exercise 5 on.' },
        { tac: '· intro hd heq', h: 'Two introductions where the statement shows one arrow, because <code>l₁ ≠ l₂</code> <i>is</i> <code>l₁ = l₂ → False</code>. The goal <code>False</code> is the giveaway that this is now a refutation.' },
        { tac: 'subst heq', h: '<code>l₂</code> is a local variable, so it is eliminated rather than rewritten. Watch it leave the context in the trace, and watch <code>hd</code> become a claim about two singletons at the <i>same</i> location.' },
        { tac: 'rcases hd l₁ with h | h <;>', h: '<code>rcases</code> takes a hypothesis apart; the bar separates one pattern per constructor of <code>Or</code>, so this instantiates disjointness at the shared location and splits the result. Two goals, <code>inl</code> and <code>inr</code>, and the same name <code>h</code> stands for a different fact in each. The trailing <code>&lt;;&gt;</code> then runs what follows on both.' },
        { tac: '· rw [singleton_same] at h; exact absurd h (by simp)', h: 'The focus dot here is not selecting a goal, it is <i>grouping</i>: <code>&lt;;&gt;</code> takes a single tactic on its right, so a two-tactic block has to be wrapped. Inside, the rewrite turns <code>h</code> into <code>some v₁ = none</code> (respectively <code>some v₂ = none</code>), and <code>absurd</code> converts that into the goal. Its refutation comes from a nested <code>by simp</code> — a tactic block used as a term, where the expected type tells simp what to prove.' },
        { tac: '· exact singleton_disjoint v₁ v₂', h: 'The <code>mpr</code> half. Its hypothesis <code>l₁ ≠ l₂</code> is not yet introduced, but <code>singleton_disjoint v₁ v₂</code> is a function expecting exactly that, so it <i>is</i> the proof. The implicit locations come from unification with the goal.' }
      ],
      deep: [
        { t: 'trace', title: 'singleton_disjoint — both branches',
          start: `l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)`,
          steps: [
            { tac: 'intro x',
              state: `l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
⊢ Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none`,
              h: 'Definition unfolded, location fixed.' },
            { tac: 'by_cases hx : x = l₁',
              state: `case pos
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx : x = l₁
⊢ Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none`,
              h: 'First of the two goals, with <code>neg</code> waiting behind it.' },
            { tac: 'right',
              state: `case pos
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx : x = l₁
⊢ Heap.singleton l₂ v₂ x = none`,
              h: 'The disjunction is gone and the choice is irrevocable.' },
            { tac: 'have : x ≠ l₂ := by rw [hx]; exact hne',
              state: `case pos
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx : x = l₁
this : x ≠ l₂
⊢ Heap.singleton l₂ v₂ x = none`,
              h: 'The goal is untouched; only the context grew, by exactly the disequality <code>singleton_other</code> demands.' },
            { tac: '(the second bullet)',
              state: `case neg
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx : ¬x = l₁
⊢ Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none`,
              h: 'And <code>left</code> then <code>singleton_other l₁ x v₁ hx</code> finishes it.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'singleton_disjoint_iff — the forward direction',
          start: `l₁ l₂ : Loc
v₁ v₂ : Val
⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂`,
          steps: [
            { tac: 'constructor',
              state: `case mp
l₁ l₂ : Loc
v₁ v₂ : Val
⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂) → l₁ ≠ l₂`,
              h: 'Two goals, <code>mp</code> and <code>mpr</code>. This is the first.' },
            { tac: 'intro hd heq',
              state: `case mp
l₁ l₂ : Loc
v₁ v₂ : Val
hd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)
heq : l₁ = l₂
⊢ False`,
              h: 'Both hypotheses in, and the goal is <code>False</code>.' },
            { tac: 'subst heq',
              state: `case mp
l₁ : Loc
v₁ v₂ : Val
hd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)
⊢ False`,
              h: '<code>l₂</code> has left the context entirely, and <code>hd</code> now asserts that two singletons at one location are disjoint. Everything after this is squeezing that dry.' },
            { tac: 'rcases hd l₁ with h | h',
              state: `case mp.inl
l₁ : Loc
v₁ v₂ : Val
hd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)
h : Heap.singleton l₁ v₁ l₁ = none
⊢ False`,
              h: 'The case name <code>mp.inl</code> records the whole path: forward direction, left injection.' },
            { tac: 'rw [singleton_same] at h',
              state: `case mp.inl
l₁ : Loc
v₁ v₂ : Val
hd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)
h : some v₁ = none
⊢ False`,
              h: 'Visibly absurd. <code>exact absurd h (by simp)</code> closes it.' },
            { tac: '(the same block, on the other disjunct)',
              state: `case mp.inr
l₁ : Loc
v₁ v₂ : Val
hd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)
h : Heap.singleton l₁ v₂ l₁ = none
⊢ False`,
              h: 'Identical in shape with <code>v₂</code> for <code>v₁</code>. That the two goals have the same shape is the whole licence for <code>&lt;;&gt;</code> instead of two bullets.' },
            { tac: '(the mpr goal)',
              state: `case mpr
l₁ l₂ : Loc
v₁ v₂ : Val
⊢ l₁ ≠ l₂ → (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)`,
              h: 'Which is literally the type of <code>singleton_disjoint v₁ v₂</code>.' }
          ],
          done: 'No goals.' },
        { t: 'steps', title: 'The moral',
          items: [
            { k: 'Disjointness is a claim you cash in', h: '<code>Heap.disjoint (singleton l₁ v₁) (singleton l₂ v₂)</code> is not the observation that these two happen not to overlap. It is a hypothesis you are handed, and the <code>mp</code> direction converts it into <code>l₁ ≠ l₂</code>.' },
            { k: 'Which is where aliasing information comes from', h: 'In M4 the assertion <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂)</code> unfolds to a splitting of the heap into two singletons, and this lemma turns that into <code>l₁ ≠ l₂</code> for free. The theorem is called <code>two_cells_distinct</code> and after the destructuring its proof is <code>exact (singleton_disjoint_iff v₁ v₂).mp hd</code>. M10 instantiates it to get <code>p ≠ p + 1</code> for a list node. In a Hoare logic without <code>∗</code>, that disequality has to be written into every precondition by hand, and forgotten exactly once per program.' }
          ] }
      ],
      pitfall: 'Argument order in <code>singleton_other (l x : Loc) (v : Val) (hne : x ≠ l)</code>: the heap’s own location first, the probed location second, so <code>singleton_other l₂ x v₂</code> and not <code>singleton_other x l₂ v₂</code>. Since <code>Loc</code> is <code>Nat</code> both orders typecheck until the last argument, and the error surfaces at the disequality, pointing at <code>this</code>. Related: the disequality must read <code>x ≠ l₂</code> to match the <code>if x = l</code> in <code>Heap.singleton</code>; the other orientation needs <code>Ne.symm</code>.',
      variants: 'Drop <code>hne</code> and the theorem fails at exactly the expected place — two singletons at one location are never disjoint:<br><br><code>example : ¬ Heap.disjoint (Heap.singleton 0 1) (Heap.singleton 0 2) := by intro hd; rcases hd 0 with h | h &lt;;&gt; · rw [singleton_same] at h; exact absurd h (by simp)</code><br><br>The values play no part. <code>Heap.singleton 0 1</code> is not disjoint from <code>Heap.singleton 0 1</code> either: disjointness is about domains, and agreeing values do not rescue it.'
    },

    /* ================================================================
       4 — the interface to union
       ================================================================ */

    { t: 'sec', s: 'Exercises · union laws' },

    { t: 'p', h: 'Nothing above needed to look inside <code>Heap.union</code>. Everything below does, and doing it by unfolding leaves a <code>match</code> in every goal. So three lookup lemmas first — not in the original syllabus, and the rest of the course is unreadable without them.' },

    { t: 'code',
      src: `theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :
    Heap.union h₁ h₂ l = h₂ l := by
  simp [Heap.union, hl]

theorem union_of_some {h₁ : Heap} (h₂ : Heap) {l : Loc} {v : Val} (hl : h₁ l = some v) :
    Heap.union h₁ h₂ l = some v := by
  simp [Heap.union, hl]

theorem union_eq_none {h₁ h₂ : Heap} {l : Loc} :
    Heap.union h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by
  constructor
  · intro h
    cases hl : h₁ l with
    | none   => exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩
    | some v => rw [union_of_some h₂ hl] at h; exact absurd h (by simp)
  · intro ⟨ha, hb⟩
    rw [union_of_none h₂ ha]; exact hb` },

    { t: 'p', h: 'These three are to <code>union</code> what <code>write_same</code> and <code>write_other</code> are to <code>write</code>. They are the last place in the course where <code>Heap.union</code> appears in a simp bracket, which is exactly the licence M1 established: a definition may be unfolded while its interface is being built, and not after.' },

    { t: 'anat',
      src: `theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :
    Heap.union h₁ h₂ l = h₂ l := by
  simp [Heap.union, hl]`,
      parts: [
        { m: '{h₁ : Heap} (h₂ : Heap) {l : Loc}', h: '<code>h₁</code> and <code>l</code> can be read off the type of <code>hl</code>, so they are implicit; <code>h₂</code> cannot, since <code>hl</code> says nothing about it, so it is explicit. That is why every call site below reads <code>union_of_none h₂ hl</code> — one visible heap, then the equation. It looks arbitrary until you see it is forced.' },
        { m: 'simp [Heap.union, hl]', h: 'Two entries, two jobs. Unfolding exposes the <code>match</code>; <code>hl : h₁ l = none</code> then rewrites its scrutinee to the constructor <code>none</code>, which is the only thing that lets the match take a branch.' }
      ],
      cap: 'Unfold, rewrite the scrutinee to a constructor, let the match compute. Every proof in this section is that pattern.' },

    { t: 'p', h: 'Unfolding alone leaves the goal parked:' },

    { t: 'state',
      src: `h₁ h₂ : Heap
l : Loc
hl : h₁ l = none
⊢ (match h₁ l with
    | some v => some v
    | none => h₂ l) =
    h₂ l`,
      cap: 'After <code>simp only [Heap.union]</code>. The match cannot fire, because <code>h₁ l</code> is an opaque application and not a constructor. Handing over <code>hl</code> is what unsticks it.' },

    { t: 'p', h: 'Which changes what a case split is <i>for</i>. Every split in M0 and M1 asked whether two locations were equal, because every definition tested <code>if x = l</code> — and exercise 3 above split that way for the same reason. From here on the question is what a heap answers at one fixed location, and that is not a proposition to decide but a value with two constructors. So <code>cases hl : h₁ l with</code> displaces <code>by_cases</code>, and the saved equation is not a convenience: the occurrence you need to rewrite is buried inside <code>Heap.union</code>, where <code>cases</code> cannot see it, and <code>hl</code> is the only handle on it.' },

    { t: 'detail', title: '<code>union_eq_none</code>, walked through', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'The only one of the three with a real proof, and the source of the <code>.mp</code> and <code>.mpr</code> you will be using in the next four exercises.' },
        { t: 'trace', title: 'union_eq_none',
          steps: [
            { tac: 'constructor · intro h',
              state: `case mp
h₁ h₂ : Heap
l : Loc
h : h₁.union h₂ l = none
⊢ h₁ l = none ∧ h₂ l = none`,
              h: 'The union is undefined at <code>l</code>; conclude both halves are.' },
            { tac: 'cases hl : h₁ l with | none => …',
              state: `case mp.none
h₁ h₂ : Heap
l : Loc
h : h₁.union h₂ l = none
hl : h₁ l = none
⊢ none = none ∧ h₂ l = none`,
              h: 'Look at what happened to the <i>goal</i>: the exposed <code>h₁ l</code> became the constructor <code>none</code>, which is why the first conjunct is now <code>rfl</code>. The copy inside <code>h</code> was out of reach, and <code>hl</code> is what reaches it.' },
            { tac: 'exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩',
              h: '<code>rfl</code> for the first conjunct; for the second, <code>rwa</code> — rewrite <code>h</code> with <code>union_of_none h₂ hl</code>, turning it into <code>h₂ l = none</code>, then close the goal with it. The trailing <code>a</code> is <i>assumption</i>: <code>rwa [e] at h</code> is <code>rw [e] at h</code> followed by <code>exact h</code>.' },
            { tac: '| some v => …',
              state: `case mp.some
h₁ h₂ : Heap
l : Loc
h : h₁.union h₂ l = none
v : Val
hl : h₁ l = some v
⊢ some v = none ∧ h₂ l = none`,
              h: 'The impossible branch. The goal is absurd too, but the hypothesis is easier to refute.' },
            { tac: 'rw [union_of_some h₂ hl] at h',
              state: `case mp.some
h₁ h₂ : Heap
l : Loc
v : Val
h : some v = none
hl : h₁ l = some v
⊢ some v = none ∧ h₂ l = none`,
              h: 'And <code>exact absurd h (by simp)</code> produces the goal out of the wreckage.' },
            { tac: '· intro ⟨ha, hb⟩',
              state: `case mpr
h₁ h₂ : Heap
l : Loc
ha : h₁ l = none
hb : h₂ l = none
⊢ h₁.union h₂ l = none`,
              h: 'Backwards. <code>intro</code> with a pattern destructures the conjunction on arrival, so it never appears in the context at all.' },
            { tac: 'rw [union_of_none h₂ ha]',
              state: `case mpr
h₁ h₂ : Heap
l : Loc
ha : h₁ l = none
hb : h₂ l = none
⊢ h₂ l = none`,
              h: 'Which is <code>hb</code>.' }
          ],
          done: 'No goals.' }
      ] },

    { t: 'ex',
      id: 'm2-4',
      name: 'union_empty_left / right',
      hard: false,
      why: 'The two unit laws, and the sharpest demonstration in the chapter of what a <code>match</code> will and will not do. One is a single <code>rfl</code>; its mirror image needs a case split. Nothing mathematical distinguishes them.',
      goal: `theorem union_empty_left  (h : Heap) : Heap.union Heap.empty h = h
theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h`,
      hints: [
        'Both statements equate two heaps, so both proofs open with <code>funext l</code>. After that you are comparing two <code>Option Val</code>s.',
        'For the left law, ask whether the <code>match</code> can compute. Its scrutinee is <code>Heap.empty l</code>, which unfolds to the constructor <code>none</code> — so it can, and the two sides become one term.',
        'For the right law the scrutinee is <code>h l</code> with <code>h</code> a variable. Nothing reduces. You have to <i>make</i> it a constructor: <code>cases hl : h l with | none =&gt; … | some v =&gt; …</code>.',
        'In each branch the saved <code>hl</code> is exactly the hypothesis <code>union_of_none</code> / <code>union_of_some</code> wants. The <code>none</code> branch then leaves <code>Heap.empty l = none</code>, which is <code>rfl</code>.'
      ],
      hint: 'Left: <code>funext l; rfl</code>. Right: <code>funext l</code> then <code>cases hl : h l</code> and rewrite with <code>union_of_none</code> / <code>union_of_some</code>.',
      sol: `theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext l; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext l
  cases hl : h l with
  | none   => rw [union_of_none Heap.empty hl]; rfl
  | some v => rw [union_of_some Heap.empty hl]`,
      expl: 'A definition by pattern matching computes only when the scrutinee is a constructor. <code>Heap.empty l</code> reduces to <code>none</code> at once; <code>h l</code> does not reduce at all until you case on it. The whole asymmetry is that sentence.',
      walk: [
        { tac: 'funext l', h: 'First theorem, and the only tactic before <code>rfl</code>.' },
        { tac: 'rfl', h: 'Both sides are now the same term. Lean unfolds <code>Heap.union</code>, beta-reduces, unfolds <code>Heap.empty</code>, sees the scrutinee is <code>none</code>, takes the second branch, and lands on <code>h l</code> twice. All of it silent.' },
        { tac: 'funext l', h: 'Second theorem, same opening, entirely different sequel: the scrutinee is <code>h l</code>, and it is stuck.' },
        { tac: 'cases hl : h l with', h: 'Two branches, each carrying the equation the rewrite below consumes. Plain <code>cases (h l)</code> would give you the split and no equation, which here is no proof at all.' },
        { tac: '| none   => rw [union_of_none Heap.empty hl]; rfl', h: 'With <code>hl : h l = none</code>, the rewrite turns the left-hand side into <code>Heap.empty l</code>. <code>cases</code> has already put <code>none</code> on the right-hand side, so what remains is <code>Heap.empty l = none</code> — true by unfolding, and no rewriting could have reached it.' },
        { tac: '| some v => rw [union_of_some Heap.empty hl]', h: 'Here one rewrite makes both sides <code>some v</code>, and <code>rw</code>’s trailing <code>rfl</code> closes the goal. That is why this branch is one tactic and the other is two.' }
      ],
      deep: [
        { t: 'trace', title: 'Why one is rfl and the other is not',
          start: `h : Heap
⊢ Heap.empty.union h = h`,
          steps: [
            { tac: 'funext l',
              state: `h : Heap
l : Loc
⊢ Heap.empty.union h l = h l`,
              h: 'The left law. <code>rfl</code> closes this: the scrutinee unfolds to a constructor and the match computes.' },
            { tac: '(second theorem) funext l',
              state: `h : Heap
l : Loc
⊢ h.union Heap.empty l = h l`,
              h: 'The right law at the same point. It looks like the mirror image and it is not — here the scrutinee is <code>h l</code>.' },
            { tac: 'cases hl : h l with | none =>',
              state: `case none
h : Heap
l : Loc
hl : h l = none
⊢ h.union Heap.empty l = none`,
              h: '<code>h l</code> became <code>none</code> on the right-hand side. On the left it is buried inside <code>Heap.union</code>, untouched, and <code>hl</code> is the only way in.' },
            { tac: 'rw [union_of_none Heap.empty hl]',
              state: `case none
h : Heap
l : Loc
hl : h l = none
⊢ Heap.empty l = none`,
              h: 'Closed by <code>rfl</code>.' },
            { tac: '(the some branch)',
              state: `case some
h : Heap
l : Loc
v : Val
hl : h l = some v
⊢ h.union Heap.empty l = some v`,
              h: 'And <code>rw [union_of_some Heap.empty hl]</code> makes both sides <code>some v</code>.' }
          ],
          done: 'No goals.' },
        { t: 'cmp',
          left: { t: 'The tempting one-liner', kind: 'bad',
            h: 'It fails, and the message is precise about why. This is not a defect of <code>rfl</code>.',
            src: `example (h : Heap) : Heap.union h Heap.empty = h := by
  funext l
  rfl`, tag: 'sketch' },
          right: { t: 'What Lean says',
            h: 'Stuck on an application of a variable. No amount of unfolding turns <code>h l</code> into a constructor, so the case split is not avoidable.',
            src: `error: Tactic \`rfl\` failed: The left-hand side
  h.union Heap.empty l
is not definitionally equal to the right-hand side
  h l

h : Heap
l : Loc
⊢ h.union Heap.empty l = h l`, tag: 'sketch' } },
        { t: 'detail', title: 'The left law does not need <code>funext</code> either', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Push the point one step. The <code>funext l</code> in <code>union_empty_left</code> is doing no work: the equation between the two <i>heaps</i>, not merely their values at a location, is already definitional.' },
            { t: 'code', tag: 'illustration',
              src: 'theorem union_empty_left_rfl (h : Heap) : Heap.union Heap.empty h = h := rfl' },
            { t: 'p', h: 'Trace it: <code>Heap.union Heap.empty h</code> unfolds to <code>fun l =&gt; match Heap.empty l with | some v =&gt; some v | none =&gt; h l</code>; under the binder <code>Heap.empty l</code> reduces to <code>none</code>, the match takes its second branch, and what remains is <code>fun l =&gt; h l</code>. Not <i>syntactically</i> <code>h</code> — but Lean 4 has <b>eta for functions</b> as a definitional rule, so the kernel sees one term. The corpus writes <code>funext l; rfl</code> anyway, so that the two unit laws line up on the page.' },
            { t: 'p', h: 'This is not a curiosity. It is why the orientation slip in exercise 8 goes undetected: <code>Heap.union Heap.empty h = h</code> and <code>h = Heap.union Heap.empty h</code> are both definitionally <code>h = h</code>, so Lean accepts either proof for either goal. The right-handed version has no such escape hatch.' }
          ] }
      ],
      pitfall: 'Reaching for <code>simp [Heap.union]</code> when <code>rfl</code> fails. On the un-<code>funext</code>ed goal it reports <code>simp made no progress</code>; after <code>funext l</code> it hands back <code>⊢ (match h l with | some v =&gt; some v | none =&gt; Heap.empty l) = h l</code> — the match now written out in the goal and no nearer to reducing, because the scrutinee is still <code>h l</code>. The fix is always the same: case on the scrutinee, with the <code>hl :</code> prefix, and keep the equation.',
      variants: 'Had <code>union</code> matched on its <i>second</i> argument, the two proofs would swap: the right unit law would be <code>rfl</code> and the left one would need the split. Nothing mathematical changes; the asymmetry belongs entirely to which argument the definition inspects. Worth internalising, because it comes back in <code>union_assoc</code>, where the <code>some</code> branch is one line and the <code>none</code> branch needs a nested split.'
    },

    { t: 'ex',
      id: 'm2-5',
      name: 'union_assoc',
      hard: false,
      why: '<b>No hypothesis at all.</b> A biased, total union is associative on the nose, because “the first defined value wins” is an associative rule whether or not anything overlaps. This is the reason associativity of <code>∗</code> in M4 costs nothing beyond bookkeeping: the step that changes the bracketing generates no side condition to discharge.',
      goal: `theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃)`,
      hints: [
        'At a fixed location the value is “the first of <code>h₁ l</code>, <code>h₂ l</code>, <code>h₃ l</code> that is <code>some</code>”. Three regimes: <code>h₁</code> defined; <code>h₁</code> undefined and <code>h₂</code> defined; both undefined. Your proof will have three leaves.',
        '<code>funext l</code>, then <code>cases hl : h₁ l</code>. The <code>some</code> regime is the easy one — both sides become <code>some v</code> after two rewrites, one of which is <code>union_of_some h₃ (union_of_some h₂ hl)</code>, a lemma applied to a lemma.',
        'In the <code>none</code> regime the right-hand side collapses at once to <code>Heap.union h₂ h₃ l</code>. Now case on <code>h₂ l</code>.',
        'The obstacle in both inner branches is the same: rewriting the <i>outer</i> union on the left needs a fact about <code>Heap.union h₁ h₂ l</code>, and all you hold are facts about <code>h₁ l</code> and <code>h₂ l</code>. Manufacture it — <code>union_eq_none.mpr ⟨hl, hl2⟩</code> in one leaf, an explicit <code>have</code> in the other.'
      ],
      hint: '<code>funext l</code>, case on <code>h₁ l</code>, and inside the <code>none</code> branch case on <code>h₂ l</code>. Three leaves.',
      sol: `theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext l
  cases hl : h₁ l with
  | none =>
      rw [union_of_none (Heap.union h₂ h₃) hl]
      cases hl2 : h₂ l with
      | none =>
          rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]
      | some v =>
          have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2
          rw [union_of_some h₃ hu, union_of_some h₃ hl2]
  | some v =>
      rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]`,
      expl: 'Both bracketings compute “the first <code>some</code> in the list <code>[h₁ l, h₂ l, h₃ l]</code>”, and that function does not care how the list was bracketed. The proof walks the three cases and rewrites. The one move to notice is <code>union_eq_none.mpr ⟨hl, hl2⟩</code>: to rewrite the outer union you must first know the inner one is <code>none</code>, which is what the backward direction of <code>union_eq_none</code> manufactures.',
      walk: [
        { tac: 'funext l', h: 'Fix a location.' },
        { tac: 'cases hl : h₁ l with', h: 'The outermost question: does the leftmost heap answer here? <code>hl</code> is what every rewrite below consumes.' },
        { tac: '| none =>', h: 'First regime: <code>h₁</code> contributes nothing at <code>l</code>.' },
        { tac: 'rw [union_of_none (Heap.union h₂ h₃) hl]', h: 'Rewrites the <i>right-hand side</i>: <code>Heap.union h₁ (Heap.union h₂ h₃) l</code> becomes <code>Heap.union h₂ h₃ l</code>. The explicit argument is the whole heap <code>Heap.union h₂ h₃</code>, because that is what plays the lemma’s <code>h₂</code>. Getting this argument wrong is the commonest failure in the proof.' },
        { tac: 'cases hl2 : h₂ l with', h: 'The second question, asked only inside the first <code>none</code> branch.' },
        { tac: '| none =>', h: 'Neither <code>h₁</code> nor <code>h₂</code> answers at <code>l</code>, so both sides must be <code>h₃ l</code>.' },
        { tac: 'rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]', h: 'Two rewrites. The first attacks the left-hand side and needs <code>Heap.union h₁ h₂ l = none</code>, assembled on the spot from the pair of facts you hold. The second turns the right-hand side into <code>h₃ l</code>. Both sides now agree.' },
        { tac: '| some v =>', h: '<code>h₁</code> silent, <code>h₂</code> answering: <code>some v</code> on both sides.' },
        { tac: 'have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2', h: 'A named intermediate, because <code>union_eq_none</code> covers only the <code>none</code> case and there is no <code>union_eq_some</code>. Its proof is two steps: rewrite <code>Heap.union h₁ h₂ l</code> to <code>h₂ l</code> with <code>hl</code>, then that is <code>hl2</code>.' },
        { tac: 'rw [union_of_some h₃ hu, union_of_some h₃ hl2]', h: 'Left-hand side to <code>some v</code> with <code>hu</code>, right-hand side to <code>some v</code> with <code>hl2</code>.' },
        { tac: '| some v =>', h: 'Third regime, back at the outer split: <code>h₁</code> answers, so nothing else is ever consulted.' },
        { tac: 'rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]', h: 'Note the nesting: <code>union_of_some h₂ hl : Heap.union h₁ h₂ l = some v</code> is itself fed to <code>union_of_some h₃</code> to get a fact about the doubly nested union. The second rewrite handles the right-hand side, where <code>h₁</code> is the outer left argument and its partner is <code>Heap.union h₂ h₃</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'union_assoc — the three leaves',
          start: `h₁ h₂ h₃ : Heap
⊢ (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃)`,
          steps: [
            { tac: 'funext l',
              state: `h₁ h₂ h₃ : Heap
l : Loc
⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l`,
              h: 'Pointwise, with the printer’s bracketing: <code>(h₁.union h₂).union h₃</code> on the left, <code>h₁.union (h₂.union h₃)</code> on the right.' },
            { tac: 'cases hl : h₁ l with | none =>',
              state: `case none
h₁ h₂ h₃ : Heap
l : Loc
hl : h₁ l = none
⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l`,
              h: 'The goal is unchanged — <code>h₁ l</code> does not occur in it syntactically, it is buried inside the unions — but <code>hl</code> is now available.' },
            { tac: 'rw [union_of_none (Heap.union h₂ h₃) hl]',
              state: `case none
h₁ h₂ h₃ : Heap
l : Loc
hl : h₁ l = none
⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l`,
              h: 'Only the right-hand side moved. On the left, <code>h₁</code> is two levels down, which is why that side needs a manufactured fact.' },
            { tac: 'cases hl2 : h₂ l with | none =>',
              state: `case none.none
h₁ h₂ h₃ : Heap
l : Loc
hl : h₁ l = none
hl2 : h₂ l = none
⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l`,
              h: 'First leaf; the case name <code>none.none</code> records both decisions. <code>union_eq_none.mpr ⟨hl, hl2⟩</code> is exactly the fact the left-hand side is waiting for.' },
            { tac: '| some v =>',
              state: `case none.some
h₁ h₂ h₃ : Heap
l : Loc
hl : h₁ l = none
v : Val
hl2 : h₂ l = some v
⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l`,
              h: 'Second leaf. Same shape, but the answer is <code>some v</code> rather than <code>h₃ l</code>.' },
            { tac: 'have hu : Heap.union h₁ h₂ l = some v := …',
              state: `case none.some
h₁ h₂ h₃ : Heap
l : Loc
hl : h₁ l = none
v : Val
hl2 : h₂ l = some v
hu : h₁.union h₂ l = some v
⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l`,
              h: '<code>hu</code> is the missing rewrite rule for the left-hand side, playing the role <code>union_eq_none.mpr</code> played inline one leaf ago.' },
            { tac: '(the outer some branch)',
              state: `case some
h₁ h₂ h₃ : Heap
l : Loc
v : Val
hl : h₁ l = some v
⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l`,
              h: 'Third leaf and the shortest: one <code>rw</code> with two lemma applications makes both sides <code>some v</code>.' }
          ],
          done: 'No goals.' },
        { t: 'steps', title: 'Why there is no hypothesis to have',
          items: [
            { k: 'Both bracketings compute one selector', h: 'At a fixed <code>l</code>, <code>(h₁ ∪ h₂) ∪ h₃</code> asks: is <code>h₁ ∪ h₂</code> defined — which asks, is <code>h₁</code>, else is <code>h₂</code>? And <code>h₁ ∪ (h₂ ∪ h₃)</code> asks: is <code>h₁</code>, else is <code>h₂ ∪ h₃</code>? Both are “first <code>some</code> in the list”, and lists do not remember their brackets.' },
            { k: 'Overlap changes the answer identically on both sides', h: 'Where the heaps do overlap, the bias picks a value — the same value on the left and on the right. Disjointness is needed only where the <i>order</i> of the arguments has to stop mattering, and that is commutativity.' },
            { k: 'Which is what makes it a rewrite rule', h: 'A genuinely partial union is associative only in the guarded sense “where both sides are defined they agree”, and every use then drags a definedness obligation with it. The unguarded equation is strictly stronger, and strong enough to fire anywhere, in any context, with no context to check.' }
          ] }
      ],
      pitfall: 'Passing the wrong explicit heap to <code>union_of_none</code> / <code>union_of_some</code>. In the outer <code>none</code> branch the reflex is <code>rw [union_of_none h₃ hl]</code>, but that term has type <code>Heap.union h₁ h₃ l = h₃ l</code> — a statement about a union that does not occur in the goal, so <code>rw</code> reports that it failed to find the pattern. Ask every time: <i>which</i> union am I rewriting and what are its two arguments? On the left they are <code>Heap.union h₁ h₂</code> and <code>h₃</code>; on the right, <code>h₁</code> and <code>Heap.union h₂ h₃</code>.',
      variants: 'There is no hypothesis to drop, which is the content. What is worth comparing is the three-way disjointness picture: nothing in this proof assumes the heaps are pairwise disjoint, so <code>union_assoc</code> is available even in the middle of a proof where you have not yet established, or have just destroyed, the disjointness facts around it. Exercise 9 uses precisely that freedom — it re-brackets the heap equation first and rebuilds the disjointness separately.'
    },

    { t: 'ex',
      id: 'm2-6',
      name: 'union_comm',
      hard: false,
      why: 'The law this chapter opened on. Commutativity is the one place disjointness is <i>needed</i>, which is where the word “partial” in partial commutative monoid earns its keep.',
      goal: `theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁`,
      hints: [
        '<code>funext l</code>, and then use the hypothesis <i>at that location</i>: <code>hd l</code> is a disjunction, and <code>rcases hd l with h | h</code> gives you its two cases.',
        'In each case one heap is known to be <code>none</code> at <code>l</code>, so <code>union_of_none</code> collapses one side of the equation. The other side is still a union whose first argument is opaque, so it still needs a case split.',
        'Watch which side of the equals sign the surviving union is on after the first rewrite. If you collapsed the left, the remaining work is on the right, and your next rewrites have to be aimed there.',
        'The fiddly leaf is <code>none</code>/<code>none</code>: both sides really are <code>none</code>, but Lean is looking at <code>none = h₁ l</code>. Two rewrites chained in one <code>rw</code>, the second being the hypothesis itself, finish it.'
      ],
      hint: '<code>funext l</code>, then <code>rcases hd l</code>. In each branch one side is known to be <code>none</code>, so <code>union_of_none</code> collapses it; then case on the other heap.',
      sol: `theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext l
  rcases hd l with h | h
  · rw [union_of_none h₂ h]
    cases hl : h₂ l with
    | none   => rw [union_of_none h₁ hl, h]
    | some v => rw [union_of_some h₁ hl]
  · rw [union_of_none h₁ h]
    cases hl : h₁ l with
    | none   => rw [union_of_none h₂ hl]; exact h
    | some v => rw [union_of_some h₂ hl]`,
      expl: 'At each location disjointness says at least one heap is undefined there. If <code>h₁ l = none</code> then <code>union h₁ h₂ l = h₂ l</code>, and <code>union h₂ h₁ l</code> is <code>h₂ l</code> when that is <code>some</code>, or <code>h₁ l = none = h₂ l</code> when it is not. The proof is that sentence, mechanised — and the hypothesis is consumed at one location and nowhere else.',
      walk: [
        { tac: 'funext l', h: 'Pointwise.' },
        { tac: 'rcases hd l with h | h', h: 'The only use of the hypothesis in the whole proof, and it is used at a single location. Two goals, <code>inl</code> and <code>inr</code>; in the first <code>h : h₁ l = none</code>, in the second <code>h : h₂ l = none</code>. Reusing the name is deliberate — the two branches then read almost identically with the heaps swapped.' },
        { tac: '· rw [union_of_none h₂ h]', h: '<code>h₁ l = none</code>, so the left-hand side becomes <code>h₂ l</code> and the goal is <code>h₂ l = Heap.union h₂ h₁ l</code>. The unknown has moved to the right.' },
        { tac: 'cases hl : h₂ l with', h: 'The surviving union has <code>h₂</code> as its first argument, so that is the scrutinee.' },
        { tac: '| none   => rw [union_of_none h₁ hl, h]', h: 'Both heaps silent at <code>l</code>. <code>cases</code> already made the left-hand side <code>none</code>; the first rewrite makes the right-hand side <code>h₁ l</code>, leaving <code>none = h₁ l</code>; the second rewrite is <code>h</code> itself, which closes it.' },
        { tac: '| some v => rw [union_of_some h₁ hl]', h: '<code>h₂</code> answers at <code>l</code>; one rewrite makes the right-hand side <code>some v</code>.' },
        { tac: '· rw [union_of_none h₁ h]', h: 'Second branch, and now it is the <i>right</i>-hand side that collapses, to <code>h₁ l</code>. The goal is <code>Heap.union h₁ h₂ l = h₁ l</code>.' },
        { tac: 'cases hl : h₁ l with', h: 'Split on the first argument of the union that survived, which is now <code>h₁</code>.' },
        { tac: '| none   => rw [union_of_none h₂ hl]; exact h', h: 'Left-hand side becomes <code>h₂ l</code> and the goal is <code>h₂ l = none</code>, which is <code>h</code>. This branch ends in <code>exact</code> where its mirror image ended in a second rewrite — the difference is only which side of the equation the leftover sat on.' },
        { tac: '| some v => rw [union_of_some h₂ hl]', h: 'Last leaf: <code>h₁</code> answers, so the left-hand side is <code>some v</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'union_comm — four leaves, two of them nearly identical',
          start: `h₁ h₂ : Heap
hd : h₁.disjoint h₂
⊢ h₁.union h₂ = h₂.union h₁`,
          steps: [
            { tac: 'funext l',
              state: `h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
⊢ h₁.union h₂ l = h₂.union h₁ l`,
              h: '<code>hd</code> is still folded; applying it to <code>l</code> is what unfolds it.' },
            { tac: 'rcases hd l with h | h',
              state: `case inl
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₁ l = none
⊢ h₁.union h₂ l = h₂.union h₁ l`,
              h: '<code>hd</code> stays in context — you could use it at another location, though here you never need to.' },
            { tac: 'rw [union_of_none h₂ h]',
              state: `case inl
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₁ l = none
⊢ h₂ l = h₂.union h₁ l`,
              h: 'Left-hand side collapsed; everything remaining is about the right.' },
            { tac: 'cases hl : h₂ l with | none =>',
              state: `case inl.none
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₁ l = none
hl : h₂ l = none
⊢ none = h₂.union h₁ l`,
              h: 'The exposed <code>h₂ l</code> on the left became <code>none</code>; the copy buried in the union on the right was out of reach.' },
            { tac: 'rw [union_of_none h₁ hl]',
              state: `case inl.none
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₁ l = none
hl : h₂ l = none
⊢ none = h₁ l`,
              h: 'And the second element of the <code>rw</code> list, <code>h</code>, closes it.' },
            { tac: '(the inl.some leaf)',
              state: `case inl.some
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₁ l = none
v : Val
hl : h₂ l = some v
⊢ some v = h₂.union h₁ l`,
              h: 'One rewrite with <code>union_of_some h₁ hl</code>.' },
            { tac: '(the second rcases branch)',
              state: `case inr
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₂ l = none
⊢ h₁.union h₂ l = h₂.union h₁ l`,
              h: 'Same goal, other hypothesis. This is where reusing the name <code>h</code> pays off: what follows is the branch above with the roles exchanged.' },
            { tac: 'rw [union_of_none h₁ h]',
              state: `case inr
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₂ l = none
⊢ h₁.union h₂ l = h₁ l`,
              h: 'This time the <i>right</i>-hand side collapsed, so the residual work is on the left — hence <code>exact h</code> rather than a rewrite.' },
            { tac: 'cases hl : h₁ l with | none => rw [union_of_none h₂ hl]',
              state: `case inr.none
h₁ h₂ : Heap
hd : h₁.disjoint h₂
l : Loc
h : h₂ l = none
hl : h₁ l = none
⊢ h₂ l = none`,
              h: 'Which is exactly <code>h</code>.' }
          ],
          done: 'No goals.' }
      ],
      pitfall: 'Copy-pasting the first <code>rcases</code> branch into the second. They look symmetric and are not: the first rewrite lands on the left-hand side in one branch and on the right in the other, so the <code>none</code> leaf ends <code>rw [union_of_none h₁ hl, h]</code> here and <code>rw [union_of_none h₂ hl]; exact h</code> there. Paste, and <code>rw</code> complains it cannot find the pattern while the goal <i>reads</i> exactly like the one you just succeeded on. Read the pattern it printed instead: <code>union_of_none h₂ h</code> with <code>h : h₂ l = none</code> is a fact about <code>h₂.union h₂</code>, and a doubled heap name in the error means you fed the lemma the wrong disjunct.',
      variants: 'The counterexample is the one this chapter opened with: <code>h₁ = 0 ↦ 1</code>, <code>h₂ = 0 ↦ 2</code>, and the left-biased union answers <code>some 1</code> one way round and <code>some 2</code> the other. Notice how little is needed — one location, and the heaps need not be singletons. This is the exact sense in which the monoid is <i>partial</i>: the operation is defined everywhere, the commutative law is claimed only on the compatible pairs, and <code>Heap.disjoint</code> is the name of that compatibility.<br><br>Commutativity is also the only law in the table with a hypothesis to drop, and that is not an accident of this model. It is the one law that asks the operation to forget the order of its arguments, and the order is exactly what the bias remembers.'
    },

    { t: 'ex',
      id: 'm2-7',
      name: 'disjoint_union_left / right',
      hard: false,
      why: 'The workhorses of the whole course. Every re-bracketing of a separating conjunction destroys some disjointness facts and needs others built, and it is always one of these two, in one of their two directions. Exercise 9 uses three of the four.',
      goal: `theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃`,
      hints: [
        '<code>constructor</code> on the <code>↔</code>. In the forward direction the goal is a conjunction of two <code>∀</code>s, so you have to build a pair whose components are functions of a location.',
        '<code>refine ⟨fun l =&gt; ?_, fun l =&gt; ?_⟩</code> does that in one move: it commits to the pair and to both lambdas and leaves two pointwise goals, each with its own <code>l</code>.',
        'Both goals open the same way, <code>rcases hd l with h | h</code>. In the <code>inr</code> case <code>h : h₃ l = none</code> already proves the right disjunct. In the <code>inl</code> case <code>h : Heap.union h₁ h₂ l = none</code>, and <code>union_eq_none.mp h</code> turns that into a pair — take <code>.1</code> in the first goal and <code>.2</code> in the second.',
        'Backwards, <code>intro ⟨ha, hb⟩ l</code> destructures the conjunction and introduces the location in one tactic. Then case on <code>ha l</code>, and inside its <code>none</code> case on <code>hb l</code>, rebuilding with <code>union_eq_none.mpr</code>.',
        'Do not prove <code>disjoint_union_right</code> from scratch. It is the left version conjugated by <code>disjoint_symm</code>: symmetrise the input, apply the left lemma, symmetrise both outputs.'
      ],
      hint: 'Prove the left one from <code>union_eq_none</code>; then get the right one for free by conjugating with <code>disjoint_symm</code>.',
      sol: `theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by
  constructor
  · intro hd
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rcases hd l with h | h
      · exact Or.inl (union_eq_none.mp h).1
      · exact Or.inr h
    · rcases hd l with h | h
      · exact Or.inl (union_eq_none.mp h).2
      · exact Or.inr h
  · intro ⟨ha, hb⟩ l
    rcases ha l with h | h
    · rcases hb l with h' | h'
      · exact Or.inl (union_eq_none.mpr ⟨h, h'⟩)
      · exact Or.inr h'
    · exact Or.inr h

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by
  constructor
  · intro hd
    have h' := disjoint_union_left.mp (disjoint_symm hd)
    exact ⟨disjoint_symm h'.1, disjoint_symm h'.2⟩
  · intro ⟨ha, hb⟩
    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)`,
      expl: 'Forwards, all the content is <code>union_eq_none.mp</code>: a union undefined at <code>l</code> means both halves are. Backwards you have to decide which disjunct to prove, and that depends on the data, so the case analysis is on your own hypotheses rather than on the goal. The <code>right</code> version is not proved again — it is <code>left</code> sandwiched between two applications of <code>disjoint_symm</code>.',
      walk: [
        { tac: 'constructor', h: 'Splits the <code>↔</code> into <code>mp</code> and <code>mpr</code>.' },
        { tac: '· intro hd', h: 'Forwards: one disjointness fact, to be split into two.' },
        { tac: 'refine ⟨fun l => ?_, fun l => ?_⟩', h: '<code>refine</code> is <code>exact</code> with holes: you give the shape of the answer and every <code>?_</code> becomes a new goal. Here the goal is <code>A ∧ B</code> with each conjunct a <code>∀ l, …</code>, and one tactic supplies the pair <i>and</i> both lambdas, leaving two goals with <code>l</code> already introduced and named <code>refine_1</code> and <code>refine_2</code> in the order written. <code>constructor</code> then <code>intro l</code> twice does the same in three tactics.' },
        { tac: '· rcases hd l with h | h', h: 'First hole: <code>h₁ l = none ∨ h₃ l = none</code>. Instantiate the hypothesis at the same location and split.' },
        { tac: '· exact Or.inl (union_eq_none.mp h).1', h: 'Three operations in one term. <code>union_eq_none.mp h : h₁ l = none ∧ h₂ l = none</code>; <code>.1</code> takes the half about <code>h₁</code>; <code>Or.inl</code> injects it as the left disjunct of the goal.' },
        { tac: '· exact Or.inr h', h: '<code>h : h₃ l = none</code> is already the right disjunct. Nothing about the union is needed in this branch at all.' },
        { tac: '· rcases hd l with h | h', h: 'Second hole: <code>h₂ l = none ∨ h₃ l = none</code>. Same opening.' },
        { tac: '· exact Or.inl (union_eq_none.mp h).2', h: 'Identical but for <code>.2</code>. That one character is the entire difference between the two holes.' },
        { tac: '· exact Or.inr h', h: 'And the same shortcut.' },
        { tac: '· intro ⟨ha, hb⟩ l', h: 'Backwards. Three introductions from one tactic: the conjunction, destructured on arrival into <code>ha</code> and <code>hb</code>, and then the location of the goal <code>Heap.disjoint (Heap.union h₁ h₂) h₃</code> — two of the three invisible in the statement.' },
        { tac: 'rcases ha l with h | h', h: 'Now <i>we</i> choose which disjunct to prove, and the choice depends on the data. Start with what <code>h₁</code> does at <code>l</code>.' },
        { tac: '· rcases hb l with h\' | h\'', h: 'If <code>h₁ l = none</code>, whether the union is <code>none</code> still turns on <code>h₂</code>, so ask <code>hb</code> too. The name is primed because <code>h</code> is taken.' },
        { tac: '· exact Or.inl (union_eq_none.mpr ⟨h, h\'⟩)', h: 'Both halves silent: rebuild the fact about the union with the backward direction of the same iff, fed the pair.' },
        { tac: '· exact Or.inr h\'', h: '<code>h₂ l</code> unknown, but <code>h\' : h₃ l = none</code> settles the goal without touching the union.' },
        { tac: '· exact Or.inr h', h: 'And if <code>ha</code> gave <code>h₃ l = none</code> straight away, this branch never learns anything about <code>h₂</code>.' },
        { tac: 'have h\' := disjoint_union_left.mp (disjoint_symm hd)', h: 'Second theorem, and the whole of it. <code>hd : Heap.disjoint h₁ (Heap.union h₂ h₃)</code> has the union on the wrong side, so flip it: <code>disjoint_symm hd</code> is the left-hand side of <code>disjoint_union_left</code> with <code>(h₂, h₃, h₁)</code> for <code>(h₁, h₂, h₃)</code>, found by unification. <code>h\' : Heap.disjoint h₂ h₁ ∧ Heap.disjoint h₃ h₁</code> — the goal with both components reversed.' },
        { tac: 'exact ⟨disjoint_symm h\'.1, disjoint_symm h\'.2⟩', h: 'Flip both back. Conjugation by an involution: <code>symm</code> in, lemma, <code>symm</code> out.' },
        { tac: 'exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)', h: 'The same conjugation read right to left: symmetrise both inputs, apply the left lemma backwards, symmetrise the output. Four uses of one lemma and no new reasoning.' }
      ],
      deep: [
        { t: 'trace', title: 'disjoint_union_left, forwards',
          steps: [
            { tac: 'constructor · intro hd',
              state: `case mp
h₁ h₂ h₃ : Heap
hd : (h₁.union h₂).disjoint h₃
⊢ h₁.disjoint h₃ ∧ h₂.disjoint h₃`,
              h: 'One fact in, two out. Nothing unfolded yet.' },
            { tac: 'refine ⟨fun l => ?_, fun l => ?_⟩',
              state: `case mp.refine_1
h₁ h₂ h₃ : Heap
hd : (h₁.union h₂).disjoint h₃
l : Loc
⊢ h₁ l = none ∨ h₃ l = none`,
              h: 'The first hole, already unfolded and already carrying its <code>l</code>: <code>refine</code> did the pairing, both lambdas, and the definitional unfolding in one step.' },
            { tac: 'rcases hd l with h | h',
              state: `case mp.refine_1.inl
h₁ h₂ h₃ : Heap
hd : (h₁.union h₂).disjoint h₃
l : Loc
h : h₁.union h₂ l = none
⊢ h₁ l = none ∨ h₃ l = none`,
              h: 'The interesting case: the union is undefined at <code>l</code> and the fact about <code>h₁</code> has to be extracted, which is <code>union_eq_none.mp</code>.' },
            { tac: '(the other disjunct)',
              state: `case mp.refine_1.inr
h₁ h₂ h₃ : Heap
hd : (h₁.union h₂).disjoint h₃
l : Loc
h : h₃ l = none
⊢ h₁ l = none ∨ h₃ l = none`,
              h: 'The dull case: <code>h</code> <i>is</i> the right disjunct.' },
            { tac: '(the second hole)',
              state: `case mp.refine_2
h₁ h₂ h₃ : Heap
hd : (h₁.union h₂).disjoint h₃
l : Loc
⊢ h₂ l = none ∨ h₃ l = none`,
              h: 'Identical in shape with <code>h₂</code> for <code>h₁</code>, and handled identically except for taking <code>.2</code> of the pair.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'disjoint_union_left, backwards',
          steps: [
            { tac: '· intro ⟨ha, hb⟩ l',
              state: `case mpr
h₁ h₂ h₃ : Heap
ha : h₁.disjoint h₃
hb : h₂.disjoint h₃
l : Loc
⊢ h₁.union h₂ l = none ∨ h₃ l = none`,
              h: 'Three introductions from one tactic.' },
            { tac: 'rcases ha l with h | h',
              state: `case mpr.inl
h₁ h₂ h₃ : Heap
ha : h₁.disjoint h₃
hb : h₂.disjoint h₃
l : Loc
h : h₁ l = none
⊢ h₁.union h₂ l = none ∨ h₃ l = none`,
              h: 'Knowing <code>h₁ l = none</code> is not yet enough to say the union is <code>none</code> — the union also consults <code>h₂</code>.' },
            { tac: 'rcases hb l with h\' | h\'',
              state: `case mpr.inl.inl
h₁ h₂ h₃ : Heap
ha : h₁.disjoint h₃
hb : h₂.disjoint h₃
l : Loc
h : h₁ l = none
h' : h₂ l = none
⊢ h₁.union h₂ l = none ∨ h₃ l = none`,
              h: 'Now it is, and <code>union_eq_none.mpr ⟨h, h\'⟩</code> assembles the left disjunct.' },
            { tac: '(the h\' : h₃ l = none case)',
              state: `case mpr.inl.inr
h₁ h₂ h₃ : Heap
ha : h₁.disjoint h₃
hb : h₂.disjoint h₃
l : Loc
h : h₁ l = none
h' : h₃ l = none
⊢ h₁.union h₂ l = none ∨ h₃ l = none`,
              h: 'Shortcut: <code>h\'</code> settles the right disjunct and the union is irrelevant.' },
            { tac: '(the outer inr case)',
              state: `case mpr.inr
h₁ h₂ h₃ : Heap
ha : h₁.disjoint h₃
hb : h₂.disjoint h₃
l : Loc
h : h₃ l = none
⊢ h₁.union h₂ l = none ∨ h₃ l = none`,
              h: 'Same shortcut one level up. Three of the four leaves are one-liners; only <code>mpr.inl.inl</code> does anything.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'disjoint_union_right — derived, not reproved',
          steps: [
            { tac: 'constructor · intro hd',
              state: `case mp
h₁ h₂ h₃ : Heap
hd : h₁.disjoint (h₂.union h₃)
⊢ h₁.disjoint h₂ ∧ h₁.disjoint h₃`,
              h: 'The union is on the right; the lemma we have wants it on the left.' },
            { tac: 'have h\' := disjoint_union_left.mp (disjoint_symm hd)',
              state: `case mp
h₁ h₂ h₃ : Heap
hd : h₁.disjoint (h₂.union h₃)
h' : h₂.disjoint h₁ ∧ h₃.disjoint h₁
⊢ h₁.disjoint h₂ ∧ h₁.disjoint h₃`,
              h: 'Compare <code>h\'</code> with the goal: the same pair with both components reversed. Two applications of <code>disjoint_symm</code> finish a theorem that would otherwise be a copy of the fifteen lines above.' },
            { tac: '(the mpr direction)',
              state: `case mpr
h₁ h₂ h₃ : Heap
ha : h₁.disjoint h₂
hb : h₁.disjoint h₃
⊢ h₁.disjoint (h₂.union h₃)`,
              h: 'Same conjugation the other way: flip <code>ha</code> and <code>hb</code>, apply <code>disjoint_union_left.mpr</code>, flip the result.' }
          ],
          done: 'No goals.' }
      ],
      pitfall: 'Taking <code>.1</code> where <code>.2</code> is wanted. The two <code>refine</code> holes differ in one character, and the slip is reported as a mismatch between <code>h₁ l = none</code> and <code>h₂ l = none</code> buried inside an <code>Or.inl</code> — pointing at the injection rather than at the projection. When a proof is this compressed, read the goal first and the error second. Second trap: all three arguments of <code>union_eq_none</code> are implicit, so <code>union_eq_none.mp h</code> unifies silently against whatever <code>h</code> happens to be, and feeding it the wrong hypothesis produces a unification failure about heaps you never mentioned.',
      variants: 'Both statements are genuine iffs and every direction is load-bearing. <code>splits_assoc</code> below uses <code>disjoint_union_left.mp</code> to take a coarse fact apart and <code>disjoint_union_right.mpr</code> to build a new one; M4’s <code>star_assoc_left</code> does the same two things and <code>star_assoc_right</code> uses the mirror pair. Weaken either to an implication and one of those four proofs stops.<br><br>Note what is absent: no hypothesis relating <code>h₁</code> to <code>h₂</code> appears anywhere. Compatibility distributes over the total biased union with no compatibility assumption of its own, which is what makes these safe to use as rewriting iffs in any context.'
    },

    /* ================================================================
       5 — splitting
       ================================================================ */

    { t: 'sec', s: 'Exercises · splitting' },

    { t: 'p', h: 'A union and a disjointness fact always travel together, so bundle them. The third definition of the chapter is the relation the other two exist for.' },

    { t: 'code',
      src: `def Heap.splits (whole left right : Heap) : Prop :=
  Heap.disjoint left right ∧ whole = Heap.union left right` },

    { t: 'p', h: 'A proof is a pair <code>⟨hd, he⟩</code>, and both exercises below are pairing and unpairing plus one union law. Note the direction of the equation: <code>whole = Heap.union left right</code>, the whole on the left. That is the direction you consume it in, and the unit laws pay for it — the aside under exercise 8 itemises the bill.' },

    { t: 'svg',
      src: `
<svg viewBox="0 0 560 172" role="img" aria-label="Splitting a heap into two disjoint parts">
  <g class="dg">
    <rect x="20" y="26" width="220" height="60" rx="8" class="dg-box"/>
    <text x="130" y="62" text-anchor="middle" class="dg-t">h</text>
    <text x="130" y="18" text-anchor="middle" class="dg-lab">one heap</text>
    <path class="dg-arr" d="M250 56 L 300 56"/>
    <rect x="312" y="20" width="106" height="34" rx="7" class="dg-box a"/>
    <text x="365" y="42" text-anchor="middle" class="dg-t">h₁</text>
    <rect x="430" y="20" width="106" height="34" rx="7" class="dg-box b"/>
    <text x="483" y="42" text-anchor="middle" class="dg-t">h₂</text>
    <text x="424" y="76" text-anchor="middle" class="dg-note">disjoint: domains never overlap</text>
    <text x="424" y="94" text-anchor="middle" class="dg-note">h = h₁ ∪ h₂</text>
    <g class="dg-cells">
      <rect x="36" y="112" width="34" height="26" rx="4" class="a"/>
      <rect x="76" y="112" width="34" height="26" rx="4" class="b"/>
      <rect x="116" y="112" width="34" height="26" rx="4" class="a"/>
      <rect x="156" y="112" width="34" height="26" rx="4" class="b"/>
      <rect x="196" y="112" width="34" height="26" rx="4" class="a"/>
    </g>
    <text x="130" y="158" text-anchor="middle" class="dg-note">every allocated cell belongs to exactly one side</text>
  </g>
</svg>` },

    { t: 'p', h: 'The two proofs below are, line for line, the two proofs you will write in M4. <code>star_comm</code> is <code>splits_comm</code> with two heaps and two assertion facts added to the tuple; <code>star_assoc_left</code> is <code>splits_assoc</code> with the same addition. Getting the shape into your fingers is the point of doing them small.' },

    { t: 'detail', title: 'Why M4 does not build <code>∗</code> on <code>Heap.splits</code>', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: '<code>Heap.splits</code> is used in this chapter and then never again. M4 writes the two conjuncts out instead:' },
        { t: 'code', cap: 'The middle two components are <code>Heap.splits h h₁ h₂</code>, unbundled.',
          src: `def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂` },
        { t: 'p', h: 'The reason is ergonomic. Flat, the whole thing comes apart in one <code>intro ⟨h₁, h₂, hd, hu, hp, hq⟩</code>; bundled, that pattern needs an extra layer of brackets at every use, in every proof, for ten chapters. So <code>splits</code> earns its keep here, as the name under which the laws are proved in the small, and from M4 you meet the same laws with the pair spread out.' }
      ] },

    { t: 'ex',
      id: 'm2-8',
      name: 'splits_empty_left / splits_comm',
      hard: false,
      why: 'These are M4’s <code>star_emp_left_intro</code> (<code>P ⊢ emp ∗ P</code>) and <code>star_comm</code> (<code>P ∗ Q ⊢ Q ∗ P</code>) with the assertion machinery deleted. Not an analogy: <code>star_comm</code>’s proof is <code>exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩</code>, which is the tuple below with two heaps and two assertion facts inserted. They also drill the one thing about <code>splits</code> that catches everybody — the direction of its equation.',
      goal: `theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h
theorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁`,
      hints: [
        'Both are pairing. Neither needs a case analysis on anything.',
        'For <code>splits_empty_left</code> the components are <code>disjoint_empty_left h</code> and a proof of <code>h = Heap.union Heap.empty h</code>. You hold <code>union_empty_left h</code>, whose equation points the other way; <code>Eq.symm</code>, written <code>.symm</code>, turns it round.',
        'For <code>splits_comm</code>, <code>intro ⟨hd, he⟩</code> introduces the hypothesis already destructured: <code>hd</code> the disjointness, <code>he : h = Heap.union h₁ h₂</code>.',
        'The second component of the answer is <code>h = Heap.union h₂ h₁</code>. Rewrite with <code>he</code> to make the goal <code>Heap.union h₁ h₂ = Heap.union h₂ h₁</code>, which is <code>union_comm hd</code> — with <code>hd</code>, not <code>disjoint_symm hd</code>.'
      ],
      hint: 'Both are direct consequences of the lemmas you already have.',
      sol: `theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=
  ⟨disjoint_empty_left h, (union_empty_left h).symm⟩

theorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁ := by
  intro ⟨hd, he⟩
  exact ⟨disjoint_symm hd, by rw [he, union_comm hd]⟩`,
      expl: 'The empty heap is disjoint from everything and is a left unit, so the first theorem is those two lemmas paired — with the equation turned round, because <code>splits</code> states it as whole-equals-union-of-parts. The second takes the pair apart and rebuilds it with <code>disjoint_symm</code> on one component and <code>union_comm</code> on the other.',
      walk: [
        { tac: '⟨disjoint_empty_left h, …⟩', h: 'First theorem, as a term. The anonymous constructor builds the conjunction and the first component is exercise 2, unchanged.' },
        { tac: '(union_empty_left h).symm', h: '<code>union_empty_left h : Heap.union Heap.empty h = h</code>, but <code>splits</code> asks for <code>h = Heap.union Heap.empty h</code>. <code>.symm</code> here is <code>Eq.symm</code>, found from the head constant of the type.' },
        { tac: 'intro ⟨hd, he⟩', h: 'Second theorem. The hypothesis is introduced and destructured in one breath, giving <code>hd : Heap.disjoint h₁ h₂</code> and <code>he : h = Heap.union h₁ h₂</code>. <code>intro hs</code> then <code>obtain ⟨hd, he⟩ := hs</code> is the same in two steps.' },
        { tac: 'exact ⟨disjoint_symm hd, …⟩', h: 'Build the answer pair; the first component is exercise 1, cashed in.' },
        { tac: 'by rw [he, union_comm hd]', h: 'A tactic block used as a term. The goal there is <code>h = Heap.union h₂ h₁</code>; <code>rw [he]</code> replaces <code>h</code> by <code>Heap.union h₁ h₂</code> and <code>union_comm hd</code> rewrites that to <code>Heap.union h₂ h₁</code>, leaving <code>a = a</code>. Used left to right, so the disjointness wanted is that of the <i>original</i> pair.' }
      ],
      deep: [
        { t: 'trace', title: 'splits_comm, with the nested `by` spelled out as tactics',
          start: `h h₁ h₂ : Heap
⊢ h.splits h₁ h₂ → h.splits h₂ h₁`,
          steps: [
            { tac: 'intro ⟨hd, he⟩',
              state: `h h₁ h₂ : Heap
hd : h₁.disjoint h₂
he : h = h₁.union h₂
⊢ h.splits h₂ h₁`,
              h: 'The conjunction never appears as such. Two hypotheses, and the goal is still folded.' },
            { tac: 'refine ⟨disjoint_symm hd, ?_⟩',
              state: `h h₁ h₂ : Heap
hd : h₁.disjoint h₂
he : h = h₁.union h₂
⊢ h = h₂.union h₁`,
              h: 'Supplying the first component unfolds <code>splits</code> and leaves the heap equation — which is what the <code>by</code> block in the real proof is proving.' },
            { tac: 'rw [he]',
              state: `h h₁ h₂ : Heap
hd : h₁.disjoint h₂
he : h = h₁.union h₂
⊢ h₁.union h₂ = h₂.union h₁`,
              h: 'Literally the statement of <code>union_comm hd</code>.' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'What the direction of the equation costs', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: '<code>whole = union left right</code> is the direction you consume. In M4 you hold a heap <code>h</code> and a proof that it splits, and you want to <i>replace</i> <code>h</code> by the union: that is <code>rw [he]</code>, left to right. Written the other way you would spend the course typing <code>rw [← he]</code>.' },
            { t: 'p', h: 'The bill is that the unit laws come out of this chapter pointing the wrong way. <code>(union_empty_left _).symm</code> and <code>(union_empty_right _).symm</code> occur nine times between here and M10 — in <code>splits_empty_left</code>, in M4’s <code>star_emp_left_intro</code> and <code>star_pure_right</code>, in M7’s <code>hoare_load</code>, in M10’s concrete list. Nine appended <code>.symm</code>s against a course-long supply of <code>←</code>: the trade is worth it.' }
          ] }
      ],
      pitfall: 'Forgetting the <code>.symm</code> — and getting away with it, which is worse. <code>⟨disjoint_empty_left h, union_empty_left h⟩</code> is accepted, although the lemma’s equation points the wrong way, because <code>Heap.union Heap.empty h</code> is <i>definitionally</i> <code>h</code> and the two propositions are therefore the same proposition up to unfolding. The habit that builds is wrong. Try the same omission on the mirror statement and Lean is unforgiving:<br><br><code>example (h : Heap) : Heap.splits h h Heap.empty := ⟨disjoint_empty_right h, union_empty_right h⟩</code><br><br><code>error: Application type mismatch: The argument union_empty_right h has type h.union Heap.empty = h but is expected to have type h = h.union Heap.empty</code><br><br>Whenever a component of a <code>splits</code> pair is rejected for no visible reason, check the orientation of the equation before anything else.',
      variants: 'The right-handed unit, <code>Heap.splits h h Heap.empty</code>, goes through the same way from <code>disjoint_empty_right</code> and <code>(union_empty_right h).symm</code> — but <code>union_empty_right</code> was the one that needed a case split, so the “symmetric” statement is genuinely the more expensive of the two.<br><br><code>splits_comm</code>’s content is <code>union_comm</code>, so it inherits that lemma’s dependence on disjointness. There is no hypothesis-free version, and none is wanted: the disjointness is part of what <code>splits</code> asserts, so it is always already in your hand at the moment you need it. That is what bundling buys.'
    },

    { t: 'ex',
      id: 'm2-9',
      name: 'splits_assoc',
      hard: true,
      why: 'Associativity of <code>∗</code> with the assertions deleted. Three pairwise disjointness facts are the real content of a three-way splitting, and re-bracketing is possible precisely because that content does not remember the brackets. Prove it here and M4’s <code>star_assoc</code> is bookkeeping.',
      goal: `theorem splits_assoc {h hPQ hP hQ hR : Heap}
    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :
    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR`,
      hints: [
        'Both hypotheses are conjunctions. <code>obtain ⟨hd₁, he₁⟩ := h1</code> and the same for <code>h2</code> put four facts in the context: two disjointness proofs and two heap equations.',
        '<code>he₂ : hPQ = Heap.union hP hQ</code> has a local variable on the left, so <code>subst he₂</code> eliminates <code>hPQ</code> outright. Afterwards <code>hd₁</code> and <code>he₁</code> speak about <code>Heap.union hP hQ</code> directly, which is what the union lemmas can see.',
        '<code>hd₁</code> is then exactly the left-hand side of <code>disjoint_union_left</code>. <code>obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁</code> hands you <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code> separately.',
        'The witness is <code>Heap.union hQ hR</code>. Disjointness of <code>hP</code> from it is <code>disjoint_union_right.mpr</code> applied to <code>⟨hd₂, hPR⟩</code>. The second <code>splits</code> is <code>⟨hQR\', rfl⟩</code> — <code>rfl</code>, because you chose the witness to be syntactically that union.',
        'Assemble with one <code>refine</code>, leaving <code>?_</code> for the single genuine heap equation, and finish with <code>rw [he₁, union_assoc]</code>.'
      ],
      hint: 'Substitute <code>hPQ = hP ∪ hQ</code>, then use <code>disjoint_union_left</code> to split <code>hd₁</code> into <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code>. The witness is <code>hQ ∪ hR</code>, and its disjointness from <code>hP</code> comes from <code>disjoint_union_right</code>.',
      sol: `theorem splits_assoc {h hPQ hP hQ hR : Heap}
    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :
    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by
  obtain ⟨hd₁, he₁⟩ := h1
  obtain ⟨hd₂, he₂⟩ := h2
  subst he₂
  obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁
  refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩
  rw [he₁, union_assoc]`,
      expl: 'The two <code>disjoint_union_*</code> uses are the argument. From <code>(hP ∪ hQ) ⊥ hR</code> extract <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code>; with the given <code>hP ⊥ hQ</code> that is all three pairwise facts, from which <code>hP ⊥ (hQ ∪ hR)</code> can be assembled. The heap equation is one <code>union_assoc</code>, unconditional, so the step that moves the brackets adds no obligation.',
      walk: [
        { tac: 'obtain ⟨hd₁, he₁⟩ := h1', h: 'Unpack the outer splitting: <code>hd₁ : Heap.disjoint hPQ hR</code> and <code>he₁ : h = Heap.union hPQ hR</code>.' },
        { tac: 'obtain ⟨hd₂, he₂⟩ := h2', h: 'And the inner one: <code>hd₂ : Heap.disjoint hP hQ</code>, <code>he₂ : hPQ = Heap.union hP hQ</code>.' },
        { tac: 'subst he₂', h: 'The pivotal step. <code>hPQ</code> is a variable, so it is eliminated rather than rewritten: every occurrence, in <code>hd₁</code> and in <code>he₁</code>, becomes <code>Heap.union hP hQ</code>. <code>rw [he₂] at hd₁ he₁</code> would leave the proof working but leave <code>hPQ</code> and <code>he₂</code> in the context referring to nothing you can still use. <code>subst</code> leaves no residue.' },
        { tac: 'obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁', h: 'First of the two real steps. <code>hd₁</code> now has the shape the lemma wants, and its forward direction gives <code>hPR : Heap.disjoint hP hR</code> and <code>hQR\' : Heap.disjoint hQ hR</code>. This is the moment the given bracketing is dismantled.' },
        { tac: 'refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR\', rfl⟩⟩', h: 'One tactic doing four things: the witness; then the first <code>splits</code>, whose disjointness component is the second real step, <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩ : Heap.disjoint hP (Heap.union hQ hR)</code>, built from the fact you were given and the one you just extracted; then <code>?_</code> for its heap equation; then the second <code>splits</code>, which is <code>⟨hQR\', rfl⟩</code> outright.' },
        { tac: 'rw [he₁, union_assoc]', h: 'The one surviving goal is <code>h = Heap.union hP (Heap.union hQ hR)</code>. <code>rw [he₁]</code> replaces <code>h</code> by the left-bracketed union and <code>union_assoc</code> rewrites that into the right-bracketed one.' }
      ],
      deep: [
        { t: 'trace', title: 'splits_assoc, tactic by tactic',
          start: `h hPQ hP hQ hR : Heap
h1 : h.splits hPQ hR
h2 : hPQ.splits hP hQ
⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR`,
          steps: [
            { tac: 'obtain ⟨hd₁, he₁⟩ := h1  /  obtain ⟨hd₂, he₂⟩ := h2',
              state: `h hPQ hP hQ hR : Heap
hd₁ : hPQ.disjoint hR
he₁ : h = hPQ.union hR
hd₂ : hP.disjoint hQ
he₂ : hPQ = hP.union hQ
⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR`,
              h: 'Four facts, one goal. Everything from here is combinatorics on these four.' },
            { tac: 'subst he₂',
              state: `h hP hQ hR : Heap
hd₂ : hP.disjoint hQ
hd₁ : (hP.union hQ).disjoint hR
he₁ : h = (hP.union hQ).union hR
⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR`,
              h: '<code>hPQ</code> has left the variable list, and the two facts about it now speak in terms of <code>hP</code> and <code>hQ</code>. Compare the previous state: that is the whole reason to prefer <code>subst</code> to <code>rw … at</code>.' },
            { tac: 'obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁',
              state: `h hP hQ hR : Heap
hd₂ : hP.disjoint hQ
hd₁ : (hP.union hQ).disjoint hR
he₁ : h = (hP.union hQ).union hR
hPR : hP.disjoint hR
hQR' : hQ.disjoint hR
⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR`,
              h: 'Three pairwise facts are now on the table: <code>hP ⊥ hQ</code>, <code>hP ⊥ hR</code>, <code>hQ ⊥ hR</code>. That is the entire information content of a three-way splitting, and it says nothing about brackets — which is why re-bracketing is possible at all.' },
            { tac: 'refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR\', rfl⟩⟩',
              state: `h hP hQ hR : Heap
hd₂ : hP.disjoint hQ
hd₁ : (hP.union hQ).disjoint hR
he₁ : h = (hP.union hQ).union hR
hPR : hP.disjoint hR
hQR' : hQ.disjoint hR
⊢ h = hP.union (hQ.union hR)`,
              h: 'One goal survives. Every disjointness obligation was discharged inline.' },
            { tac: 'rw [he₁]',
              state: `h hP hQ hR : Heap
hd₂ : hP.disjoint hQ
hd₁ : (hP.union hQ).disjoint hR
he₁ : h = (hP.union hQ).union hR
hPR : hP.disjoint hR
hQR' : hQ.disjoint hR
⊢ (hP.union hQ).union hR = hP.union (hQ.union hR)`,
              h: 'Which is <code>union_assoc hP hQ hR</code>, verbatim.' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'Why that <code>⟨…⟩</code> has three components and not two', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The goal is <code>∃ hQR, A ∧ B</code>, and <code>Exists.intro</code> takes two arguments, so you would expect <code>⟨witness, proof⟩</code>. The <code>refine</code> supplies three. This is the anonymous constructor’s one piece of magic: <b>surplus components are re-nested into the last field</b>. <code>⟨a, b, c⟩</code> elaborates as <code>⟨a, ⟨b, c⟩⟩</code>, <code>⟨a, b, c, d⟩</code> as <code>⟨a, ⟨b, ⟨c, d⟩⟩⟩</code>. Both of these are accepted here:' },
            { t: 'code', tag: 'sketch',
              src: `refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩

refine ⟨Heap.union hQ hR, ⟨⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩⟩` },
            { t: 'p', h: 'The second is what the first means. The re-nesting only ever goes to the <i>right</i>, so it flattens a right-leaning chain and nothing else. The inner brackets survive because the tree there is <code>(A₁ ∧ A₂) ∧ (B₁ ∧ B₂)</code>, left-leaning at the top. Flatten those too and it breaks:' },
            { t: 'cmp',
              left: { t: 'Flattening one level too far', kind: 'bad',
                h: 'Five components for <code>∃ hQR, (A₁ ∧ A₂) ∧ (B₁ ∧ B₂)</code>.',
                src: `refine ⟨Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hQR', rfl⟩`, tag: 'sketch' },
              right: { t: 'What Lean says',
                h: 'The right-nesting put a disjointness proof where a whole <code>Heap.splits</code> was expected.',
                src: `error: Application type mismatch: The argument
  disjoint_union_right.mpr ⟨hd₂, hPR⟩
has type
  hP.disjoint (hQ.union hR)
but is expected to have type
  h.splits hP (hQ.union hR)
in the application
  And.intro (disjoint_union_right.mpr ⟨hd₂, hPR⟩)`, tag: 'sketch' } },
            { t: 'p', h: 'One thing more is happening silently. <code>Heap.splits h hP hQR</code> is a <code>def</code>, not a structure, so <code>⟨_, _⟩</code> works on it only because the elaborator reduces the expected type to weak head normal form first, finds <code>And</code>, and uses <code>And.intro</code> — the same mechanism as <code>intro l</code> seeing the <code>∀</code> inside <code>Heap.disjoint</code>. In M4 the definition of <code>∗</code> is one long right-leaning chain, so there the flattening does apply all the way down and you write six components in a row.' }
          ] },
        { t: 'steps', title: 'The argument, without Lean',
          items: [
            { k: 'Given', h: '<code>h = (hP ∪ hQ) ∪ hR</code>, with <code>hP ⊥ hQ</code> and <code>(hP ∪ hQ) ⊥ hR</code>.' },
            { k: 'Take the coarse fact apart', h: '<code>(hP ∪ hQ) ⊥ hR</code> gives <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code>: <code>disjoint_union_left</code>, forwards. All three pairwise facts are now in hand.' },
            { k: 'Put it back together the other way', h: '<code>hP ⊥ hQ</code> and <code>hP ⊥ hR</code> give <code>hP ⊥ (hQ ∪ hR)</code>: <code>disjoint_union_right</code>, backwards. The two lemmas run in opposite directions, which is why both had to be iffs.' },
            { k: 'Move the brackets', h: 'Unconditionally, by <code>union_assoc</code>. The step that changes the shape is the one step that generates nothing to discharge.' },
            { k: 'What M4 adds', h: 'Two binders and three assertion facts to carry, and nothing else. <code>star_assoc_left</code> is <code>subst</code>, <code>obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁</code>, a <code>refine</code> containing <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code>, and <code>rw [hu₁, union_assoc]</code> — these five lines with <code>hp</code>, <code>hq</code>, <code>hr</code> threaded through.' }
          ] }
      ],
      pitfall: 'Expecting <code>rfl</code> to work for the second <code>splits</code> after choosing a different witness. <code>⟨hQR\', rfl⟩</code> proves <code>Heap.splits (Heap.union hQ hR) hQ hR</code> only because the witness is <i>syntactically</i> <code>Heap.union hQ hR</code>; a propositionally equal but differently written witness leaves <code>rfl</code> failing on two sides that print identically. Choose the witness to make the equation reflexive and put the real work in the <code>?_</code>.<br><br>The other trap is the order of the pair fed to <code>disjoint_union_right.mpr</code>. It wants <code>⟨hP ⊥ hQ, hP ⊥ hR⟩</code>, in the order the halves appear in <code>Heap.union hQ hR</code>, and you are holding two facts about <code>hP</code>, so <code>⟨hPR, hd₂⟩</code> is an easy slip. Lean catches it, but names the <i>first</i> component:<br><br><code>error: Application type mismatch: The argument hPR has type hP.disjoint hR but is expected to have type hP.disjoint hQ</code><br><br>which reads as though <code>hPR</code> were wrong rather than merely in the wrong seat.',
      variants: 'Drop <code>hd₂</code> — keep <code>hPQ = hP ∪ hQ</code> but not <code>hP ⊥ hQ</code> — and the theorem is false. Take <code>hP = 0 ↦ 1</code>, <code>hQ = 0 ↦ 2</code>, <code>hR = Heap.empty</code>. Then <code>hPQ = 0 ↦ 1</code> by the bias, <code>h = 0 ↦ 1</code>, and <code>Heap.splits h hPQ hR</code> holds outright. The conclusion fails: the second component forces <code>hQR = 0 ↦ 2</code>, and then <code>Heap.splits h hP hQR</code> demands that <code>0 ↦ 1</code> and <code>0 ↦ 2</code> be disjoint. So <code>hd₂</code> is load-bearing, and it enters at exactly one place, the <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code>.<br><br>Reversing the statement — from <code>splits h hP hQR</code> and <code>splits hQR hQ hR</code> to a left-bracketed splitting — is the mirror image: swap the roles of the two <code>disjoint_union_*</code> lemmas and use <code>rw [← union_assoc]</code>.'
    },

    /* ================================================================
       6 — the interface, and what cannot yet be said
       ================================================================ */

    { t: 'sec', s: 'Union, from here on' },

    { t: 'p', h: 'Nine laws, and <code>match</code> is finished. If you find yourself unfolding <code>Heap.union</code> in a later chapter, the lemma you are missing is one of the first three rows.' },

    { t: 'tbl',
      head: ['when you need to…', 'reach for'],
      rows: [
        ['evaluate a union where the left heap is undefined', '<code>union_of_none h₂ hl</code>'],
        ['evaluate a union where the left heap is defined', '<code>union_of_some h₂ hl</code>'],
        ['know a union is undefined at a point', '<code>union_eq_none</code>, either direction'],
        ['re-bracket', '<code>union_assoc</code> — no side condition'],
        ['swap two disjoint heaps', '<code>union_comm hd</code>'],
        ['take a disjointness fact apart', '<code>disjoint_union_left.mp</code> / <code>disjoint_union_right.mp</code>'],
        ['build a disjointness fact', '<code>disjoint_union_left.mpr</code> / <code>disjoint_union_right.mpr</code>'],
        ['get a disequality out of a separation', '<code>(singleton_disjoint_iff v₁ v₂).mp</code>'],
        ['flip or re-associate a splitting', '<code>splits_comm</code> / <code>splits_assoc</code>']
      ] },

    { t: 'p', h: 'One consequence of the algebra is the reason separation logic is not Hoare logic with a new symbol, and exercise 2 left it lying about: a heap disjoint from itself is empty.' },

    { t: 'p', h: 'Suppose <code>P</code> pins its heap down — suppose there is exactly one <code>h₀</code> satisfying it, as you would expect of <code>l ↦ v</code>. Then <code>P ∗ P</code> asks for a splitting into two heaps each satisfying <code>P</code>, so both halves are <code>h₀</code>, so <code>h₀</code> is disjoint from itself, so <code>h₀</code> is empty. For a <code>P</code> that owns anything at all, <code>P ∗ P</code> has no model — while <code>P ∧ P</code> is just <code>P</code>. Ownership does not duplicate, and that three-line argument is the whole reason.' },

    { t: 'p', h: 'Not one word of it can currently be written down. It needs an assertion; it needs the phrase “pins its heap down”, which is a property some assertions have and others do not; and it needs “has no model”, which is a relation between assertions. <code>Assertion := Store → Heap → Prop</code> is one line — but two assertions being the same is then an equation between <code>Prop</code>-valued functions, and <code>funext</code> gets you to the propositions and no further. M3 asks what relation between assertions to use instead, and <code>=</code> turns out to be the wrong answer.' },

    { t: 'dod', h: 'Heaps are a partial commutative monoid: nine laws, one of which needs a hypothesis, and none of which will ever be reproved.' }

  ]
});
