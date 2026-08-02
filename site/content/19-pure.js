registerChapter({
  id: 'pure',
  num: '17',
  ledgerForward: ['write_with_frame', 'node_cells_distinct'],
  phase: 'Phase 2 · The logic of ownership',
  title: 'Propositions inside a star, and the toolkit',
  blurb: 'A store proposition owns no memory, so to sit under a separating conjunction it has to say so. That is one definition, one theorem, and the library that every later proof reshapes preconditions with.',

  orient: {
    youWill: [
      'Say why <code>fact φ ∗ P</code> is a weaker sentence than <code>aAnd (fact φ) P</code>, and refute the entailment between them at a one-cell heap.',
      'State the rule that decides which embedding pairs with which connective, and apply it to get <code>pure</code> without guessing.',
      'Prove <code>pure φ ∗ P ⊢ aAnd (fact φ) P</code> and its converse, and say which slot of the tuple pins the cut.',
      'Prove that a two-cell precondition already contains the fact that its two cells are at different addresses, and say why the conclusion is <code>fact</code> and not <code>pure</code>.',
      'Build an entailment out of three earlier entailments and <code>entails_trans</code>, with no <code>intro</code>, no heap and no tuple in it.',
      'Read the error <code>don\'t know how to synthesize implicit argument <b>Q</b></code> as Lean asking you to name the middle of a chain.',
      'Push <code>∗</code> past <code>∨</code> and <code>∃</code> in both directions, and say why the same argument fails for <code>∀</code>.',
      'Take a precondition in whatever shape it arrived in and drive it into the shape the next step wants.'
    ],
    needs: [
      'Unit 12: <code>fact</code>, <code>aAnd</code>, <code>aOr</code>, <code>aExists</code>, <code>entails_trans</code>, <code>and_intro</code>.',
      'Unit 13: <code>emp</code> as an equation on the heap, and <code>subst</code> through a folded definition.',
      'Unit 14: the six-slot <code>⟨…⟩</code>, and <code>no_star_weakening</code> — the star has no projection.',
      'Units 15 and 16: <code>star_comm</code>, <code>star_mono_left</code>, <code>star_assoc_left</code>, <code>star_assoc_right</code>.'
    ],
    payoff: 'Everything after this unit reshapes assertions rather than heaps. <code>pure</code> goes into the <i>definition</i> of a list segment in Unit 33 and appears in six later fragments; <code>two_cells_distinct</code> is the entire proof of Unit 32\'s <code>node_cells_distinct</code>, and is why Unit 27\'s framed write never takes <code>l ≠ other</code> as a hypothesis; and the chain of <code>entails_trans</code> you assemble here is the shape of eleven later entailment steps, in five proofs.'
  },

  blocks: [

    /* ============================================ the obvious embedding === */

    {t:'p', h:'Attach the proposition the obvious way and read what you get. The only embedding of a store proposition in hand is <code>fact</code>, so write <code>fact φ ∗ P</code> and unfold it.'},

    {t:'code', cap:'Unit 12\'s embedding, unchanged. The underscore is the heap argument, discarded.',
     src:'def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ'},

    {t:'p', h:'At a store <code>σ</code> and a heap <code>h</code>, the definition of <code>∗</code> asks for a cut: two disjoint heaps whose union is <code>h</code>, the left one satisfying <code>fact φ</code> and the right one satisfying <code>P</code>. Write the four conditions out and look at the third.'},

    {t:'txt', cap:'<code>(fact φ ∗ P) σ h</code>, unfolded. The third condition does not mention <code>h₁</code>.',
     src:'  ∃ h₁ h₂,   Heap.disjoint h₁ h₂\n           ∧  h = Heap.union h₁ h₂\n           ∧  φ σ                        ←  fact φ σ h₁, with h₁ gone\n           ∧  P σ h₂'},

    {t:'p', h:'So <code>h₁</code> is unconstrained. Any sub-heap of <code>h</code> at all can be handed to the left conjunct and it will be accepted. The sentence the whole formula makes is <i>φ holds, and <b>some</b> piece of <code>h</code> satisfies <code>P</code></i> — not <i><code>h</code> satisfies <code>P</code></i>. The rest of the heap has been given away to a conjunct that takes anything.'},

    {t:'p', h:'That is <code>no_star_weakening</code> arriving from the other side. A star cannot forget one of its conjuncts: the cells the forgotten conjunct owned are still in the heap, and an exact assertion will not accept them. What a star <i>can</i> contain is a conjunct that volunteers to absorb whatever it is given — and then the forgetting happens inside the star, where no theorem is protecting you. Refuting the entailment takes one cell.'},

    {t:'code', tag:'illustration', cap:'<code>P</code> is <code>emp</code> and the heap holds one cell. Compiled against this unit\'s context.',
     src:'theorem factStar_not_and : ¬ ((fact (fun _ => True)) ∗ emp ⊢ aAnd (fact (fun _ => True)) emp) := by\n  intro hbad\n  have h := hbad (fun _ => 0) (Heap.singleton 0 4)\n    ⟨Heap.singleton 0 4, Heap.empty, disjoint_empty_right _,\n      (union_empty_right _).symm, trivial, rfl⟩\n  have h0 := congrFun h.2 0\n  rw [singleton_same] at h0\n  exact absurd h0 (by simp [Heap.empty])'},

    {t:'p', h:'The witness is the heap <code>Heap.singleton 0 4</code> and the cut is <code>(Heap.singleton 0 4, Heap.empty)</code>. <code>fact</code> accepts the cell without looking at it and <code>emp</code> accepts the empty half, so the left-hand side holds. The right-hand side says the heap is <code>Heap.empty</code>, and it is not: at address <code>0</code> it is <code>some 4</code>.'},

    {t:'p', h:'The other direction does hold, and it buys nothing: put <code>Heap.empty</code> on the left of the cut and <code>fact</code> is satisfied there as well as anywhere. So <code>fact φ ∗ P</code> is strictly weaker than <code>aAnd (fact φ) P</code>, and what the star lost is the only thing <code>P</code> was claiming — which heap it holds at.'},

    {t:'code', tag:'illustration', cap:'True, and useless — the cut is chosen for you and tells you nothing.',
     src:'theorem factStar_from_and (φ : Store → Prop) (P : Assertion) :\n    aAnd (fact φ) P ⊢ fact φ ∗ P := by\n  intro σ h ⟨hφ, hp⟩\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, hφ, hp⟩'},

    /* =================================== what an embedding has to match === */

    {t:'sec', s:'What an embedding has to match'},

    {t:'p', h:'The failure names its own cause. <code>aAnd</code> hands both conjuncts the same whole heap, so what one conjunct claims about it costs the other nothing; an embedding that claims nothing at all therefore fits <code>aAnd</code> exactly, and that is <code>fact</code>. <code>∗</code> hands each conjunct a <i>share</i> and holds it to whatever it claims about that share. A conjunct that claims nothing lets its share be anything, and then the cut is not pinned and the star has stopped separating.'},

    {t:'p', h:'So the embedding that goes under <code>∗</code> has to name a share. A proposition about the store owns no memory, and the share it can honestly claim is the empty one. The definition is that sentence, written down.'},

    {t:'code', cap:'The <code>∗</code>-compatible embedding: <code>φ</code> holds, and I own nothing.',
     src:'def pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp'},

    {t:'p', h:'Both halves of the definition are already in the course, and nothing new is unfolded to work with it: <code>pure φ ⊢ fact φ</code> is <code>and_left (fact φ) emp</code> and <code>pure φ ⊢ emp</code> is <code>and_right (fact φ) emp</code>, each a term you can write without opening anything.'},

    {t:'txt', cap:'An embedding must match the resource discipline of the connective it will sit under.',
     src:'  connective     what it hands a conjunct     the embedding that fits\n  ──────────────────────────────────────────────────────────────────────\n  aAnd P Q       the WHOLE heap, to both       fact φ\n                                               "φ holds." Nothing about h.\n\n  P ∗ Q          a SHARE of the heap, to each  pure φ\n                                               "φ holds, and my share\n                                                is empty."'},

    {t:'note', kind:'warn', title:'Lean already has a <code>pure</code>', h:'Lean\'s own library has a <code>pure</code> — the one that belongs to monads, which this course never uses. Yours wins wherever the types decide it, and every statement on this page is accepted without help. What changes is the <b>display</b>: from here on the goal window writes yours as <code>_root_.pure</code>, with the leading path that says <i>the one at the top level, not the library\'s</i>. It is output, not something you type.'},

    {t:'detail', title:'The other spelling, and what <code>@pure</code> does', open:false, blocks:[
      {t:'p', h:'The obvious alternative is to write the predicate out instead of building it from <code>fact</code> and <code>emp</code>.'},
      {t:'code', tag:'illustration', cap:'The same predicate, spelled directly.',
       src:'def pureRaw (φ : Store → Prop) : Assertion := fun σ h => φ σ ∧ h = Heap.empty\n\ntheorem pureRaw_agrees (φ : Store → Prop) : pure φ ⊣⊢ pureRaw φ :=\n  ⟨fun _ _ hp => hp, fun _ _ hp => hp⟩'},
      {t:'p', h:'The proof is the identity function in both directions, which is the strongest statement of agreement available: the two definitions are the same predicate, not two predicates that happen to agree. What differs is the vocabulary that applies to them. <code>pure</code> is an <code>aAnd</code>, so <code>and_left</code>, <code>and_right</code> and <code>and_intro</code> reach it by name; <code>pureRaw</code> is a new primitive, and every one of those facts has to be reproved for it. Building new assertions out of old ones so the old laws still fire is the discipline; it is the same reason <code>Heap.write</code> was never unfolded after Unit 05.'},
      {t:'p', h:'The name clash does bite in one place. Asking for the constant on its own gives two candidates and no way to choose:'},
      {t:'state', cap:'<code>#check @pure</code>. The second interpretation is Lean\'s monadic <code>pure</code>; the first is this unit\'s.',
       src:'error: Ambiguous term\n  @pure\nPossible interpretations:\n  _root_.pure : (Store → Prop) → Assertion\n  \n  @Pure.pure : {f : Type ?u.2 → Type ?u.1} → [self : Pure f] → {α : Type ?u.2} → α → f α'},
      {t:'p', h:'Applying it to an argument, which is what every real use does, resolves immediately — <code>#check pure (fun σ => σ 0 = 7)</code> answers <code>_root_.pure fun σ => σ 0 = 7 : Assertion</code>. Only the bare constant is ambiguous, and the cure is to write <code>_root_.pure</code>.'}
    ]},

    /* ================================== pure φ ∗ P is aAnd (fact φ) P === */

    {t:'sec', s:'The formal content of the slogan'},

    {t:'p', h:'"<code>φ</code>, and I own nothing" should mean that putting <code>pure φ</code> beside <code>P</code> under a star leaves <code>P</code> owning everything it owned before, with <code>φ</code> along for the ride. That is an equivalence, and it is two theorems.'},

    {t:'code', tag:'sketch', cap:'Statements only; each is followed in the corpus by its proof.',
     src:'theorem star_pure_left (φ : Store → Prop) (P : Assertion) :\n    pure φ ∗ P ⊢ aAnd (fact φ) P := by\n\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) :\n    aAnd (fact φ) P ⊢ pure φ ∗ P := by'},

    {t:'p', h:'Left to right, there is no cut to choose: the star hands you one, and the <code>emp</code> inside <code>pure φ</code> forces the left piece to be <code>Heap.empty</code>, so the right piece is the whole heap.'},

    {t:'trace', title:'<code>star_pure_left</code>, tactic by tactic',
     start:'φ : Store → Prop\nP : Assertion\n⊢ _root_.pure φ ∗ P ⊢ aAnd (fact φ) P',
     steps:[
       {tac:'intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩',
        state:'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhφ : fact φ σ h₁\nhe : emp σ h₁\nhp : P σ h₂\n⊢ aAnd (fact φ) P σ h',
        h:'Slot five of the six-slot pattern is <code>pure φ σ h₁</code>, and <code>pure</code> is an <code>aAnd</code>, so it takes a two-name pattern of its own. Disjointness is the only thing neither proof needs; the underscore in slot three is why the context shows <code>left✝</code>.'},
       {tac:'subst he',
        state:'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₂ : Heap\nhp : P σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhφ : fact φ σ Heap.empty\n⊢ aAnd (fact φ) P σ h',
        h:'<code>he : emp σ h₁</code> is the equation <code>h₁ = Heap.empty</code>, so <code>h₁</code> disappears from the whole context. This is the step that pins the cut: <code>hu</code> now reads <code>h = Heap.empty.union h₂</code>.'},
       {tac:'rw [hu, union_empty_left]',
        state:'φ : Store → Prop\nP : Assertion\nσ : Store\nh h₂ : Heap\nhp : P σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhφ : fact φ σ Heap.empty\n⊢ aAnd (fact φ) P σ h₂',
        h:'The rewrite lands in the <b>goal</b>, not in a hypothesis: the heap the goal is evaluated at changes from <code>h</code> to <code>h₂</code>. Nothing about the assertions moved.'},
       {tac:'exact ⟨hφ, hp⟩',
        state:'No goals.',
        h:'Both conjuncts are now at <code>h₂</code>. <code>hφ</code> is at <code>Heap.empty</code> rather than <code>h₂</code>, and that is fine: <code>fact</code> discards its heap argument, so the two are the same proposition.'}
     ]},

    {t:'p', h:'Right to left there is a cut to choose and exactly one choice works, for the same reason: the left piece must satisfy <code>emp</code>. Choose <code>(Heap.empty, h)</code>, and of the four slots that remain, two are the empty-heap laws — <code>Heap.empty</code> is disjoint from anything, and unioning it on the left changes nothing — and two are the facts you were handed, with an <code>rfl</code> beside one of them for the <code>emp</code>.'},

    /* ============================== ownership implies non-aliasing === */

    {t:'sec', s:'Ownership implies non-aliasing'},

    {t:'p', h:'Unit 08 proved <code>singleton_disjoint_iff</code>: two one-cell heaps are disjoint exactly when their addresses differ. Unit 14 put disjointness inside the definition of the conjunction. Put those together and something follows that no program has to be told: a precondition that owns two cells <b>already contains</b> the fact that they are at different addresses.'},

    {t:'code', tag:'sketch', cap:'The statement. Its proof is the exercise below.',
     src:'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by'},

    {t:'p', h:'The conclusion is <code>fact</code> and not <code>pure</code>, and the difference is the subject of this unit. Both would be legitimate places to <i>put</i> a store proposition; only one of them is true here. <code>pure (fun _ => l₁ ≠ l₂)</code> does not say "nothing about the heap" — it says the heap is empty, and this heap holds two cells.'},

    {t:'code', tag:'illustration', cap:'Strengthening the conclusion to <code>pure</code> makes the theorem false, at the two-cell heap the premise describes.',
     src:'theorem two_cells_not_pure : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ pure (fun _ => (0 : Loc) ≠ 1)) := by\n  intro hbad\n  have h := hbad (fun _ => 0) (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7))\n    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩\n  have h0 := congrFun h.2 0\n  rw [union_of_some (Heap.singleton 1 7) (singleton_same 0 4)] at h0\n  exact absurd h0 (by simp [Heap.empty])'},

    {t:'p', h:'An entailment is free to conclude less than its premise knows, so <code>two_cells_distinct</code> throws the two cells away. At a call site you want the fact <i>and</i> the cells, which is what <code>and_intro</code> is for — it runs the same premise into two conclusions and keeps both.'},

    {t:'code', tag:'illustration', cap:'The form you actually spend: the non-aliasing fact, with the resources still in hand.',
     src:'theorem two_cells_and_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ aAnd ((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) (fact (fun _ => l₁ ≠ l₂)) :=\n  and_intro (entails_refl _) (two_cells_distinct l₁ l₂ v₁ v₂)'},

    /* ------------------------------------------------------------ m4-7 --- */

    {t:'ex',
     id: 'm4-7',
     name: 'two_cells_distinct',
     why: 'This is what the star was for. Unit 00 opened on a swap routine that is wrong when its two arguments are the same address, and the classical repair was to carry <code>l₁ ≠ l₂</code> as a side condition in every specification that touches two cells. Here the side condition is a <b>theorem</b> about the precondition, so it never has to be assumed. Two later theorems you cannot read yet are where that is spent: Unit 27\'s <code>write_with_frame</code>, which never takes <code>l ≠ other</code> as a hypothesis, and Unit 32\'s <code>node_cells_distinct</code>, which is this theorem applied to a two-field record and has no proof of its own.',
     setup: 'Three lines. Everything you need is Unit 14\'s consumption move and Unit 08\'s <code>singleton_disjoint_iff</code>, whose <code>.mp</code> direction turns disjointness of two singletons into distinctness of their addresses.',
     goal: 'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by',
     hints: [
       'The goal says: for every store <code>σ</code> and heap <code>h</code>, if <code>h</code> splits into two disjoint pieces with <code>l₁ ↦ v₁</code> at one and <code>l₂ ↦ v₂</code> at the other, then <code>l₁ ≠ l₂</code>. The conclusion is a <code>fact</code>, so the heap plays no part in it — <code>fact (fun _ => l₁ ≠ l₂) σ h</code> <i>is</i> <code>l₁ ≠ l₂</code>.',
       'The two pieces are disjoint. Each of them is a one-cell heap, because that is what <code>↦</code> asserts. Two one-cell heaps are disjoint exactly when their addresses differ, and that is a theorem you already have. The whole argument is: turn the two ownership facts into the identities of the two heaps, then apply that theorem to the disjointness fact.',
       'One <code>intro</code> with the six-name pattern, two <code>subst</code>s, one <code>exact</code>. The theorem at the end is <code>singleton_disjoint_iff</code>, in its <code>.mp</code> direction.',
       'Start <code>intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩</code> — this time the union equation is the slot nobody needs, so the underscore moves to slot four. That leaves <code>hd : h₁.disjoint h₂</code>, <code>hp : (l₁ ↦ v₁) σ h₁</code>, <code>hq : (l₂ ↦ v₂) σ h₂</code> and the goal <code>fact (fun x => l₁ ≠ l₂) σ h</code>. The next line rewrites <code>hd</code> into a statement about two singletons.'
     ],
     sol: 'theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂) := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩\n  subst hp; subst hq\n  exact (singleton_disjoint_iff v₁ v₂).mp hd',
     solNote: 'The same three lines are the whole of Unit 14\'s <code>star_same_loc_absurd</code> with a <code>rfl</code> on the end. There the two addresses were equal by assumption and the disjointness fact was the contradiction; here they are arbitrary and the disjointness fact is the conclusion. One theorem, read forwards and backwards.',
     expl: 'The proof never mentions <code>fact</code>, because <code>fact φ σ h</code> unfolds to <code>φ σ</code> and the goal is therefore already <code>l₁ ≠ l₂</code> as far as <code>exact</code> is concerned. What it does is convert the disjointness hypothesis, which is about two anonymous heaps, into a disjointness hypothesis about two singletons — and that conversion is the two <code>subst</code>s.',
     walk: [
       {tac:'intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩', h:'Three binders out of the entailment, then the star opened into six. The underscore is the union equation: the address of a cell does not depend on how the pieces were glued, so the proof never looks at it.'},
       {tac:'subst hp; subst hq', h:'<code>hp : (l₁ ↦ v₁) σ h₁</code> is definitionally the equation <code>h₁ = Heap.singleton l₁ v₁</code>, so <code>subst</code> takes it as one and erases <code>h₁</code> from the context. The effect that matters is on <code>hd</code>, which changes from <code>h₁.disjoint h₂</code> to <code>(Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)</code> — the exact shape <code>singleton_disjoint_iff</code> is stated at.'},
       {tac:'exact (singleton_disjoint_iff v₁ v₂).mp hd', h:'The biconditional applied to the rewritten hypothesis. The two values are explicit arguments and the two locations are implicit, which is why <code>v₁</code> and <code>v₂</code> are written and <code>l₁</code>, <code>l₂</code> are not.'}
     ],
     deep: [
       {t:'trace', title:'The two <code>subst</code>s are the whole proof',
        start:'l₁ l₂ : Loc\nv₁ v₂ : Val\n⊢ l₁ ↦ v₁ ∗ l₂ ↦ v₂ ⊢ fact fun x => l₁ ≠ l₂',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩',
           state:'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nleft✝ : h = h₁.union h₂\nhp : (l₁ ↦ v₁) σ h₁\nhq : (l₂ ↦ v₂) σ h₂\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
           h:'<code>hd</code> is about two heaps nothing is known about. In this form <code>singleton_disjoint_iff</code> does not apply to it.'},
          {tac:'subst hp; subst hq',
           state:'l₁ l₂ : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nleft✝ : h = (Heap.singleton l₁ v₁).union (Heap.singleton l₂ v₂)\n⊢ fact (fun x => l₁ ≠ l₂) σ h',
           h:'Two heap variables gone, and <code>hd</code> now matches the statement of the theorem that finishes the proof.'},
          {tac:'exact (singleton_disjoint_iff v₁ v₂).mp hd',
           state:'No goals.',
           h:'<code>.mp</code> applied to <code>hd</code> has type <code>l₁ ≠ l₂</code>, and the goal is <code>fact (fun x => l₁ ≠ l₂) σ h</code>. Those are the same proposition after unfolding <code>fact</code>, which <code>exact</code> does silently; the <code>σ</code> and the <code>h</code> in the goal are discarded by that unfolding.'}
        ]},
       {t:'p', h:'The goal in the opening line prints as <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂ ⊢ fact fun x => l₁ ≠ l₂</code>. Two turnstiles, no brackets around either side of the star, and the binder Lean invented for the discarded store argument is called <code>x</code> although you wrote <code>_</code>.'}
     ],
     pitfall: 'Reaching for <code>singleton_disjoint_iff</code> before the two <code>subst</code>s. It looks as if it should work, because <code>hp</code> and <code>hq</code> are sitting right there, but what Lean checks is that the argument\'s type is the type the function wants, and no rewriting happens on its own:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;hd<br>has type<br>&nbsp;&nbsp;h₁.disjoint h₂<br>but is expected to have type<br>&nbsp;&nbsp;(Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)</code><br><br>The message is telling you precisely which two rewrites are missing.',
     variants: 'Drop the disjointness conjunct from <code>∗</code> and the theorem dies immediately: <code>starNoDisj</code> from Unit 14 lets the same heap satisfy <code>(0 ↦ 4)</code> and <code>(0 ↦ 7)</code> at once, and nothing then says the addresses differ. Disjointness is not bookkeeping here; it is the entire content of the theorem, as it was in Unit 14\'s <code>star_same_loc_absurd</code> and <code>no_star_duplication</code>.<br><br>Strengthen the conclusion from <code>fact</code> to <code>pure</code> and it becomes false, refuted above at the two-cell heap. Weaken it in the other direction — conjoin the premise back on with <code>and_intro</code> — and it stays true and becomes usable, which is <code>two_cells_and_distinct</code>.<br><br>Replace <code>↦</code> by the loose reading Unit 07 rejected and the theorem <b>survives</b>: it needs disjointness of the two pieces and nothing else, and a heap that contains <code>l₁</code> and a disjoint heap that contains <code>l₂</code> still force <code>l₁ ≠ l₂</code>. Exactness is not what this theorem turns on. What does change is the proof. <code>ptsAtLeast l v σ h</code> is <code>h l = some v</code>, not an equation between heaps, so there is nothing to <code>subst</code> and <code>singleton_disjoint_iff</code> never applies. You assume <code>l₁ = l₂</code>, case on <code>hd l₁</code> — which says one of the two pieces is empty at that address — and contradict whichever ownership fact it names. Five lines instead of three, and disjointness is still the only hypothesis spent.'
    },

    /* ================================================ composition === */

    {t:'sec', s:'Proof by composition'},

    {t:'p', h:'The next thing you will constantly want is to move one conjunct of a star to the front, past another. Call it <code>star_swap_middle</code>: from <code>P ∗ (Q ∗ R)</code> to <code>Q ∗ (P ∗ R)</code>. There is no law that does it. <code>star_comm</code> exchanges the two immediate sides of one star, and the two immediate sides of <code>P ∗ (Q ∗ R)</code> are <code>P</code> and <code>Q ∗ R</code> — <code>Q</code> is not one of them.'},

    {t:'p', h:'Re-bracket first, so that <code>P</code> and <code>Q</code> become siblings; swap them; re-bracket back. Two shapes between the start and the finish, and each of the three moves that produce them is a law you have proved.'},

    {t:'txt', cap:'Four shapes, three moves. Nothing about heaps appears anywhere in this diagram, and nothing will appear in the proof.',
     src:'      P ∗ (Q ∗ R)\n          │   star_assoc_right P Q R        move the bracket left\n      (P ∗ Q) ∗ R\n          │   star_mono_left R (star_comm P Q)\n      (Q ∗ P) ∗ R                            exchanged, under the ∗ R\n          │   star_assoc_left Q P R          move the bracket back\n      Q ∗ (P ∗ R)'},

    {t:'p', h:'The middle move is the one worth naming. <code>star_comm P Q</code> is an entailment between <code>P ∗ Q</code> and <code>Q ∗ P</code>, and what needs improving is not the whole assertion but its left conjunct. <code>star_mono_left R</code> is the lemma that takes an entailment and runs it underneath a <code>∗ R</code>; that is what monotonicity was for.'},

    {t:'p', h:'Three entailments in a row are glued by <code>entails_trans</code>, which takes two entailments whose middle assertion agrees. Ask Lean to find that middle for you and it declines, in a message worth reading carefully.'},

    {t:'code', tag:'sketch', cap:'Two holes and no information about what goes between them.',
     src:'example (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) := by\n  refine entails_trans ?_ ?_'},

    {t:'state', cap:'The first of the two errors that line reports; the second is <code>unsolved goals</code>, because nothing got proved. The last line here is the interesting one.',
     src:'error: don\'t know how to synthesize implicit argument `Q`\n  @entails_trans (P ∗ Q ∗ R) ?m.3 (Q ∗ P ∗ R) ?m.5 ?m.6\ncontext:\nP Q R : Assertion\n⊢ Assertion'},

    {t:'p', h:'The <code>Q</code> in the first line is <code>entails_trans</code>\'s own middle binder, not the <code>Q</code> of your theorem; the two names collide by accident. The last line is Lean stating, as a goal, that what is missing is <i>an assertion</i>. Any assertion at all would typecheck, so nothing determines it and nothing can guess it. Choosing the middle is the proof, and the way to choose it is to write the first component down.'},

    {t:'trace', title:'Hand over one component and the rest is determined',
     start:'P Q R : Assertion\n⊢ P ∗ Q ∗ R ⊢ Q ∗ P ∗ R',
     steps:[
       {tac:'refine entails_trans (star_assoc_right P Q R) ?_',
        state:'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ Q ∗ P ∗ R',
        h:'The first component fixes the middle at <code>(P ∗ Q) ∗ R</code>, and the hole is now the rest of the journey, stated as an entailment you can read off the diagram. Two more steps of the same kind close it, and the corpus writes the whole thing as one term rather than three tactic lines.'}
     ]},

    {t:'note', kind:'key', title:'The rule for this section', h:'If you find yourself typing <code>intro σ h ⟨…⟩</code> for <code>star_swap_middle</code> or for either rotation, stop. All three are rearrangements of a star, every rearrangement of a star is already a theorem, and a proof that goes down to the heaps is throwing that away.'},

    {t:'p', h:'The rule is not aesthetic. <code>star_swap_middle</code> can be proved semantically, and it costs seven lines that name four heaps, construct a fifth, and spend four heap lemmas in six applications — <code>disjoint_union_right</code> twice, <code>disjoint_symm</code>, <code>union_assoc</code> twice and <code>union_comm</code>. Every one of those is a place to get an argument backwards. The composed proof spends three lemmas, names no heap, and is checked by matching four assertion shapes against each other.'},

    {t:'p', h:'Two of the toolkit\'s entries are the associativity theorems under a second name. <code>star_assoc_left</code> and <code>star_assoc_right</code> are named for the bracketing you <b>start</b> from; <code>star_rotate_left</code> and <code>star_rotate_right</code> are named for the direction the bracket <b>moves</b>. Mechanically nothing is gained — each is defined to be the other. What is gained is that in a chain of four <code>entails_trans</code>es you can read the motion off the names instead of unfolding each statement to see which way it went.'},

    /* ------------------------------------------------------------ m4-8 --- */

    {t:'ex',
     id: 'm4-8',
     name: 'star_pure_left / star_pure_right / star_swap_middle / star_rotate_left / star_rotate_right',
     why: 'Five theorems, and the skill is one skill: build an entailment out of entailments instead of out of heaps. The accounting first, because it decides how to read the rest — <b>none of these five is cited by name in any later proof.</b> What is cited constantly is their <i>shape</i>. The inductive step of each of Unit 33\'s two list theorems is a chain of <code>refine entails_trans … ?_</code>, and across the units after this one there are eleven such steps, spread over five proofs and built out of <code>star_assoc_left</code>, <code>star_mono_left</code>, <code>star_mono_right</code>, <code>star_exists_left</code> and <code>star_comm</code>. <code>star_swap_middle</code> is that shape at its smallest and with the destination already known, which is why it is the one you assemble by hand. The two <code>pure</code> laws earn their place differently: <code>pure</code> itself occurs in six later fragments — Unit 33 puts it inside the <i>definition</i> of a list segment — and these two theorems are what license doing that, by saying that a proposition under a star costs no resources.',
     setup: 'The first three are terms with no tactic anywhere in them. <code>star_pure_left</code> is worked in full above; <code>star_pure_right</code> is its converse, and needs the one cut that works. Available: <code>entails_trans</code>, <code>star_comm</code>, <code>star_mono_left</code>, <code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>disjoint_empty_left</code>, <code>union_empty_left</code>.',
     goal: 'theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=\n  sorry\n\ntheorem star_rotate_left (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=\n  sorry\n\ntheorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) :=\n  sorry\n\ntheorem star_pure_left (φ : Store → Prop) (P : Assertion) :\n    pure φ ∗ P ⊢ aAnd (fact φ) P := by\n  sorry\n\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) :\n    aAnd (fact φ) P ⊢ pure φ ∗ P := by',
     hints: [
       'Five statements; read each as a sentence before planning anything. <code>star_swap_middle</code>: if a heap splits into a piece satisfying <code>P</code> and a piece that itself splits for <code>Q</code> and <code>R</code>, then it also splits into a piece satisfying <code>Q</code> and a piece that splits for <code>P</code> and <code>R</code>. The two rotations say that a three-way split can be reported with the bracket on either side, one for each direction. <code>star_pure_left</code>: if <code>h</code> splits with <code>pure φ</code> on the left, then <code>φ</code> holds and <code>P</code> holds at <b>all</b> of <code>h</code> — the qualifier is the content, since the premise only gave you <code>P</code> at a share. <code>star_pure_right</code> is that read backwards: given <code>φ</code> and <code>P</code> at <code>h</code>, produce a splitting of <code>h</code>.',
       'For <code>star_swap_middle</code>: re-bracket so that <code>P</code> and <code>Q</code> sit under the same star, exchange them there, re-bracket back — the diagram above is that plan. The exchange happens inside a larger assertion, so it has to be carried in by monotonicity rather than applied to the whole thing. For the two rotations, do not plan at all: set each statement beside the two associativity laws and compare them character by character. For <code>star_pure_right</code>: there is only one heap that satisfies <code>emp</code>, so there is only one cut available, and the union law that says it is a legitimate cut is the one for the empty heap on the left.',
       '<code>entails_trans</code>, twice, nested, is the whole of <code>star_swap_middle</code>; its three components are <code>star_assoc_right</code>, <code>star_comm</code> carried in by <code>star_mono_left</code> with <code>R</code> as its explicit first argument, and <code>star_assoc_left</code>. Each rotation is one of <code>star_assoc_left</code> and <code>star_assoc_right</code> applied at <code>P Q R</code> — no <code>by</code>, no tactic, nothing else in the proof — and which of the two it is, is decided by matching the premise. <code>star_pure_right</code> is a single <code>intro</code> with a two-name pattern followed by a single six-slot <code>exact</code>, whose third and fourth entries are <code>disjoint_empty_left</code> and <code>union_empty_left</code>.',
       'The outer step of <code>star_swap_middle</code> is <code>entails_trans (star_assoc_right P Q R) ?</code>, which leaves <code>(P ∗ Q) ∗ R ⊢ Q ∗ (P ∗ R)</code>; that hole is a second <code>entails_trans</code> whose first component is <code>star_mono_left R (star_comm P Q)</code>. <code>star_rotate_left</code> is <code>star_assoc_right P Q R</code> — its premise is <code>P ∗ (Q ∗ R)</code>, which is what fixes the choice — and <code>star_rotate_right</code> is the other associativity theorem at the same three arguments. For <code>star_pure_right</code>, after <code>intro σ h ⟨hφ, hp⟩</code> the tuple begins <code>⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, …⟩</code> and its fifth entry is itself a pair, because <code>pure</code> is an <code>aAnd</code>.'
     ],
     sol: 'theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=\n  entails_trans (star_assoc_right P Q R)\n    (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))\n\ntheorem star_rotate_left (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R :=\n  star_assoc_right P Q R\n\ntheorem star_rotate_right (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) :=\n  star_assoc_left P Q R\n\ntheorem star_pure_left (φ : Store → Prop) (P : Assertion) :\n    pure φ ∗ P ⊢ aAnd (fact φ) P := by\n  intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩\n  subst he\n  rw [hu, union_empty_left]\n  exact ⟨hφ, hp⟩\n\ntheorem star_pure_right (φ : Store → Prop) (P : Assertion) :\n    aAnd (fact φ) P ⊢ pure φ ∗ P := by\n  intro σ h ⟨hφ, hp⟩\n  exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩',
     solNote: 'If you climbed all four rungs on <code>star_swap_middle</code> and are still turning the nesting inside out, open this and read the term from the outside in: the outermost <code>entails_trans</code> is the first move of the diagram, and everything after it is the rest of the journey.',
     expl: 'Three of the five contain no tactic and no heap. <code>star_swap_middle</code> is the diagram transcribed: outermost application is the first move, and the second argument of each <code>entails_trans</code> is whatever is left to do. The two rotations are aliases with a name that describes motion. Only <code>star_pure_left</code> and <code>star_pure_right</code> go down to the definition of <code>∗</code>, and they have to, because they are what connects the new definition to everything else — after them, <code>pure</code> can be handled algebraically like anything else.',
     walk: [
       {tac:'entails_trans (star_assoc_right P Q R) …', h:'Fixes the middle of the chain at <code>(P ∗ Q) ∗ R</code>, and so turns the goal into "get from there to <code>Q ∗ (P ∗ R)</code>". Written first because it is the outermost application, and everything inside it is read against the middle it has just fixed.'},
       {tac:'entails_trans (star_mono_left R (star_comm P Q)) …', h:'Fixes the second middle at <code>(Q ∗ P) ∗ R</code>. <code>star_comm P Q</code> alone would be an entailment about <code>P ∗ Q</code>, which is not the assertion in hand; <code>star_mono_left R</code> is what pushes it under the outer star.'},
       {tac:'star_assoc_left Q P R', h:'Closes the chain by moving the bracket back, at the arguments <code>Q P R</code> rather than <code>P Q R</code> — the letters have been permuted by the swap, and passing them in the old order is a type mismatch Lean reports at once.'},
       {tac:':= star_assoc_right P Q R', h:'The whole of <code>star_rotate_left</code>. Nothing happens. The statement of <code>star_rotate_left</code> and the statement of <code>star_assoc_right</code> are the same proposition, so the proof of one is the proof of the other, and the second name exists to be read.'},
       {tac:':= star_assoc_left P Q R', h:'The whole of <code>star_rotate_right</code>, the other alias. Worth pausing on the arguments: they are <code>P Q R</code>, in the order the theorem bound them, because nothing in this proof has moved anything. Contrast the last component of <code>star_swap_middle</code>, which is <code>star_assoc_left Q P R</code> — there the swap had already exchanged two of the three, and passing <code>P Q R</code> out of habit is the mismatch Lean reports.'},
       {tac:'intro σ h ⟨h₁, h₂, _, hu, ⟨hφ, he⟩, hp⟩', h:'Opens the star into six and slot five into two more, because <code>pure φ</code> is an <code>aAnd</code>. The disjointness fact is discarded: this proof does not care that the pieces do not overlap, only that one of them is empty.'},
       {tac:'subst he', h:'Erases <code>h₁</code> in favour of <code>Heap.empty</code>. This is the step where "I own nothing" turns from an assertion into an equation the rest of the proof can compute with.'},
       {tac:'rw [hu, union_empty_left]', h:'Changes the heap the goal is evaluated at, from <code>h</code> to <code>Heap.empty.union h₂</code> and then to <code>h₂</code>. The two rewrites must be in that order: <code>union_empty_left</code> has nothing to fire on until <code>hu</code> has put a union into the goal.'},
       {tac:'exact ⟨hφ, hp⟩', h:'Builds the <code>aAnd</code>. <code>hφ</code> is stated at <code>Heap.empty</code> and the goal wants it at <code>h₂</code>; they are the same proposition because <code>fact</code> throws its heap away.'},
       {tac:'exact ⟨Heap.empty, h, disjoint_empty_left h, (union_empty_left h).symm, ⟨hφ, rfl⟩, hp⟩', h:'The converse, in one tuple. Slots one and two are the only cut available. Slot four needs <code>h = Heap.empty.union h</code> while <code>union_empty_left</code> states <code>Heap.empty.union h = h</code>, hence <code>.symm</code>. Slot five is a nested pair whose second entry is <code>rfl</code>, proving <code>emp σ Heap.empty</code>.'}
     ],
     deep: [
       {t:'trace', title:'<code>star_swap_middle</code>, staged as tactics so the middles are visible',
        start:'P Q R : Assertion\n⊢ P ∗ Q ∗ R ⊢ Q ∗ P ∗ R',
        steps:[
          {tac:'refine entails_trans (star_assoc_right P Q R) ?_',
           state:'P Q R : Assertion\n⊢ (P ∗ Q) ∗ R ⊢ Q ∗ P ∗ R',
           h:'First move made; what remains is the last two rows of the diagram.'},
          {tac:'refine entails_trans (star_mono_left R (star_comm P Q)) ?_',
           state:'P Q R : Assertion\n⊢ (Q ∗ P) ∗ R ⊢ Q ∗ P ∗ R',
           h:'<code>P</code> and <code>Q</code> have exchanged places under the outer star. The goal now reads "left-bracketed entails right-bracketed", which is <code>star_assoc_left</code> exactly.'},
          {tac:'exact star_assoc_left Q P R', state:'No goals.', h:'The term proof in the corpus is these three components nested, with <code>refine … ?_</code> replaced by ordinary application.'}
        ]},
       {t:'p', h:'The tactic staging and the term are the same proof; the staging exists so that the two intermediate assertions, which the term never names, can be looked at. Written as a term, the middles are inferred from the components — which is why supplying a component in the wrong order produces a message about a type rather than about a strategy.'},
       {t:'cmp',
        left: {t:'The middle move', kind:'good', h:'Type: <code>(P ∗ Q) ∗ R ⊢ (Q ∗ P) ∗ R</code>. The fixed conjunct <code>R</code> stays on the right and <code>star_comm</code> fires on the left one, which is the assertion the chain has in hand.', src:'star_mono_left R (star_comm P Q)', tag:'sketch'},
        right:{t:'The same components, wrong lemma', kind:'bad', h:'Type: <code>R ∗ P ∗ Q ⊢ R ∗ Q ∗ P</code>. Well-typed, and about a different assertion — <code>R</code> has become the <i>left</i> conjunct and the star being commuted is now the right one.', src:'star_mono_right R (star_comm P Q)', tag:'sketch'}},
       {t:'p', h:'Both are well-typed terms; only one of them is about the assertion in your hand. <code>star_mono_left</code> takes the frame that stays fixed as its explicit argument and improves the <b>left</b> conjunct; <code>star_mono_right</code> takes the fixed part first as well, but improves the <b>right</b> one. Getting them the wrong way round does not fail where you wrote it — it fails where the chain is glued.'},
       {t:'state', cap:'<code>star_pure_right</code> after its <code>intro</code>. Two hypotheses, both at the whole of <code>h</code>, and a goal that wants a splitting.',
        src:'φ : Store → Prop\nP : Assertion\nσ : Store\nh : Heap\nhφ : fact φ σ h\nhp : P σ h\n⊢ (_root_.pure φ ∗ P) σ h'},
       {t:'p', h:'Nothing in that context is a heap other than <code>h</code> itself, so the two heaps the goal asks for have to be manufactured, and <code>Heap.empty</code> is the only other one in the language. That is the whole search: the cut is <code>(Heap.empty, h)</code> because there is nothing else to try, and it works because <code>emp</code> is satisfied on the left exactly there.'}
     ],
     pitfall: 'Writing <code>star_mono_right R (star_comm P Q)</code> for the middle move. It type-checks perfectly well, into an entailment between <code>R ∗ (P ∗ Q)</code> and <code>R ∗ (Q ∗ P)</code>, and the complaint arrives one level out where <code>entails_trans</code> tries to glue it:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;star_mono_right R (star_comm P Q)<br>has type<br>&nbsp;&nbsp;R ∗ P ∗ Q ⊢ R ∗ Q ∗ P<br>but is expected to have type<br>&nbsp;&nbsp;(P ∗ Q) ∗ R ⊢ ?m.5</code><br><br>Read the reported type: <code>R</code> has become the left conjunct. That is the tell for a <code>_left</code>/<code>_right</code> mix-up, and it is quicker to spot than to reason out.',
     variants: 'Start the chain with <code>star_assoc_left</code> instead of <code>star_assoc_right</code> and the outermost application fails on its own, before the other two components are ever looked at:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;star_assoc_left P Q R<br>has type<br>&nbsp;&nbsp;(P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R<br>but is expected to have type<br>&nbsp;&nbsp;P ∗ Q ∗ R ⊢ ?m.2</code><br><br>One error, not three. Read the expected type: its right-hand side is still a metavariable, because the middle of the chain is exactly what has not been decided yet, while its left-hand side is already <code>P ∗ Q ∗ R</code>, pinned by the goal. So the only thing being checked at this joint is the <i>premise</i> of the component you supplied, and that is what did not match.<br><br>Try to get <code>star_swap_middle</code> from commutativity alone and you cannot: <code>star_comm P (Q ∗ R)</code> gives <code>(Q ∗ R) ∗ P</code>, and no amount of further commuting will separate <code>Q</code> from <code>R</code> without a re-bracketing.<br><br>Prove it semantically instead and it still works, in seven lines: one nested <code>intro</code>, a <code>subst</code>, <code>disjoint_union_right.mp</code>, a <code>refine</code>, a rewrite <code>rw [hu₁, ← union_assoc, ← union_assoc, union_comm hPQ]</code> and a tuple. Four heaps named and a fifth built, four heap lemmas in six applications, no reuse of anything on this page.<br><br>For <code>star_pure_left</code>, replace <code>pure</code> by <code>fact</code> and it becomes false — <code>factStar_not_and</code>, at the top of this page. Replace it in <code>star_pure_right</code> and it stays true and stops being worth stating, because the cut it produces is no longer forced.'
    },

    /* ============================================ or and exists === */

    {t:'sec', s:'Crossing a star, in both directions'},

    {t:'p', h:'Unit 15 pushed <code>∗</code> inward past a disjunction and past an existential: <code>(aOr P Q) ∗ R</code> entails <code>aOr (P ∗ R) (Q ∗ R)</code>, and <code>aExists P ∗ Q</code> entails <code>aExists (fun x => P x ∗ Q)</code>. The converses complete both, and they are the shapes you meet when a case analysis or a witness comes back up out of a proof and has to be put back under the star.'},

    {t:'code', tag:'sketch', cap:'The two converses. Both are true; the corpus proves each in four lines or fewer.',
     src:'theorem star_or_right (P Q R : Assertion) : aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by\n\ntheorem star_exists_right {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists (fun x => P x ∗ Q) ⊢ aExists P ∗ Q := by'},

    {t:'p', h:'Neither is automatic, and the way to see that is to try the same argument on <code>∀</code>, where it fails. In all three cases the premise hands you cuts and the goal asks for one. From <code>aOr (P ∗ R) (Q ∗ R)</code> you get one cut, in whichever disjunct you were given, and you hand it straight back. From <code>aExists (fun x => P x ∗ Q)</code> you get one witness and one cut, and hand both back. From <code>aForall (fun x => P x ∗ Q)</code> you get a cut <b>for every</b> <code>x</code>, and they need not agree; the goal wants a single one that works for all of them.'},

    {t:'state', cap:'Two <code>intro</code>s into the <code>∀</code> converse, and nowhere to go. <code>hall</code> is a family of splittings; the goal is one splitting.',
     src:'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh : Heap\nhall : aForall (fun x => P x ∗ Q) σ h\n⊢ (aForall P ∗ Q) σ h'},

    {t:'p', h:'The obstacle is not a shortage of ingenuity. Unit 15\'s <code>star_forall_right_fails</code> settles it: two locations, a family with two members whose cuts genuinely differ, and the entailment is refuted.'},

    /* ------------------------------------------------------------ x38 --- */

    {t:'ex',
     id: 'x38',
     name: 'star_or_right / star_exists_right',
     why: 'The pair closes the distribution laws and, more usefully, teaches you where to look when a distribution law fails. Both proofs are the same tuple handed back with one slot rewrapped, which is what makes the contrast with <code>∀</code> sharp: the shape of the argument is identical, and what decides whether it goes through is how many cuts the premise hands you. Neither converse is cited by name later — <code>star_exists_left</code>, the direction Unit 15 proved, is spent twice in Unit 33 — and what knowing the converse buys you there is the confidence that pulling an existential out from under a star loses nothing, so it can be done whenever it is convenient rather than only when it is forced.',
     setup: 'Both proofs consume a premise and rebuild a star. The only new thing is which slot changes: in <code>star_or_right</code> the fifth slot of the tuple has to be wrapped in <code>Or.inl</code> or <code>Or.inr</code>; in <code>star_exists_right</code> the fifth slot has to be wrapped in a one-slot <code>⟨x, …⟩</code>.',
     goal: 'theorem star_or_right (P Q R : Assertion) : aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by\n  sorry\n\ntheorem star_exists_right {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists (fun x => P x ∗ Q) ⊢ aExists P ∗ Q := by',
     hints: [
       'For the first: assume the disjunction of two stars at <code>σ</code> and <code>h</code>, and produce the star of the disjunction. In either case you are handed two heaps, a disjointness fact, a union equation, an ownership fact for <code>R</code>, and an ownership fact for whichever of <code>P</code> and <code>Q</code> you got. For the second: assume there is an <code>x</code> such that <code>P x ∗ Q</code> holds at <code>h</code>, and produce a star whose left conjunct is <code>aExists P</code>.',
       'Nothing about the cut changes. Both proofs take the cut they are given and give it back; the only thing that moves is the ownership fact for the left conjunct, which has to be rewrapped so that it proves the weaker statement the goal asks for. For the disjunction there are two cases and they differ only in which injection is used.',
       'For the first: <code>intro</code>, then <code>rcases</code> on the disjunction with two six-name patterns, then one <code>exact</code> per branch, with <code>Or.inl</code> and <code>Or.inr</code> in the fifth slot. For the second: a single <code>intro</code> whose pattern has the witness first and the six star names after it, then one <code>exact</code>.',
       'The disjunction splits with <code>rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩</code>, which leaves two goals with the same statement <code>(aOr P Q ∗ R) σ h</code> and different hypotheses. The existential opens with <code>intro σ h ⟨x, h₁, h₂, hd, hu, hp, hq⟩</code> — seven names, because the witness flattens in ahead of the star\'s six.'
     ],
     sol: 'theorem star_or_right (P Q R : Assertion) : aOr (P ∗ R) (Q ∗ R) ⊢ (aOr P Q) ∗ R := by\n  intro σ h hor\n  rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩\n  · exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩\n  · exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩\n\ntheorem star_exists_right {α : Sort u} (P : α → Assertion) (Q : Assertion) :\n    aExists (fun x => P x ∗ Q) ⊢ aExists P ∗ Q := by\n  intro σ h ⟨x, h₁, h₂, hd, hu, hp, hq⟩\n  exact ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩',
     expl: 'Both theorems give back exactly the cut they were handed. The heaps, the disjointness fact and the union equation travel unchanged from hypothesis to conclusion in all three branches; the single edit is to slot five, where an ownership fact for <code>P</code> is weakened into one for <code>aOr P Q</code>, or an ownership fact for <code>P x</code> is weakened into one for <code>aExists P</code>. Weakening a conjunct is legitimate under <code>∗</code> — what is not legitimate is dropping one, which is <code>no_star_weakening</code>.',
     walk: [
       {tac:'intro σ h hor', h:'Three binders, and the premise left folded under the name <code>hor</code>. It is not destructured here because the first thing to do to it is a case split, not a projection.'},
       {tac:'rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩', h:'One tactic doing two jobs: the bar splits the disjunction into two goals, and each six-name pattern opens the star inside that branch. The two branches reuse the same four names for the cut, so the two <code>exact</code>s below differ in one token.'},
       {tac:'· exact ⟨h₁, h₂, hd, hu, Or.inl hp, hr⟩', h:'The same six-slot tuple that came in, with slot five wrapped. <code>Or.inl hp</code> has type <code>aOr P Q σ h₁</code> because <code>aOr</code> is a lifted <code>∨</code> and its proofs are the ordinary injections.'},
       {tac:'· exact ⟨h₁, h₂, hd, hu, Or.inr hq, hr⟩', h:'The mirror. Everything except the injection is character-identical to the branch above.'},
       {tac:'intro σ h ⟨x, h₁, h₂, hd, hu, hp, hq⟩', h:'Seven names for what looks like two nested structures, because <code>⟨…⟩</code> flattens: the existential contributes the witness and the star contributes six, and they run together into one list.'},
       {tac:'exact ⟨h₁, h₂, hd, hu, ⟨x, hp⟩, hq⟩', h:'Now the nesting is the other way and the flattening cannot be relied on, because the witness has to sit inside slot five rather than in front of the whole tuple. Writing it as a nested pair puts it where the goal expects it.'}
     ],
     deep: [
       {t:'trace', title:'<code>star_or_right</code>: one tactic, two goals',
        start:'P Q R : Assertion\nσ : Store\nh : Heap\nhor : aOr (P ∗ R) (Q ∗ R) σ h\n⊢ (aOr P Q ∗ R) σ h',
        steps:[
          {tac:'rcases hor with ⟨h₁, h₂, hd, hu, hp, hr⟩ | ⟨h₁, h₂, hd, hu, hq, hr⟩',
           state:'case inl\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhr : R σ h₂\n⊢ (aOr P Q ∗ R) σ h\n\ncase inr\nP Q R : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhq : Q σ h₁\nhr : R σ h₂\n⊢ (aOr P Q ∗ R) σ h',
           h:'Two goals with identical conclusions. The only difference is the name and type of the fifth hypothesis, which is the only thing the two <code>exact</code>s differ in.'}
        ]},
       {t:'state', cap:'<code>star_exists_right</code> after its single <code>intro</code>. Nine names go in — the store, the heap, and the seven of the pattern — and eight lines come out, because the two heaps share one.',
        src:'α : Sort u\nP : α → Assertion\nQ : Assertion\nσ : Store\nh : Heap\nx : α\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P x σ h₁\nhq : Q σ h₂\n⊢ (aExists P ∗ Q) σ h'},
       {t:'p', h:'<code>x</code> is the only thing in that context that does not also appear in the goal, and it is why the theorem is true: there is exactly one of it, and it fits in one slot. Compare what the <code>∀</code> version would leave — a hypothesis <code>hall</code> from which a cut can be extracted at every <code>x</code>, with nothing in the context to say two of them agree, and a goal that names one pair of heaps.'}
     ],
     pitfall: 'Two, one per theorem.<br><br>Using <code>obtain</code> instead of <code>rcases</code> on the disjunction. It does split — <code>obtain ⟨h₁, h₂, hd, hu, hp, hr⟩ := hor</code> is accepted and solves the first branch — but the second one is still open, and the complaint arrives at the <code>theorem</code> keyword rather than where you were working:<br><br><code>error: unsolved goals<br>case inr<br>…<br>h✝ : (Q ∗ R) σ h<br>⊢ (aOr P Q ∗ R) σ h</code><br><br>The daggered name is the giveaway: a case you never named.<br><br>For <code>star_exists_right</code>, putting the witness in front of the outgoing tuple, mirroring the incoming one — <code>exact ⟨x, h₁, h₂, hd, hu, hp, hq⟩</code>. The incoming pattern flattened, so it looks as though the outgoing one will too. It does flatten, and that is the problem: it flattens against the <b>star</b>, whose first slot is a heap.<br><br><code>error: Application type mismatch: The argument<br>&nbsp;&nbsp;x<br>has type<br>&nbsp;&nbsp;α<br>of sort `Sort u` but is expected to have type<br>&nbsp;&nbsp;Heap<br>of sort `Type` in the application<br>&nbsp;&nbsp;Exists.intro x<br><br>error: Invalid `⟨...⟩` notation: The expected type `Q σ h₁` is not an inductive type</code><br><br>The second error is the same mistake seen at the far end. Seven entries have been poured into six slots, so everything is shifted by one: your <code>h₁</code> has landed in the star\'s <i>second</i> heap slot, which is why the last slot now wants <code>Q σ h₁</code>, and what reaches it is the leftover bracket <code>⟨hp, hq⟩</code> rather than a proof. The witness belongs inside slot five.',
     variants: 'Drop the wrapping in <code>star_or_right</code> and hand back <code>hp</code> bare: <code>The argument hp has type P σ h₁ but is expected to have type aOr P Q σ h₁</code>. The message names the exact weakening you forgot to perform.<br><br>Turn <code>star_or_right</code> around and it is <code>star_or_left</code>, which Unit 15 proved, so the two together give a <code>⊣⊢</code>. The same holds for the existential pair. The corresponding claim for <code>∀</code> is false in the right-to-left direction, and Unit 15\'s <code>star_forall_right_fails</code> is the counterexample; the proof above breaks at the point where a single cut has to serve every instance.<br><br>Replace <code>aOr</code> by <code>aAnd</code> and one direction survives while the other dies. <code>(aAnd P Q) ∗ R ⊢ aAnd (P ∗ R) (Q ∗ R)</code> goes through — one cut serves both conjuncts. The converse asks two independently chosen splittings to be the same splitting, and nothing makes them so: take the two-cell heap, <code>P</code> as <code>0 ↦ 4</code>, <code>Q</code> as <code>1 ↦ 7</code> and <code>R</code> as <code>aTrue</code>. Each of <code>P ∗ R</code> and <code>Q ∗ R</code> holds at it, but under cuts that are each other\'s mirror image — <code>(0 ↦ 4</code> cell, <code>1 ↦ 7</code> cell<code>)</code> for the first and the same pair reversed for the second — and a proof of the conclusion would have to be a single cut whose left half satisfies both <code>0 ↦ 4</code> and <code>1 ↦ 7</code>, which no heap does. Compiled, in both directions.'
    },

    /* ============================================ the toolkit === */

    {t:'sec', s:'Normalisation, and the whole toolkit'},

    {t:'p', h:'A precondition arrives in whatever shape the last step left it in. The next step wants a particular shape — its own footprint at the front, everything it does not touch behind, and any store facts pulled out where they can be read. Getting from the first to the second is <b>normalisation</b>, and it is what the entailment half of every later proof consists of: eleven <code>entails_trans</code> steps in the units after this one, spread over five proofs, and not one of them names a heap. This table is what they are built from.'},

    {t:'tbl', cap:'Every shape-to-shape move Module 3 proved, and the one it refuted. Chain any of them with <code>entails_trans</code>; rewrite inside a star with <code>star_congr</code> or <code>star_mono_left</code>/<code>star_mono_right</code>.',
     head:['you have', 'you want', 'the lemma'],
     rows:[
       ['<code>emp ∗ P</code>', '<code>P</code>', '<code>star_emp_left</code>'],
       ['<code>P</code>', '<code>emp ∗ P</code>', '<code>star_emp_left_intro</code>'],
       ['<code>P ∗ emp</code>', '<code>P</code>', '<code>star_emp_right</code>'],
       ['<code>P</code>', '<code>P ∗ emp</code>', '<code>star_emp_right_intro</code>'],
       ['<code>P ∗ Q</code>', '<code>Q ∗ P</code>', '<code>star_comm</code>'],
       ['<code>(P ∗ Q) ∗ R</code>', '<code>P ∗ (Q ∗ R)</code>', '<code>star_assoc_left</code> = <code>star_rotate_right</code>'],
       ['<code>P ∗ (Q ∗ R)</code>', '<code>(P ∗ Q) ∗ R</code>', '<code>star_assoc_right</code> = <code>star_rotate_left</code>'],
       ['<code>P ∗ (Q ∗ R)</code>', '<code>Q ∗ (P ∗ R)</code>', '<code>star_swap_middle</code>'],
       ['<code>P ⊢ P\'</code>', '<code>P ∗ Q ⊢ P\' ∗ Q</code>', '<code>star_mono_left</code>'],
       ['<code>Q ⊢ Q\'</code>', '<code>P ∗ Q ⊢ P ∗ Q\'</code>', '<code>star_mono_right</code>'],
       ['<code>pure φ ∗ P</code>', '<code>aAnd (fact φ) P</code>', '<code>star_pure_left</code>'],
       ['<code>aAnd (fact φ) P</code>', '<code>pure φ ∗ P</code>', '<code>star_pure_right</code>'],
       ['<code>(aOr P Q) ∗ R</code>', '<code>aOr (P ∗ R) (Q ∗ R)</code>', '<code>star_or_left</code>'],
       ['<code>aOr (P ∗ R) (Q ∗ R)</code>', '<code>(aOr P Q) ∗ R</code>', '<code>star_or_right</code>'],
       ['<code>aExists P ∗ Q</code>', '<code>aExists (fun x => P x ∗ Q)</code>', '<code>star_exists_left</code>'],
       ['<code>aExists (fun x => P x ∗ Q)</code>', '<code>aExists P ∗ Q</code>', '<code>star_exists_right</code>'],
       ['<code>aForall P ∗ Q</code>', '<code>aForall (fun x => P x ∗ Q)</code>', '<code>star_forall_left</code>'],
       ['<code>aForall (fun x => P x ∗ Q)</code>', '<code>aForall P ∗ Q</code>', 'no such theorem — <code>star_forall_right_fails</code>']
     ]},

    {t:'p', h:'A normalisation is a term. Here is one of the shortest useful ones: a store fact buried one level down in a star, brought out to the front where a rule can read it.'},

    {t:'code', tag:'illustration', cap:'Two lemmas from the table, glued. No tactic, no heap, no tuple.',
     src:'theorem normalise_demo (φ : Store → Prop) (P R : Assertion) :\n    P ∗ (pure φ ∗ R) ⊢ aAnd (fact φ) (P ∗ R) :=\n  entails_trans (star_swap_middle P (pure φ) R) (star_pure_left φ (P ∗ R))'},

    {t:'p', h:'<code>star_swap_middle</code> brings the <code>pure</code> conjunct to the front, past <code>P</code>; <code>star_pure_left</code> then converts <code>pure φ ∗ (P ∗ R)</code> into <code>aAnd (fact φ) (P ∗ R)</code>, at which point the fact is a hypothesis and the resources are untouched. Two lines, and the ownership of <code>P</code> and <code>R</code> was never in question.'},

    {t:'dod', h:'You can look at a precondition, say what shape the next step needs it in, and write the chain of <code>entails_trans</code> that gets there — without unfolding <code>∗</code>. You can say why <code>fact</code> belongs under <code>aAnd</code> and <code>pure</code> under <code>∗</code>, and refute the pairing that is wrong. You can prove that a two-cell precondition contains its own non-aliasing hypothesis.'},

    {t:'p', h:'The algebra is complete and every law it has is proved. It cannot state the frame rule, because the frame rule says a <i>command</i> leaves the frame alone, and there are no commands. The next module builds them, and mentions <code>∗</code> exactly zero times.'}

  ]
});
