registerChapter({
  id: 'splits',
  num: '11',
  phase: 'Phase 1 · The resource algebra',
  title: 'LAB — splitting a heap',
  blurb: 'The relation that says one heap is two heaps side by side, and the four theorems that make it usable — ending with the associativity of a partial operation, which is not the associativity of the total operation underneath it.',

  orient: {
    youWill: [
      'Read <code>Heap.splits whole left right</code> as a conjunction, build one with <code>⟨_, _⟩</code>, and say why the logic quantifies over the <i>relation</i> and could not quantify over an operation.',
      'Prove <code>splits_empty_left</code> as a one-line term proof and give its tactic transcript, and prove <code>splits_comm</code> in two.',
      'Prove <code>splits_assoc</code>, whose statement is an existential: choose the witness before discharging the obligations, and <code>subst</code> the heap equation <i>before</i> asking Lean for the goals.',
      'Name the two <code>disjoint_union_*</code> uses as the whole content of that proof: the equation is free, and every hypothesis it needs has to be manufactured.',
      'Say in one sentence why this is harder than <code>union_assoc</code>.',
      'State a negation from scratch and prove it: union is not commutative.'
    ],
    needs: [
      'Unit 10: <code>union_assoc</code>, <code>union_comm</code>, <code>disjoint_union_left</code> and <code>disjoint_union_right</code> — all four, and nothing else about combination.',
      'Unit 09: both unit laws, and that <code>Heap.union Heap.empty h</code> reduces to <code>h</code> while <code>Heap.union h Heap.empty</code> does not.',
      'Unit 08: <code>Heap.disjoint</code>, <code>disjoint_symm</code>, <code>singleton_disjoint_iff</code>. Unit 01: <code>⟨…⟩</code> and its flattening, <code>obtain</code>, <code>.mp</code>/<code>.mpr</code>.'
    ],
    payoff: 'The last proof on this page is Unit 16\'s associativity of the connective Module 3 is built on, with every trace of assertions removed. Those two proofs agree line for line; the difference is four extra components in the tuples. Everything hard about that unit is on this page, where there is nothing else to look at.'
  },

  blocks: [

    /* ----------------------------------------------------------------- brief --- */

    {t:'p', h:'Unit 08 wrote <code>Heap.splits</code> down in the same breath as <code>Heap.union</code>, because the definition of one mentions the other, and then proved nothing whatever about it. The algebra is now finished — seventeen theorems and a structure with eight fields — and the relation is still exactly as it was: two lines of text and not one fact. It is also the only object in this module that Module 3 will quantify over. Every rule of the logic is a statement about the ways a heap can be cut in two.'},

    {t:'p', h:'This lab proves four theorems about the cutting: that a heap splits into nothing and itself, that it splits into itself and nothing, that a split can be read in either order, and that a split of a split can be re-bracketed. The first three are one or two lines each and they exist so that the fourth has somewhere to stand. The fourth is <code>splits_assoc</code>, and it is the first proof in the course whose difficulty is mathematical rather than notational: nothing in its statement tells you what to do, the hypotheses it needs are not the hypotheses it is given, and the object it has to produce is not named anywhere.'},

    /* ------------------------------------------------------- relation not op --- */

    {t:'sec', s:'A relation, not an operation'},

    {t:'anat', tag:'verified', src:'def Heap.splits (whole left right : Heap) : Prop :=\n  Heap.disjoint left right ∧ whole = Heap.union left right',
     parts:[
       {m:'whole left right', h:'Three heaps, named by the role they play rather than by a number. Read the application <code>Heap.splits h h₁ h₂</code> as <i>h is h₁ and h₂ side by side</i>, with <code>h</code> the thing being cut and the other two the pieces.'},
       {m:'Prop', h:'It is a proposition, not a heap and not a Boolean. There is nothing to compute here: a statement about two arbitrary heaps at every one of infinitely many addresses is not something a program could decide.'},
       {m:'Heap.disjoint left right', h:'The first half: the pieces do not overlap. Without it the second half would still be satisfiable — <code>Heap.union</code> is total and always returns something — and it would be satisfied by pieces that both claim the same cell, which is precisely the situation ownership is supposed to exclude.'},
       {m:'whole = Heap.union left right', h:'The second half: the pieces account for all of the whole. Look at which side of the equation the whole is on. That orientation is what makes <code>subst</code> and <code>rw</code> replace the whole by the combination rather than the other way round, and every proof on this page depends on it.'}
     ]},

    {t:'p', h:'You could carry the same information as two separate hypotheses and never name the pair. Bundling them buys one thing, and it is the thing Module 3 is made of. The central connective there has to say <i>there is some way of cutting this heap in two so that the first piece satisfies P and the second satisfies Q</i>. That sentence starts with a quantifier, and a quantifier needs a single proposition to bind.'},

    {t:'p', h:'That is also why it is a relation and not a function. An operation would take two heaps and a proof that they do not overlap and return the combination; you could then name the result of a cut you already had. You could not ask whether <i>any</i> cut works, because to ask that you have to range over the cuts, and the cuts are not values of anything. A heap has many splittings — a two-cell heap has four, one per way of dealing the two cells — and the logic has to quantify over them. Unit 09 refused a proof-carrying operation for a quite different reason, that the disjointness proof travels inside the term and every rewrite trips over it; the relation is what is left when you take the operation away and keep the statement.'},

    /* ------------------------------------------------------- worked example --- */

    {t:'sec', s:'Worked: the smallest split there is'},

    {t:'p', h:'Take the emptiest cut. Every heap <code>h</code> splits into the empty heap on the left and <code>h</code> itself on the right: you have given away nothing and kept everything. Both halves of the definition need checking, and both are already theorems from earlier units, so the whole proof is one pair.'},

    {t:'code', tag:'verified', cap:'A term, not a tactic block. The proof of a conjunction is a pair of proofs, and both components are named lemmas.',
     src:'theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=\n  ⟨disjoint_empty_left h, (union_empty_left h).symm⟩'},

    {t:'p', h:'For <code>⟨…⟩</code> to work at all, Lean has to know how many slots the goal has, and the goal is <code>Heap.splits h Heap.empty h</code> — a name applied to three heaps, with no conjunction visible anywhere in it. So Lean unfolds the name, finds a conjunction underneath, and asks for two components. You can make that step visible with <code>show</code>, because a folded definition is definitionally equal to its body.'},

    {t:'code', tag:'illustration', cap:'The same proof with the unfolding written out. The <code>show</code> line changes nothing about what has to be proved; it changes what you can see.',
     src:'example (h : Heap) : Heap.splits h Heap.empty h := by\n  show Heap.disjoint Heap.empty h ∧ h = Heap.union Heap.empty h\n  exact ⟨disjoint_empty_left h, (union_empty_left h).symm⟩'},

    {t:'state', cap:'The goal after the <code>show</code>, from <code>trace_state</code> — written out in full above, printed back in dot notation. The line-and-column prefix is dropped here and everywhere below.',
     src:'h : Heap\n⊢ Heap.empty.disjoint h ∧ h = Heap.empty.union h'},

    {t:'p', h:'Now the two slots are readable. The first wants <code>Heap.disjoint Heap.empty h</code>, which is <code>disjoint_empty_left h</code> exactly. The second wants <code>h = Heap.union Heap.empty h</code>, and Unit 09 proved that equation the other way round, so <code>.symm</code> turns it. That is the whole proof.'},

    {t:'p', h:'The same object in tactic mode. <code>constructor</code> takes the goal apart instead of you supplying the pair, and it unfolds <code>Heap.splits</code> to do it — the same unfolding <code>⟨…⟩</code> did silently.'},

    {t:'code', tag:'illustration', cap:'Three lines instead of one. The case labels are <code>And</code>\'s two field names, which is where <code>.1</code> and <code>.2</code> get their meaning.',
     src:'example (h : Heap) : Heap.splits h Heap.empty h := by\n  constructor\n  · exact disjoint_empty_left h\n  · exact (union_empty_left h).symm'},

    {t:'trace', title:'splits_empty_left, tactic by tactic',
     start:'h : Heap\n⊢ h.splits Heap.empty h',
     steps:[
       {tac:'constructor',
        state:'case left\nh : Heap\n⊢ Heap.empty.disjoint h',
        h:'The relation is gone from the goal display. <code>constructor</code> could only have applied <code>And.intro</code> after deciding that <code>h.splits Heap.empty h</code> <i>is</i> a conjunction, and having decided it, it shows you the conjunct.'},
       {tac:'· exact disjoint_empty_left h',
        state:'case right\nh : Heap\n⊢ h = Heap.empty.union h',
        h:'First goal closed; the second is the equation, with the whole heap on the left of the <code>=</code>, exactly as the definition orients it.'},
       {tac:'· exact (union_empty_left h).symm',
        state:'No goals.',
        h:'<code>union_empty_left h</code> proves <code>Heap.empty.union h = h</code>. The goal is that equation read backwards, and <code>.symm</code> is how you read an equation backwards.'}
     ],
     done:'No goals.'},

    {t:'p', h:'Three lines against one, and the same proof term at the end of both. From Module 3 on the short spelling is the normal one, so this is the last place where the two are written out against each other.'},

    {t:'p', h:'Here is what you would plausibly try instead, and it works. The second slot wants <code>h = Heap.union Heap.empty h</code>, and Unit 09 recorded that <code>Heap.union Heap.empty h</code> reduces to <code>h</code> with no lemma at all — reduction under the binder, then eta. So <code>rfl</code> fills the slot:'},

    {t:'code', tag:'illustration', cap:'Accepted. Both sides of the equation are the same term after reduction, so there is nothing for a lemma to do.',
     src:'example (h : Heap) : Heap.splits h Heap.empty h := ⟨disjoint_empty_left h, rfl⟩'},

    {t:'p', h:'What licenses that is which side of the combination the empty heap sits on, not anything about the empty heap itself. Mirror the theorem — empty on the right — and the second slot stops being <code>rfl</code>. The exercise below is where that bites.'},

    /* ------------------------------------------------------------ exercises --- */

    {t:'sec', s:'The laws'},

    {t:'ex',
     id:'x25',
     name:'splits_empty_right',
     hard:false,
     why:'The mirror image of the worked example, and the course has been asymmetric without it: <code>disjoint_empty_left</code> and <code>disjoint_empty_right</code> both exist, <code>union_empty_left</code> and <code>union_empty_right</code> both exist, and until now only one of the two unit laws for splitting did. It is also the cheapest place to feel the difference between the two sides of a left-biased operation, because here that difference is the whole exercise.',
     setup:'A term proof, no <code>by</code>. Two slots: a disjointness and an equation. Both are named theorems you already have, and one of them needs turning round.',
     goal:'theorem splits_empty_right (h : Heap) : Heap.splits h h Heap.empty :=',
     hints:[
       'The goal is a name applied to three heaps. Unfold the name and it is a conjunction: <code>Heap.disjoint h Heap.empty ∧ h = Heap.union h Heap.empty</code>. Two components, and in the second one the whole heap sits on the left of the equals sign, where the definition of <code>Heap.splits</code> puts it.',
       'A proof of a conjunction is a pair of proofs, so the answer has two parts and neither part needs a tactic. The first part says the empty heap overlaps nothing — here it is the second of the two heaps rather than the first. The second part says combining a heap with nothing gives that heap back, and the fact you have states that with the whole heap on the <i>right</i> of the equals sign while your goal has it on the left, so it has to be read backwards.',
       'The anonymous constructor <code>⟨_, _⟩</code>, <code>disjoint_empty_right</code>, <code>union_empty_right</code>, and <code>.symm</code> on the second one.',
       'The proof is <code>⟨disjoint_empty_right h, (union_empty_right h).symm⟩</code>. Both arguments are explicit, so both take <code>h</code>.'
     ],
     sol:'theorem splits_empty_right (h : Heap) : Heap.splits h h Heap.empty :=\n  ⟨disjoint_empty_right h, (union_empty_right h).symm⟩',
     solNote:'One line, and it is the worked example with <code>left</code> and <code>right</code> exchanged everywhere. That exchange is not free: the equation component is now the law that needs a proof rather than the one that holds by reduction.',
     expl:'Both components are quotations. What the exercise is really testing is whether you can read the orientation of an equation off a goal: <code>union_empty_right h</code> is <code>Heap.union h Heap.empty = h</code>, and the slot wants <code>h = Heap.union h Heap.empty</code>. Those are two different terms of two different types, and <code>.symm</code> is the function between them.',
     walk:[
       {tac:'⟨_, _⟩', h:'Committed to building the conjunction directly. Lean unfolds <code>Heap.splits</code> to discover that two components are wanted and what type each has.'},
       {tac:'disjoint_empty_right h', h:'Filled the first slot. It is stated with the empty heap on the right, matching the position <code>Heap.empty</code> occupies in the goal, so nothing has to be turned.'},
       {tac:'(union_empty_right h).symm', h:'Filled the second. Without <code>.symm</code> the term has type <code>Heap.union h Heap.empty = h</code> and the slot wants the reverse; <code>.symm</code> is <code>Eq.symm</code> reached by dot notation on a proof whose type is headed by <code>Eq</code>.'}
     ],
     deep:[
       {t:'trace', title:'The same proof in tactic mode, so you can see both goals',
        start:'h : Heap\n⊢ h.splits h Heap.empty',
        steps:[
          {tac:'constructor',
           state:'case left\nh : Heap\n⊢ h.disjoint Heap.empty',
           h:'Compare with the worked example: there the first goal was <code>Heap.empty.disjoint h</code>. Two different propositions, differing in which argument of <code>Heap.disjoint</code> the empty heap occupies, which is why Unit 08 states both and proves each in a line.'},
          {tac:'· exact disjoint_empty_right h',
           state:'case right\nh : Heap\n⊢ h = h.union Heap.empty',
           h:'This is the goal that refuses <code>rfl</code>, where its mirror image in the worked example accepted it. Same shape, same two heaps, opposite answer.'},
          {tac:'· exact (union_empty_right h).symm',
           state:'No goals.',
           h:'Unit 09 spent a <code>funext</code> and a two-branch case split on that equation. Here it is one name.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The two unit laws for splitting have the same statement up to exchanging the pieces, and different proofs at exactly one component. That is what a left-biased operation costs, priced in lemmas.'}
     ],
     pitfall:'Writing <code>rfl</code> for the equation, because it worked in the worked example above. Lean answers <code>Application type mismatch: The argument rfl has type ?m.4 = ?m.4 but is expected to have type h = h.union Heap.empty in the application ⟨disjoint_empty_right h, rfl⟩</code> (line breaks removed). <code>rfl</code> closes an equation only when both sides reduce to a single term, and these two do not: <code>h.union Heap.empty</code> at an address is a <code>match</code> on <code>h l</code>, <code>h l</code> is a variable, and a <code>match</code> on a variable is stuck. The repair is the lemma, and the reason you need one is Unit 09\'s: the left argument of the combination is consulted first, so with the empty heap on the left everything reduces and with it on the right nothing does.',
     variants:'Drop the <code>.symm</code> and Lean names both orientations at once: <code>Application type mismatch: The argument union_empty_right h has type h.union Heap.empty = h but is expected to have type h = h.union Heap.empty</code> (line breaks removed). Do the same thing to <code>splits_empty_left</code> and Lean accepts it, because there the two sides of the equation reduce to the same term and so do the two <i>types</i> <code>Heap.union Heap.empty h = h</code> and <code>h = Heap.union Heap.empty h</code>. Both were compiled. Treat that as an accident of the left unit law rather than a licence: it holds for no other equation in this module. Replace <code>Heap.empty</code> by an arbitrary second heap and the statement fails the moment the two pieces share an address. The sharpest form of that is the strengthening <code>Heap.splits h h h ↔ h = Heap.empty</code>: its forward direction is <code>self_disjoint_iff_empty</code> applied to the first component and nothing else, so the only heap that splits into two copies of itself is the empty one. Compiled.'
    },

    {t:'p', h:'Next, a split read backwards: two theorems in one exercise, the first transcribed from the worked example and the second costing two rewrites, one of which has to be paid for with a disjointness proof.'},

    {t:'ex',
     id:'m2-8',
     name:'splits_empty_left / splits_comm',
     hard:false,
     why:'<code>splits_comm</code> is the first theorem you prove that has to hand a disjointness proof to a lemma demanding one, and the shape of a move Module 3 makes constantly: a hypothesis is taken apart, one half is used to repair the other, and the pair is rebuilt. Its proof body is also, character for character, the body of Unit 15\'s commutativity law for the connective — with four more components in the tuple and <code>hu</code> in place of <code>he</code>. As with <code>splits_assoc</code> below, you are writing a Module 3 proof early, with nothing standing in front of it.',
     setup:'Two theorems. The first is the worked example, transcribed — you have seen its proof and you are typing it, which is deliberate: the editor checks both statements together, so the second cannot be attempted without the first present. The work is in <code>splits_comm</code>. Its hypothesis is a <code>Heap.splits</code>, so it can be taken apart in the <code>intro</code> pattern itself.',
     goal:'theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=\n  sorry\n\ntheorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁ := by',
     hints:[
       'Two goals. The first is the worked example, which you are transcribing. The second is an implication, and both of its sides unfold to conjunctions: the hypothesis is <code>h₁.disjoint h₂ ∧ h = h₁.union h₂</code>, and the conclusion is <code>h₂.disjoint h₁ ∧ h = h₂.union h₁</code>. The same two facts about the same three heaps, with the two pieces exchanged.',
       'Both components of the conclusion are components of the hypothesis with the pieces exchanged, so the question is what each exchange costs. Exchanging them in a disjointness statement is a theorem from Unit 08 with no side condition. Exchanging them in a combination is a theorem from Unit 10 that has one, and the side condition is the disjointness you were handed.',
       '<code>disjoint_symm</code> for the first component. For the second, <code>rw</code> twice: once with <code>he</code>, to replace the whole by the combination, and once with <code>union_comm</code>, which takes the disjointness as its argument.',
       'Open with <code>intro ⟨hd, he⟩</code>, which introduces the hypothesis and destructures it in one step, leaving <code>⊢ h.splits h₂ h₁</code>. Then <code>refine ⟨disjoint_symm hd, ?_⟩</code> discharges the first component outright and leaves <code>⊢ h = h₂.union h₁</code> as the only goal, two rewrites from done. The shipped proof puts those two rewrites in a <code>by</code> block in the second slot rather than using <code>refine</code>; it is the same proof.'
     ],
     sol:'theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=\n  ⟨disjoint_empty_left h, (union_empty_left h).symm⟩\n\ntheorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁ := by\n  intro ⟨hd, he⟩\n  exact ⟨disjoint_symm hd, by rw [he, union_comm hd]⟩',
     solNote:'The order of the two rewrites is forced. <code>union_comm hd</code> is about <code>h₁.union h₂</code>, and until <code>he</code> has fired there is no <code>h₁.union h₂</code> in the goal for it to find.',
     expl:'Every component of the answer is a component of the hypothesis with something applied to it. <code>disjoint_symm</code> exchanges the arguments of a disjointness for nothing; <code>union_comm</code> exchanges the arguments of a combination for the price of a disjointness proof, and the proof it wants is the one already in the context. Naming that is the point of the exercise: <code>splits_comm</code> looks like a symmetry of the relation, and it is really the one law of the algebra that is not free, wearing the relation as a coat.',
     walk:[
       {tac:'⟨disjoint_empty_left h, (union_empty_left h).symm⟩', h:'The first theorem, transcribed from the worked example. Both components are quotations and the <code>.symm</code> turns the unit law round.'},
       {tac:'intro ⟨hd, he⟩', h:'Introduced the implication\'s hypothesis and destructured it in the same step. The context gains <code>hd : h₁.disjoint h₂</code> and <code>he : h = h₁.union h₂</code>; no hypothesis called <code>Heap.splits</code> is left, because it was never named.'},
       {tac:'exact ⟨disjoint_symm hd, …⟩', h:'Built the answer as a pair. The first slot is discharged outright: <code>disjoint_symm hd</code> has exactly the type <code>h₂.disjoint h₁</code> that the unfolded goal wants.'},
       {tac:'by rw [he, union_comm hd]', h:'The second slot, in tactic mode inside a term. <code>rw [he]</code> turns <code>⊢ h = h₂.union h₁</code> into <code>⊢ h₁.union h₂ = h₂.union h₁</code>; <code>rw [union_comm hd]</code> rewrites the left-hand side to <code>h₂.union h₁</code> and the trailing <code>rfl</code> closes it.'}
     ],
     deep:[
       {t:'trace', title:'splits_comm, with the second slot opened out',
        start:'h h₁ h₂ : Heap\n⊢ h.splits h₁ h₂ → h.splits h₂ h₁',
        steps:[
          {tac:'intro ⟨hd, he⟩',
           state:'h h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhe : h = h₁.union h₂\n⊢ h.splits h₂ h₁',
           h:'One tactic, two effects: the arrow is discharged and the conjunction behind it is broken up. The pattern is the same one Unit 00 used on an <code>∧</code>, applied to a folded definition that turns out to be one.'},
          {tac:'refine ⟨disjoint_symm hd, ?_⟩',
           state:'h h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhe : h = h₁.union h₂\n⊢ h = h₂.union h₁',
           h:'Written with <code>refine</code> here so the remaining slot becomes a visible goal. In the shipped proof it is a <code>by</code> block in that slot instead; the two are the same proof.'},
          {tac:'rw [he]',
           state:'h h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhe : h = h₁.union h₂\n⊢ h₁.union h₂ = h₂.union h₁',
           h:'The whole heap has been replaced by the combination, and what is left is <i>exactly the statement of</i> <code>union_comm</code>. This is the moment the relation stops being involved and the algebra takes over.'},
          {tac:'rw [union_comm hd]',
           state:'No goals.',
           h:'The rewrite fires on the left-hand side and the trailing <code>rfl</code> finishes. <code>hd</code> is spent here and nowhere else in the proof.'}
        ],
        done:'No goals.'},
       {t:'p', h:'A second route reaches the same place. <code>rw [union_comm hd] at he</code> rewrites the hypothesis instead of the goal, leaving <code>he : h = h₂.union h₁</code>, which <i>is</i> the goal, so the slot becomes <code>by rw [union_comm hd] at he; exact he</code>. It compiles and it is longer, and the reason to know it exists is that rewriting forwards in a hypothesis and backwards in a goal are the same move seen from two ends — later units use whichever end has fewer occurrences to disturb.'}
     ],
     pitfall:'Handing <code>hd</code> to the first slot instead of <code>disjoint_symm hd</code>. The two heaps have been exchanged in the goal and not in the hypothesis, so Lean answers <code>Application type mismatch: The argument hd has type h₁.disjoint h₂ but is expected to have type h₂.disjoint h₁ in the application And.intro hd</code> (line breaks removed). Disjointness is symmetric as a fact and not as a term: the two statements are different propositions and <code>disjoint_symm</code> is the function that converts one into the other.',
     variants:'Rewrite in the other order — <code>rw [union_comm hd, he]</code> — and the first rewrite fails outright: <code>Tactic `rewrite` failed: Did not find an occurrence of the pattern h₁.union h₂ in the target expression h = h₂.union h₁</code> (line breaks removed). Nothing in the goal mentions <code>h₁.union h₂</code> until <code>he</code> has put it there. Drop the argument and write <code>rw [he, union_comm]</code> and the failure is quieter: the rewrite fires, because <code>rw</code> is willing to leave a lemma\'s unsupplied hypothesis behind as a second goal, and the proof ends with <code>unsolved goals … ⊢ h₁.disjoint h₂</code>. The disjointness has not gone away; it has been deferred, and <code>hd</code> is what discharges it. That deferred goal is exactly where commutativity would be false if you could not discharge it, which is what exercise <code>x26</code> below asks you to state. Compiled. Finally, the theorem exchanges the two <i>pieces</i> and licenses nothing about exchanging a piece with the whole: <code>Heap.splits (Heap.singleton 0 4) Heap.empty (Heap.singleton 0 4)</code> holds, and <code>Heap.splits Heap.empty (Heap.singleton 0 4) (Heap.singleton 0 4)</code> is refutable in two lines, because its first component asks a one-cell heap to be disjoint from itself. Both compiled.'
    },

    {t:'p', h:'That a heap has more than one splitting is itself a theorem, and for a single cell the two unit laws are already the two splittings:'},

    {t:'code', tag:'illustration', cap:'The same heap cut two ways. Nothing in the definition prefers either, which is what gives <i>some cut works</i> any content at all.',
     src:'example : Heap.splits (Heap.singleton 0 4) Heap.empty (Heap.singleton 0 4) :=\n  splits_empty_left _\n\nexample : Heap.splits (Heap.singleton 0 4) (Heap.singleton 0 4) Heap.empty :=\n  splits_empty_right _'},

    /* ---------------------------------------------------------- associativity --- */

    {t:'sec', s:'Associativity of a partial operation'},

    {t:'p', h:'Now cut twice. A heap <code>h</code> is split into <code>hPQ</code> and <code>hR</code>; then <code>hPQ</code> is itself split into <code>hP</code> and <code>hQ</code>. Three pieces, bracketed to the left. Re-bracket them to the right and the claim is that the same three pieces are still a legitimate division of <code>h</code>.'},

    {t:'txt', cap:'What has to be produced is the node marked with the question mark. It is not mentioned in the hypotheses, it is not mentioned in the conclusion until you supply it, and until it has been chosen there is nothing in the goal to work on.',
     src:'        h                              h\n       / \\                            / \\\n    hPQ   hR          ⟶            hP   ?\n    / \\                                 / \\\n  hP   hQ                             hQ   hR'},

    {t:'code', tag:'verified', cap:'The statement. Its conclusion is an existential whose body is a conjunction of two more splittings.',
     src:'theorem splits_assoc {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by'},

    {t:'p', h:'Compare that with <code>union_assoc</code>, which needs no hypothesis and says the two bracketings of the total operation are the same heap. The difference is the existential, and the existential is not decoration. For a partial operation, associativity has to assert that the middle combination <i>exists</i> — that it is a legal combination and not only a term you can write down. <code>Heap.union hQ hR</code> is always writable, because Unit 09 made the operation total; what is not automatic is that <code>hQ</code> and <code>hR</code> may legitimately stand side by side, and that is the fact the existential is carrying. <b>The associativity of a partial operation is not the associativity of the total operation underneath it.</b> It is that, plus definedness.'},

    {t:'p', h:'So the witness is not the hard part: it can only be <code>Heap.union hQ hR</code>. What has to happen before you can name it is that <code>hPQ</code> disappears. Unit 10\'s two bridges are stated about a <i>combination</i> — <code>Heap.disjoint (Heap.union h₁ h₂) h₃</code>, and its mirror — and what the hypotheses hand you is <code>hd₁ : hPQ.disjoint hR</code>, in which <code>hPQ</code> is a bare variable. Nothing matches a variable against a combination, so while <code>hPQ</code> is still in the proof neither bridge can be used on <code>hd₁</code> at all.'},

    {t:'p', h:'<code>he₂ : hPQ = hP.union hQ</code> is what removes it. <code>subst he₂</code> deletes the variable and rewrites every hypothesis that mentioned it, so <code>hd₁</code> becomes a statement about <code>(hP.union hQ).disjoint hR</code>. Substituting the equations first and asking for the goals second is the order this proof has to be written in.'},

    {t:'p', h:'With that done, write the four obligations out with holes in them and look at them before proving anything.'},

    {t:'code', tag:'sketch', cap:'Deliberately unfinished: it stops after the <code>refine</code>, and Lean answers <code>unsolved goals</code> with four of them. No hypothesis mentions <code>hPQ</code>, because <code>subst</code> has replaced it by <code>hP.union hQ</code> everywhere.',
     src:'example {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by\n  obtain ⟨hd₁, he₁⟩ := h1\n  obtain ⟨hd₂, he₂⟩ := h2\n  subst he₂\n  refine ⟨Heap.union hQ hR, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩'},

    {t:'tbl', cap:'The four goals, in the order Lean numbers them. Besides the four heaps, the context is the same in all four: <code>hd₂ : hP.disjoint hQ</code>, <code>hd₁ : (hP.union hQ).disjoint hR</code>, <code>he₁ : h = (hP.union hQ).union hR</code>. The full display is in the fold below.',
     head:['hole', 'goal', 'what it needs'],
     rows:[
       ['<code>refine_1</code>', '<code>hP.disjoint (hQ.union hR)</code>', 'a disjointness that has to be <b>built</b>: from <code>hP</code> against <code>hQ</code> and <code>hP</code> against <code>hR</code>'],
       ['<code>refine_2</code>', '<code>h = hP.union (hQ.union hR)</code>', 'the equation — <code>he₁</code> and <code>union_assoc</code>, and nothing else'],
       ['<code>refine_3</code>', '<code>hQ.disjoint hR</code>', 'a disjointness that has to be <b>extracted</b>: it is hiding inside <code>hd₁</code>'],
       ['<code>refine_4</code>', '<code>hQ.union hR = hQ.union hR</code>', '<code>rfl</code> — and it is <code>rfl</code> only because of how the witness was chosen']
     ]},

    {t:'detail', title:'The four goals as Lean prints them', tag:'aside', open:false, blocks:[
      {t:'p', h:'Twenty-four lines, because the five-line context is repeated under each goal. This is what the table above is an index to.'},
      {t:'state', cap:'From <code>trace_state</code> immediately after the <code>refine</code>, with the four goals separated by blank lines as Lean separates them.',
       src:'case refine_1\nh hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\n⊢ hP.disjoint (hQ.union hR)\n\ncase refine_2\nh hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\n⊢ h = hP.union (hQ.union hR)\n\ncase refine_3\nh hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\n⊢ hQ.disjoint hR\n\ncase refine_4\nh hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\n⊢ hQ.union hR = hQ.union hR'}
    ]},

    {t:'note', kind:'key', title:'Where the work is',
     h:'One of those four is the equation, and it costs two rewrites and no hypothesis, because <code>union_assoc</code> holds for every triple of heaps. One is <code>rfl</code>. The other two are disjointness facts that nobody handed you: <code>hQ.disjoint hR</code> has to be pulled out of a hypothesis about a combination, and <code>hP.disjoint (hQ.union hR)</code> has to be assembled from two smaller facts. That is the whole content of the theorem, and the lemmas that supply both are Unit 10\'s two bridges.'},

    {t:'ex',
     id:'m2-9',
     name:'splits_assoc',
     hard:true,
     why:'The module checkpoint, and the proof this whole page exists to make writable. Unit 16 proves associativity for Module 3\'s central connective in six lines, and four of them are four of these, changed in one name: the same <code>subst</code>, the same <code>obtain … := disjoint_union_left.mp hd₁</code>, the same <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code> inside the <code>refine</code>, the same <code>rw [_, union_assoc]</code>. The difference is that there the tuples carry assertion components as well, and an <code>intro</code> at the front does the work of your two <code>obtain</code>s. You are writing that proof now, with nothing standing in front of it.',
     setup:'Two hypotheses, both splittings, and a conclusion that is an existential over a conjunction of two more. The conclusion mentions five heaps and exactly one of them, the bound <code>hQR</code>, is not named in the hypotheses. Nothing in this proof unfolds a definition and nothing does a case split; every step is either taking a hypothesis apart or applying a named lemma to it.',
     goal:'theorem splits_assoc {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by',
     hints:[
       'Both hypotheses are conjunctions once unfolded: <code>h1</code> gives you that <code>hPQ</code> and <code>hR</code> do not overlap and that <code>h</code> is their combination; <code>h2</code> gives the same for <code>hP</code>, <code>hQ</code> and <code>hPQ</code>. The goal asks you to produce a heap and then prove two splittings about it.',
       'The heap to produce can only be the combination of <code>hQ</code> and <code>hR</code>. Having produced it you owe four things: that <code>hP</code> does not overlap it, that <code>h</code> is <code>hP</code> combined with it, that <code>hQ</code> and <code>hR</code> do not overlap, and that it is what it is. Two of those are disjointness facts you have not been given; find where each comes from before writing anything.',
       'Take the hypotheses apart with <code>obtain</code>, then <code>subst</code> the equation that defines <code>hPQ</code>, so that the other disjointness hypothesis stops being about a variable and becomes a statement about a combination. The named facts you then need are Unit 10\'s two bridges, <code>disjoint_union_left</code> and <code>disjoint_union_right</code>, used in opposite directions — <code>.mp</code> on one and <code>.mpr</code> on the other — together with <code>union_assoc</code> for the equation. <code>refine</code> lets you supply the witness and the components you already have in one line and leave the equation as a hole.',
       'After the two <code>obtain</code>s and <code>subst he₂</code>, write <code>obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁</code>. That leaves you holding <code>hP.disjoint hR</code> and <code>hQ.disjoint hR</code>, which are the two facts nothing else could have given you. Then <code>refine</code> with the witness <code>Heap.union hQ hR</code> and one hole, and the hole is the equation.'
     ],
     sol:'theorem splits_assoc {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by\n  obtain ⟨hd₁, he₁⟩ := h1\n  obtain ⟨hd₂, he₂⟩ := h2\n  subst he₂\n  obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁\n  refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR\', rfl⟩⟩\n  rw [he₁, union_assoc]',
     solNote:'Six lines, of which one is an equation and five are bookkeeping about which heaps may stand next to which. If you climbed all four hints and are still stuck, read the solution: the shape is worth more to you than the struggle, and you will write it again in Unit 16.',
     expl:'The proof has three movements. First, the hypotheses are opened and <code>hPQ</code> is eliminated, which is what makes the remaining disjointness hypothesis addressable by a lemma. Second, <code>disjoint_union_left.mp</code> turns "the combination of <code>hP</code> and <code>hQ</code> does not overlap <code>hR</code>" into its two halves, and one of those halves is <code>hQ.disjoint hR</code> — the definedness of the new middle heap, which is what the existential was really claiming. Third, the answer is assembled: the two disjointness components are supplied directly, the last component is <code>rfl</code> because the witness was chosen to make it so, and the only real goal left is the equation, which <code>union_assoc</code> settles with no hypothesis at all.',
     walk:[
       {tac:'obtain ⟨hd₁, he₁⟩ := h1', h:'Replaced the hypothesis <code>h1</code> by its two components. Lean unfolds <code>Heap.splits</code> to find them, exactly as <code>⟨…⟩</code> does when building one.'},
       {tac:'obtain ⟨hd₂, he₂⟩ := h2', h:'The same for the inner splitting. The context now has two disjointness facts and two equations, and no <code>Heap.splits</code> anywhere.'},
       {tac:'subst he₂', h:'Deleted the variable <code>hPQ</code>. <code>he₂ : hPQ = hP.union hQ</code> has a variable on its left, so <code>subst</code> eliminates it and rewrites <code>hd₁</code> and <code>he₁</code>, which both mentioned it. This is the step that makes the next line possible.'},
       {tac:'obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁', h:'Split one hypothesis into two. <code>hd₁ : (hP.union hQ).disjoint hR</code> now matches the lemma, and <code>.mp</code> yields the conjunction <code>hP.disjoint hR ∧ hQ.disjoint hR</code>, which <code>obtain</code> names in one step. The second of those is the fact the whole theorem turns on.'},
       {tac:'refine ⟨Heap.union hQ hR, ⟨…, ?_⟩, ⟨hQR\', rfl⟩⟩', h:'Committed to the witness and filled three of the four components on the spot. <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code> builds <code>hP.disjoint (hQ.union hR)</code> out of the two facts about <code>hP</code>; <code>hQR\'</code> is the extracted disjointness; <code>rfl</code> closes <code>hQ.union hR = hQ.union hR</code>, which is an identity because the witness is literally that term. One hole is left.'},
       {tac:'rw [he₁, union_assoc]', h:'Closed the equation. <code>rw [he₁]</code> replaced <code>h</code> by <code>(hP.union hQ).union hR</code>, leaving precisely the statement of <code>union_assoc</code>; rewriting with it makes both sides identical and the trailing <code>rfl</code> finishes.'}
     ],
     deep:[
       {t:'trace', title:'splits_assoc, down to the last hole',
        start:'h hPQ hP hQ hR : Heap\nh1 : h.splits hPQ hR\nh2 : hPQ.splits hP hQ\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR',
        steps:[
          {tac:'obtain ⟨hd₁, he₁⟩ := h1',
           state:'h hPQ hP hQ hR : Heap\nh2 : hPQ.splits hP hQ\nhd₁ : hPQ.disjoint hR\nhe₁ : h = hPQ.union hR\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR',
           h:'<code>h1</code> is gone and its two halves are in its place. The goal is untouched: nothing in it mentioned <code>h1</code>.'},
          {tac:'obtain ⟨hd₂, he₂⟩ := h2',
           state:'h hPQ hP hQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhe₁ : h = hPQ.union hR\nhd₂ : hP.disjoint hQ\nhe₂ : hPQ = hP.union hQ\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR',
           h:'Four hypotheses, two of them equations. <code>hPQ</code> occurs in three of them and in none of the goal — a variable that exists only to be eliminated.'},
          {tac:'subst he₂',
           state:'h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR',
           h:'<code>hPQ</code> has left the context and both hypotheses that mentioned it have been rewritten. <code>hd₁</code> is now about a combination, which is the only form Unit 10\'s bridge lemmas can read.'},
          {tac:'obtain ⟨hPR, hQR\'⟩ := disjoint_union_left.mp hd₁',
           state:'h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR\' : hQ.disjoint hR\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR',
           h:'The two new lines are the manufactured hypotheses. Nothing was assumed to get them and nothing was case-split; they were inside <code>hd₁</code> all along and the lemma is the tool that reaches in.'},
          {tac:'refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR\', rfl⟩⟩',
           state:'h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR\' : hQ.disjoint hR\n⊢ h = hP.union (hQ.union hR)',
           h:'One goal left out of four, and it is the only one that is about heaps rather than about which heaps may sit beside which. Two rewrites away from done.'}
        ],
        done:'rw [he₁, union_assoc] closes it.'},
       {t:'h4', s:'What the hypotheses are actually for'},
       {t:'p', h:'Keep the equation and throw away <code>hd₁</code>\'s disjointness and the theorem is false. Take <code>hP</code> empty, <code>hQ</code> the one-cell heap <code>Heap.singleton 0 4</code> and <code>hR</code> the one-cell heap <code>Heap.singleton 0 7</code>. The equation still holds — the left-biased combination discards what <code>hR</code> says at an address <code>hQ</code> already claims — and <code>hP</code> and <code>hQ</code> are still disjoint, so <code>h2</code> survives intact.'},
       {t:'code', tag:'illustration', cap:'The equation, with the pieces overlapping. Both branches go through the interface: <code>union_of_some</code> where the left piece speaks, <code>union_of_none</code> where it is silent.',
        src:'example :\n    Heap.union (Heap.union Heap.empty (Heap.singleton 0 4)) (Heap.singleton 0 7)\n      = Heap.singleton 0 4 := by\n  rw [union_empty_left]\n  funext l\n  by_cases hl : l = 0\n  · subst hl\n    rw [union_of_some (Heap.singleton 0 7) (singleton_same 0 4)]\n    exact (singleton_same 0 4).symm\n  · rw [union_of_none (Heap.singleton 0 7) (singleton_other 0 l 4 hl),\n        singleton_other 0 l 7 hl, singleton_other 0 l 4 hl]'},
       {t:'code', tag:'illustration', cap:'And the conclusion fails for those three pieces. The proof reaches straight past the existential and the first splitting to the disjointness the second one demands, which is the one that is false.',
        src:'example : ¬ ∃ hQR, Heap.splits (Heap.singleton 0 4) Heap.empty hQR\n                     ∧ Heap.splits hQR (Heap.singleton 0 4) (Heap.singleton 0 7) := by\n  intro hex\n  obtain ⟨hQR, _, hd, _⟩ := hex\n  exact absurd rfl ((singleton_disjoint_iff 4 7).mp hd)'},
       {t:'p', h:'That is the definedness claim, refuted. Read the two exhibits together and the shape of <code>splits_assoc</code> is clear: the equation part of it is a consequence of <code>union_assoc</code> and holds whatever the pieces do; everything that can fail is disjointness, and all of it fails at once.'}
     ],
     pitfall:'Reaching for <code>disjoint_union_left.mp hd₁</code> before <code>subst he₂</code>. It is the natural order — you have a disjointness, you want its halves — and it fails, because <code>hd₁</code> is about the variable <code>hPQ</code> and the lemma is about a combination. Lean\'s message shows the lemma\'s own heaps as unassigned metavariables, <code>(Heap.union ?m.20 ?m.21).disjoint ?m.22</code>, which is the display\'s way of saying <i>I could not match anything against this pattern</i>. Rewriting with <code>he₂</code> instead of substituting works too, but leaves the dead variable <code>hPQ</code> in the context to trip over later. A second trap waits at the <code>refine</code>. Four proofs have to be supplied, so it is tempting to write them flat — <code>⟨Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hQR\', rfl⟩</code> — but <code>⟨…⟩</code> flattening reassociates to the right and never splits the first field, so the disjointness proof lands where the whole of <code>Heap.splits h hP hQR</code> is wanted: <code>Application type mismatch: The argument disjoint_union_right.mpr ⟨hd₂, hPR⟩ has type hP.disjoint (hQ.union hR) but is expected to have type h.splits hP (hQ.union hR)</code> (line breaks removed), followed by two more errors that are consequences of that one. Bracket the two splittings by hand, <code>⟨w, ⟨_, _⟩, ⟨_, _⟩⟩</code>, and it goes through. Both spellings were compiled.',
     variants:'<code>subst he₁</code> as well, immediately after, and the proof still works: the goal becomes an existential about <code>(hP.union hQ).union hR</code> and the equation component can then be <code>union_assoc hP hQ hR</code> applied directly, with no <code>rw</code> at all. Compiled. Choose the other witness, <code>Heap.union hR hQ</code>, and the proof also goes through, but two components change and both changes are informative: the pair fed to <code>disjoint_union_right.mpr</code> swaps to <code>⟨hPR, hd₂⟩</code>, and the last component stops being <code>rfl</code> — it becomes <code>hR.union hQ = hQ.union hR</code>, discharged by <code>union_comm (disjoint_symm hQR\')</code>, so it now costs a disjointness proof; and the equation goal grows a third rewrite, <code>rw [he₁, union_assoc, union_comm hQR\']</code>. Compiled as well, and it is the sharpest statement of why the witness is a choice rather than a discovery: <code>rfl</code> in the fourth slot is not a fact about heaps, it is a reward for having written the witness the way the goal wanted it. Reverse the two hypotheses (start from a right-bracketed split and produce the left-bracketed one) and the theorem is still true; the proof is the mirror image, line for line, with <code>disjoint_union_right.mp</code> and <code>disjoint_union_left.mpr</code> in place of the two used here. Compiled — and it is exactly what Unit 16\'s second half does.'
    },

    {t:'p', h:'One thing this module has shown you and never proved is that the hypothesis on <code>union_comm</code> cannot be dropped. It is the one law of the algebra that carries a hypothesis at all, so it is the only one that can be broken by taking the hypothesis away.'},

    {t:'ex',
     id:'x26',
     name:'union_not_comm',
     hard:false,
     why:'Your third design exercise, and the second whose statement is a negated universal — Unit 06 refuted the unconditional commutation of erase and write in exactly this shape. What is new is what gets refuted. <code>union_comm</code> carries a disjointness hypothesis, and until this theorem exists you have no citable reason to believe the hypothesis is doing anything; afterwards you do, and every later proof that discharges one is discharging something real.',
     setup:'A design exercise. <b>State and prove that combining two heaps is not commutative in general.</b> The editor starts you with a placeholder rather than a statement; delete it and write your own <code>theorem union_not_comm …</code>. Your own text is what gets checked, so a different correct statement of the same fact passes too — the <i>variants</i> panel names two of them. Unit 10 put the counterexample on the page as two <code>rfl</code> lines; your job is to turn a demonstration into a theorem.',
     goal:'-- Delete the line below and write your own `theorem union_not_comm …`.\n-- Any correct statement of the fact will be accepted.\nexample : True := by',
     hints:[
       'What has to be decided first is where the negation goes. "Not commutative in general" does not mean "for all heaps, the two orders disagree" — that is false, since a heap combined with itself gives the same answer either way. It means: it is not the case that, for all heaps, the two orders agree.',
       'So the statement is a <code>¬</code> wrapped around a <code>∀</code> over two heaps of an equation between combinations. To prove it, assume the universal statement, instantiate it at two heaps you can compute with, apply both sides at one address, and derive an equality between two different values.',
       'The statement to aim at is <code>theorem union_not_comm : ¬ ∀ h₁ h₂ : Heap, Heap.union h₁ h₂ = Heap.union h₂ h₁</code>, and the two heaps that break it are one-cell heaps at the same address holding different values. The tools are Unit 07\'s: <code>intro</code> to assume the universal, <code>congrFun</code> to apply an equation between heaps at a chosen address, <code>union_of_some</code> with <code>singleton_same</code> to evaluate each side, and <code>absurd</code> to finish.',
       'Open with <code>intro h</code>. That leaves <code>⊢ False</code> with <code>h : ∀ (h₁ h₂ : Heap), h₁.union h₂ = h₂.union h₁</code> in the context, and everything after it is a hunt for a contradiction inside <code>h</code>. The next line spends <code>h</code> and picks the address in one go — <code>have h0 := congrFun (h (Heap.singleton 0 4) (Heap.singleton 0 7)) 0</code> — leaving <code>h0</code> an equation between two <code>Option Val</code>s that two rewrites turn into <code>some 4 = some 7</code>.'
     ],
     sol:'theorem union_not_comm :\n    ¬ ∀ h₁ h₂ : Heap, Heap.union h₁ h₂ = Heap.union h₂ h₁ := by\n  intro h\n  have h0 := congrFun (h (Heap.singleton 0 4) (Heap.singleton 0 7)) 0\n  rw [union_of_some (Heap.singleton 0 7) (singleton_same 0 4),\n      union_of_some (Heap.singleton 0 4) (singleton_same 0 7)] at h0\n  exact absurd h0 (by simp)',
     solNote:'If your own statement was different and Lean accepted your proof of it, you were right; the checker runs your text, not this one. Compare the two anyway, because where the negation sits relative to the quantifier is the part that keeps mattering.',
     expl:'The refutation is the four-move idiom from Unit 07 with a combination in place of a lookup: assume the universal claim, choose the two heaps, choose the address, and collide two constructors. The two <code>union_of_some</code> rewrites are what keep the proof inside the interface — each one says "the left argument speaks here, so the combination answers with what it says", and applying that to both orders gives <code>some 4</code> on one side and <code>some 7</code> on the other. The disequality itself is injectivity of <code>some</code> together with <code>4 ≠ 7</code>, and <code>simp</code> supplies both.',
     walk:[
       {tac:'intro h', h:'Turned the negation into an implication into <code>False</code>. The goal became <code>⊢ False</code> and the context gained the universal statement you are going to refute.'},
       {tac:'have h0 := congrFun (h (Heap.singleton 0 4) (Heap.singleton 0 7)) 0', h:'Two instantiations in one line. Applying <code>h</code> to the two heaps gives an equation between two heaps; <code>congrFun … 0</code> applies both sides at address <code>0</code>, giving an equation between two <code>Option Val</code>s.'},
       {tac:'rw [union_of_some …, union_of_some …] at h0', h:'Evaluated both sides through the interface. On the left the first heap speaks at <code>0</code>, so the combination answers <code>some 4</code>; on the right the roles are exchanged and it answers <code>some 7</code>. <code>h0</code> is now <code>some 4 = some 7</code>.'},
       {tac:'exact absurd h0 (by simp)', h:'Collided the two. <code>simp</code> proves <code>¬ (some 4 = some 7)</code> from constructor injectivity, and <code>absurd</code> turns a proposition and its negation into <code>False</code>, which is the goal.'}
     ],
     deep:[
       {t:'trace', title:'From the negation to the collision',
        start:'⊢ ¬∀ (h₁ h₂ : Heap), h₁.union h₂ = h₂.union h₁',
        steps:[
          {tac:'intro h',
           state:'h : ∀ (h₁ h₂ : Heap), h₁.union h₂ = h₂.union h₁\n⊢ False',
           h:'A negation is an implication into <code>False</code>, so <code>intro</code> applies to it. Everything after this is a hunt for a contradiction inside <code>h</code>.'},
          {tac:'have h0 := congrFun (h (Heap.singleton 0 4) (Heap.singleton 0 7)) 0',
           state:'h : ∀ (h₁ h₂ : Heap), h₁.union h₂ = h₂.union h₁\nh0 : (Heap.singleton 0 4).union (Heap.singleton 0 7) 0 = (Heap.singleton 0 7).union (Heap.singleton 0 4) 0\n⊢ False',
           h:'The universal statement has been spent at the two heaps that break it, and the equation between heaps has been applied at the one address where they disagree. Nothing has been evaluated yet.'},
          {tac:'rw [union_of_some …, union_of_some …] at h0',
           state:'h : ∀ (h₁ h₂ : Heap), h₁.union h₂ = h₂.union h₁\nh0 : some 4 = some 7\n⊢ False',
           h:'Both combinations resolved. The hypothesis is now a false equation between two constructor applications, and no heap is left in it.'}
        ],
        done:'exact absurd h0 (by simp) closes it.'},
       {t:'p', h:'The address <code>0</code> is chosen twice over: once when the two singleton heaps are picked, and once when <code>congrFun</code> is applied. Both choices are yours and neither is forced by the goal. That is what makes this a refutation rather than a calculation — a refutation is a witness, and you supply it.'}
     ],
     pitfall:'Writing <code>∀ h₁ h₂ : Heap, Heap.union h₁ h₂ ≠ Heap.union h₂ h₁</code>, with the negation inside the quantifier. It reads like the English and it is false: take both heaps to be <code>Heap.empty</code> and the two combinations are the same heap by <code>rfl</code>, so <code>intro h</code> followed by <code>exact h Heap.empty Heap.empty rfl</code> refutes it (compiled). "Not always equal" and "always unequal" differ by the position of one symbol, and only the first is what <i>not commutative</i> means.',
     variants:'Two other statements are accepted and both were compiled. The existential form <code>∃ h₁ h₂ : Heap, Heap.union h₁ h₂ ≠ Heap.union h₂ h₁</code> is the same proof with the witnesses supplied by a <code>refine</code> at the front instead of an application in the middle, and it is arguably the better statement, because it hands the counterexample to a reader rather than making them dig it out of a proof. The concrete form — <code>Heap.union (Heap.singleton 0 4) (Heap.singleton 0 7) ≠ Heap.union (Heap.singleton 0 7) (Heap.singleton 0 4)</code> — is the weakest of the three and the shortest to prove, being the body of the other two with nothing quantified; it says nothing about heaps in general, which is either honest or useless depending on what you wanted it for. What no correct statement can drop is the collision: the two heaps have to claim the same address, since any two heaps that are disjoint <i>do</i> commute, by <code>union_comm</code>. Move the two singletons to address <code>0</code> and address <code>1</code> and the concrete statement turns false — <code>union_comm ((singleton_disjoint_iff 4 7).mpr (by simp))</code> proves the equation it denies — while the quantified two stay true and lose only this witness. Compiled.'
    },

    /* -------------------------------------------------------- retrospective --- */

    {t:'sec', s:'Retrospective'},

    {t:'detail', title:'Which single law of the algebra needs disjointness, and why only that one?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Commutativity, and among the laws it is the only one. Associativity, both unit laws, idempotence and the two bridge lemmas hold for every pair or triple of heaps with no hypothesis at all. (Cancellation carries two disjointness hypotheses, but it is not one of the laws: it is an extra fact heaps happen to satisfy and partial commutative monoids in general do not.) The reason is that <code>Heap.union</code> resolves a clash by preferring its left argument, and every one of those laws leaves the left-to-right order of the pieces alone: re-bracketing does not reorder, and combining with the empty heap adds nothing to reorder. Commutativity is the one statement that asks what happens when the order changes, so it is the one statement the left bias can answer wrongly — and <code>x26</code> is the proof that it does.'},
      {t:'p', h:'Read the other way: disjointness is not a hypothesis about heaps, it is a hypothesis about the <i>bias</i>. On overlapping heaps the operation makes a choice that mathematics does not license, and disjointness is the assumption that no such choice was ever made.'}
    ]},

    {t:'detail', title:'Why is the equation in splits_assoc free?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Because <code>union_assoc</code> is free. Unit 10 proved that the two bracketings of the total operation are the same heap for every triple, overlapping or not, so the equation component of <code>splits_assoc</code> is settled by a rewrite and a lemma application. Everything else in the proof is about definedness: whether <code>hQ</code> and <code>hR</code> may legitimately stand side by side, and whether <code>hP</code> may stand beside their combination.'},
      {t:'p', h:'That split — a free equation and expensive side conditions — is what makes associativity of a <i>partial</i> operation a different theorem from associativity of the total one it is carved out of. If you ever meet a resource model whose underlying operation is not associative, none of this survives; if you meet one whose operation is associative but whose validity relation does not compose, the equation is still free and the theorem is still false.'}
    ]},

    {t:'detail', title:'If you replaced heaps with something else, what exactly would you have to reprove?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Nothing about addresses, cells, <code>Option</code>, or the left bias: none of them appears in any of these four proofs, because every mention of them was discharged in Units 08 to 10. Take the four proofs apart and what is left are citations of an operation, a unit, a validity relation, and nine laws. Two of those nine — <code>union_empty_left</code> and <code>disjoint_empty_left</code> — are fields of the structure Unit 10 built, and so are both symmetry facts; the two right-hand unit laws are the ones Unit 10 derived from the fields for an arbitrary <code>PCM</code>. So <code>splits_empty_left</code>, <code>splits_empty_right</code> and <code>splits_comm</code> transfer to any partial commutative monoid with the names changed.'},
      {t:'p', h:'<code>splits_assoc</code> does not, and the reason is exact. Its proof cites <code>union_assoc</code> — a field — and <code>disjoint_union_left</code> and <code>disjoint_union_right</code>, which are <i>not</i> fields. Those two say that validity composes across a combination: that <code>a</code> is compatible with the combination of <code>b</code> and <code>c</code> exactly when it is compatible with each of them. Nothing in the eight fields implies that, and Unit 10\'s <code>agreePCM</code> — the read-only-sharing model, which satisfies all eight — is a counterexample:'},
      {t:'code', tag:'illustration', cap:'Unit 10\'s structure, repeated so that this block runs on its own — it is not in the course corpus, only on that page. <code>some 3</code> is compatible with the combination of <code>some 3</code> and <code>some 5</code>, because the left-biased operation makes that combination <code>some 3</code>; it is not compatible with <code>some 5</code>. So the left-to-right half of <code>disjoint_union_right</code> is false in this model, and all eight fields are still filled.',
       src:'def agreePCM : PCM (Option Val) where\n  op         := fun a b => match a with | some v => some v | none => b\n  unit       := none\n  valid      := fun a b => a = none ∨ b = none ∨ a = b\n  op_comm    := by\n    intro a b h\n    rcases h with h | h | h\n    · subst h; cases b <;> rfl\n    · subst h; cases a <;> rfl\n    · subst h; cases a <;> rfl\n  op_assoc   := by intro a b c; cases a <;> rfl\n  unit_left  := fun _ => rfl\n  valid_unit := fun _ => Or.inl rfl\n  valid_comm := by\n    intro a b h\n    rcases h with h | h | h\n    · exact Or.inr (Or.inl h)\n    · exact Or.inl h\n    · exact Or.inr (Or.inr h.symm)\n\nexample : agreePCM.valid (some 3) (agreePCM.op (some 3) (some 5)) := Or.inr (Or.inr rfl)\n\nexample : ¬ agreePCM.valid (some 3) (some 5) := by simp [agreePCM]'},
      {t:'p', h:'So a resource model that wants re-bracketing has to add validity-composition as an axiom; it is not free. A reader who reaches Unit 38 will find the generic connective proved commutative and unital there, and its associativity left standing as one of the things that unit calls undone.'},
      {t:'p', h:'One other thing is lost. Cancellativity — that a heap determines its complement — is a theorem about heaps and not a consequence of those laws, and Unit 10 exhibited a partial commutative monoid where it fails. Nothing on this page needs it, which is the good news; anything later that does need it is a theorem about heaps and not about resources in general.'}
    ]},

    /* -------------------------------------------------------------- closing --- */

    {t:'dod', h:'You can read <code>Heap.splits whole left right</code> as a conjunction, build one with <code>⟨_, _⟩</code> or take one apart in an <code>intro</code> pattern, and say why the logic quantifies over the relation rather than over an operation. You can prove both unit laws as term proofs and say which of the two refuses <code>rfl</code>, and why. You can prove <code>splits_comm</code>, and name the single line where disjointness is spent. You can prove <code>splits_assoc</code>: choose the witness, <code>subst</code> the heap equation before asking for the goals, extract one disjointness with <code>disjoint_union_left.mp</code> and build another with <code>disjoint_union_right.mpr</code>, and close the equation with <code>union_assoc</code>. You can say why that is harder than <code>union_assoc</code> — the associativity of a partial operation is the associativity of the total one plus definedness — and you can state and prove that combination is not commutative, with the negation outside the quantifier.'},

    {t:'p', h:'<code>(Heap, union, empty, disjoint)</code> is a partial commutative monoid, and you can split a heap and re-bracket the pieces. Not one line of this module has mentioned truth, or a proposition about memory, or a program. The logic starts now.'}

  ]
});
