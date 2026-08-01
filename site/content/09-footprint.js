registerChapter({
  id: 'footprint',
  num: '07',
  phase: 'Phase 1 · The resource algebra',
  title: 'How much do you own?',
  blurb: 'Which heaps satisfy "l holds v" — every heap with that cell in it, or the single heap that is that cell? The two answers disagree about whether deallocation can be specified at all, and the disagreement is provable.',

  orient: {
    youWill: [
      'Write the two candidate readings of "<code>l</code> holds <code>v</code>" as two Lean predicates at the type <code>Store → Heap → Prop</code>, and say which is satisfied by one heap and which by unboundedly many.',
      'Exhibit a heap that satisfies one and not the other, and prove both halves.',
      'Refute an equation between two heaps by choosing the address at which they must disagree and applying both sides to it — the pattern every later refutation about heaps is an instance of.',
      'Prove that freeing a cell from a heap that satisfies the loose reading can leave memory non-empty, and say why that counterexample is not vacuous.',
      'Say what the <i>footprint</i> of a claim about memory is, and why a claim that does not pin one down cannot support any promise about what survives a command.'
    ],
    needs: [
      'Unit 06: <code>erase_singleton</code>, and the discipline that a proof about heaps cites the lookup laws rather than unfolding the operations.',
      'Unit 05: the four operations and the six lookup equations, in particular <code>write_same</code>, <code>write_other</code>, <code>singleton_same</code>, <code>singleton_other</code> and <code>erase_other</code>.',
      'Unit 03: <code>congrFun</code> and <code>funext</code>; Unit 02: <code>show</code>, <code>unfold</code> and <code>some_ne_none</code>; Unit 00: that <code>¬P</code> is <code>P → False</code>.'
    ],
    payoff: 'Unit 13 defines the assertion <code>l ↦ v</code> and it is the exact reading, not the loose one; this page is the argument that makes that definition the only available choice. Unit 23 states every rule of the logic in terms of the smallest heap a command touches, and points back to exercise <code>x18</code> for what would otherwise be false.'
  },

  blocks: [

    /* ---------------------------------------------------------- the question --- */

    {t:'p', h:'Holding one cell is the smallest claim there is to make about memory, and Unit 06 proved a fact of exactly that shape.'},

    {t:'code', tag:'verified', cap:'Free the cell you hold, and nothing is left.',
     src:'theorem erase_singleton (l : Loc) (v : Val) :\n    Heap.erase (Heap.singleton l v) l = Heap.empty := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]'},

    {t:'p', h:'Read it as a promise about a program: you hold the cell <code>l</code>, you deallocate it, you are left holding nothing. That is what a specification of deallocation ought to say, and this is the theorem that would make it true. What stops it from being that specification is the heap it is about — <code>Heap.singleton l v</code>, the heap consisting of the cell <code>l</code> and nothing else. A command runs in whatever memory the program has, and that is not one cell. So the promise has to be made about every heap in which <i>l holds v</i>, and there the sentence divides. The loose reading: every heap that maps <code>l</code> to <code>v</code>, whatever it does elsewhere. The exact reading: the one heap that maps <code>l</code> to <code>v</code> and is undefined at every other address. On paper that difference reads as emphasis. Written in Lean it is two predicates, and they can be told apart by a proof.'},

    /* ------------------------------------------------------------ two readings --- */

    {t:'sec', s:'Two readings, two predicates'},

    {t:'anat', tag:'verified',
     src:'def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v\ndef ptsExactly (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h = Heap.singleton l v',
     parts:[
       {m:'Store → Heap → Prop', h:'A claim about memory is a function from the state to a proposition, and the state is a store together with a heap. Nothing in it is new — <code>Store</code> and <code>Heap</code> are Unit 00\'s abbreviations, and a claim is a function into <code>Prop</code> because that is where propositions live. It has no name yet. Unit 12 gives it one, and from there on the course writes the name instead of the arrow chain.'},
       {m:'fun _ h', h:'The store is bound and discarded — <code>_</code> is what you call a binder you are not going to use. Neither reading says anything about program variables. The argument is there because a claim about memory has to be a claim about the state a command runs in, and later claims will use both halves of it.'},
       {m:'h l = some v', h:'The whole of the loose reading. Look <code>l</code> up in <code>h</code>; the answer is <code>v</code>. What <code>h</code> answers at any other address is unconstrained, so a heap with a million other cells in it satisfies this exactly as well as the one-cell heap does.'},
       {m:'h = Heap.singleton l v', h:'The whole of the exact reading, and it is an equation between two heaps rather than between two lookups. It does not say what <code>h</code> holds at <code>l</code> and stop; it says which function <code>h</code> <i>is</i>. Exactly one heap satisfies it.'}
     ]},

    {t:'cmp',
     left: {t:'<code>ptsAtLeast</code> — at least this much',
       h:'Satisfied by unboundedly many heaps: the one-cell heap, that heap with a hundred more cells beside it, the entire memory of a running program provided <code>l</code> is in it holding <code>v</code>. It licenses one thing — reading <code>l</code>. It says nothing whatever about how much of memory is yours, which is the reading of a precondition as <i>a fact that happens to be true here</i>.'},
     right:{t:'<code>ptsExactly</code> — exactly this much',
       h:'Satisfied by one heap. It licenses reading <code>l</code>, and it also licenses the statement that nothing else is there, which is a statement about the whole of memory. The cost is that to claim two cells you must describe both of them, so a claim about a large heap has to be assembled out of claims about its pieces.'}},

    {t:'p', h:'One direction between them is free, and it costs two rewrites.'},

    {t:'code', tag:'illustration', cap:'The exact reading implies the loose one. <code>σ</code> is a store, and neither side looks at it.',
     src:'example (l : Loc) (v : Val) (σ : Store) (h : Heap) (hp : ptsExactly l v σ h) :\n    ptsAtLeast l v σ h := by\n  show h l = some v\n  rw [hp, singleton_same]'},

    {t:'p', h:'Both lines lean on the same fact — that a definition is transparent to the checker — one of them on the goal and one on a hypothesis. <code>show</code> replaces the goal <code>ptsAtLeast l v σ h</code> by <code>h l = some v</code>, which Lean accepts because reduction goes through a definition and a lambda: to the checker those two propositions are one. <code>rw [hp]</code> is the same transparency used on a hypothesis — <code>hp</code> is typed <code>ptsExactly l v σ h</code>, and <code>rw</code> looks through the definition to find the equation <code>h = Heap.singleton l v</code> underneath, rewrites <code>h</code> away, and leaves a lookup in a one-cell heap for <code>singleton_same</code>. The converse is the direction with content, and settling it needs a heap that satisfies the loose reading and fails the exact one.'},

    /* ------------------------------------------------------------- two cells --- */

    {t:'sec', s:'A heap with two cells'},

    {t:'code', tag:'verified', cap:'Cell 4 holds 3, cell 9 holds 7, every other address is unallocated.',
     src:'def twoCells : Heap := Heap.write (Heap.singleton 4 3) 9 7'},

    {t:'p', h:'It is built out of the operations rather than written as a bare conditional, and that is not decoration: the six lookup laws are stated about <code>Heap.write</code> and <code>Heap.singleton</code>, so a heap written this way is one the laws can be aimed at. The write at 9 is on the outside, so a lookup at 9 stops there and answers <code>some 7</code>; a lookup anywhere else falls through it to the one-cell heap underneath.'},

    {t:'ex',
     id:'x16', name:'a two-cell heap satisfies the loose reading', hard:false,
     why:'Everything on this page rests on the loose reading being satisfied by something other than the one-cell heap, and this is that fact, proved rather than asserted. It is also the half of exercise <code>x18</code> that keeps it from being a refutation of nothing — a rule no heap satisfies the precondition of cannot be broken by any heap. And it is the first lookup in a heap you can point at that goes through the interface Unit 06 closed: two of the six lookup laws, cited by name, with neither <code>Heap.write</code> nor <code>Heap.singleton</code> opened.',
     setup:'<code>twoCells</code>, <code>ptsAtLeast</code> and the six lookup equations are in scope. The store argument can be anything, so it is <code>fun _ => 0</code>, the store that answers 0 for every variable.',
     goal:'example : ptsAtLeast 4 3 (fun _ => 0) twoCells := by',
     hints:[
       'Unfolded, the goal is <code>twoCells 4 = some 3</code>: one lookup, at address 4, in the heap <code>Heap.write (Heap.singleton 4 3) 9 7</code>. Nothing is being claimed about address 9, and nothing is being claimed about the store.',
       'The write is at 9 and the lookup is at 4, so the write is transparent and the lookup falls through to the heap underneath — which is the one-cell heap holding 3 at 4, read at its own address. Two facts, in that order, and the first needs to know that 4 and 9 are different addresses.',
       'Two laws and nothing clever. The laws are <code>write_other</code>, which says a write is invisible away from its own address, and <code>singleton_same</code>; the tactics that spend them are <code>show</code>, <code>unfold</code> and <code>rw</code>. <code>write_other</code> wants the disequality between the two addresses handed to it as an argument, so park it in the context first with <code>have</code> — <code>simp</code> proves that one on its own.',
       'The first line is <code>have hne : (4 : Loc) ≠ 9 := by simp</code>. It leaves the goal untouched at <code>⊢ ptsAtLeast 4 3 (fun x => 0) twoCells</code> and adds <code>hne : 4 ≠ 9</code> to the context. <code>(4 : Loc)</code> is the numeral with its type written on it; <code>Loc</code> is <code>Nat</code>, so Lean would have settled on that type unasked, and the label is documentation saying which <code>4</code> this is. From there <code>show twoCells 4 = some 3</code> and <code>unfold twoCells</code> bring the goal to <code>⊢ (Heap.singleton 4 3).write 9 7 4 = some 3</code>, and one <code>rw</code> finishes it.'
     ],
     sol:'example : ptsAtLeast 4 3 (fun _ => 0) twoCells := by\n  have hne : (4 : Loc) ≠ 9 := by simp\n  show twoCells 4 = some 3\n  unfold twoCells\n  rw [write_other (Heap.singleton 4 3) 9 4 7 hne, singleton_same]',
     solNote:'<code>unfold twoCells</code> is not a breach of the rule that heap operations stay folded. <code>twoCells</code> is a name for a particular heap, not one of the four operations; unfolding it exposes the operations, and from there the proof cites laws and never looks inside <code>Heap.write</code> or <code>Heap.singleton</code>.',
     expl:'The proof is the two-cell heap read at the address that is not the one it was most recently written at. <code>write_other</code> is the law that says a write is invisible away from its own address, and it is the only line that spends the disequality between 4 and 9. What it leaves is a lookup in <code>Heap.singleton 4 3</code> at 4, which is <code>singleton_same</code>, and <code>rw</code>\'s trailing <code>rfl</code> closes <code>some 3 = some 3</code>.',
     walk:[
       {tac:'have hne : (4 : Loc) ≠ 9 := by simp', h:'Put the disequality in the context before it is wanted. <code>(4 : Loc)</code> is the numeral with its type written on it — the labelling <code>pp.numericTypes</code> turns on. It changes nothing here, because <code>Loc</code> is <code>Nat</code> and Lean infers that unasked; it records which <code>4</code> is meant, and the goal display drops it again.'},
       {tac:'show twoCells 4 = some 3', h:'Restated the goal as a definitionally equal one. <code>ptsAtLeast 4 3 σ twoCells</code> reduces to this by unfolding the definition and applying the lambda; the goal did not change, its display did, and now it is a lookup rather than an application of a predicate.'},
       {tac:'unfold twoCells', h:'Replaced the name by the heap it stands for, so the goal reads <code>(Heap.singleton 4 3).write 9 7 4 = some 3</code>. The head of the left-hand side is now <code>Heap.write</code>, which is what <code>write_other</code> matches.'},
       {tac:'rw [write_other (Heap.singleton 4 3) 9 4 7 hne, singleton_same]', h:'The first rewrite discarded the write and left <code>Heap.singleton 4 3 4 = some 3</code>. The second turned the left-hand side into <code>some 3</code>, and the trailing <code>rfl</code> closed it. The four arguments before <code>hne</code> are the heap, the written address, the read address and the value, in the order <code>write_other</code> declares them; the goal fixes all four, so <code>_</code> in place of each would do. What the goal does not fix is <code>hne</code>: write <code>rw [write_other]</code> with nothing supplied and the rewrite fires and then hands <code>⊢ 4 ≠ 9</code> back as a second goal.'}
     ],
     deep:[
       {t:'trace', title:'Four lines, four goals',
        start:'⊢ ptsAtLeast 4 3 (fun x => 0) twoCells',
        steps:[
          {tac:'have hne : (4 : Loc) ≠ 9 := by simp',
           state:'hne : 4 ≠ 9\n⊢ ptsAtLeast 4 3 (fun x => 0) twoCells',
           h:'The goal is untouched; the context gained the one fact the proof will spend. The store <code>fun _ => 0</code> prints as <code>fun x => 0</code>, because the binder had to be given a name to be printed.'},
          {tac:'show twoCells 4 = some 3',
           state:'hne : 4 ≠ 9\n⊢ twoCells 4 = some 3',
           h:'The same proposition, displayed as the lookup it is.'},
          {tac:'unfold twoCells',
           state:'hne : 4 ≠ 9\n⊢ (Heap.singleton 4 3).write 9 7 4 = some 3',
           h:'The definition is gone and both operations are visible. This is the goal the lookup laws are about.'},
          {tac:'rw [write_other (Heap.singleton 4 3) 9 4 7 hne]',
           state:'hne : 4 ≠ 9\n⊢ Heap.singleton 4 3 4 = some 3',
           h:'The write at 9 was read at 4 and answered nothing, so it vanished and the heap underneath is exposed. This is where the two addresses being different is used, and it is used once.'},
          {tac:'rw [singleton_same]', state:'No goals.', h:'A one-cell heap read at its own address.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Two shorter proofs exist and each gives something up. <code>rfl</code> closes this goal on its own: every address in the statement is a numeral, so Lean settles <code>4 = 9</code> by computation and reduces both sides to <code>some 3</code>. What that proves is a fact about three particular numbers, and it stops the moment one of them becomes a variable. <code>simp [ptsAtLeast, twoCells, Heap.write, Heap.singleton]</code> closes it too, and unlike <code>rfl</code> it survives the move to variables — but only if the disequality goes into the bracket beside the definitions. Leave it out on the variable statement below and <code>simp</code> unfolds everything, gets as far as it can, and hands back <code>⊢ l = l\' → w = v</code>: the branch it could not rule out, stated as a bill. Either way it works by unfolding the two operations, which is what closing the interface in Unit 06 was for. The four lines above name two laws and look inside nothing, so they survive both changes: variables in place of numerals, and a different definition of <code>Heap.write</code>.'},
       {t:'code', tag:'illustration', cap:'The same four lines with the numerals replaced by variables, and the disequality now a hypothesis rather than something <code>simp</code> can check. <code>rfl</code> does not close this one: with nothing left in the statement to compute, it falls back to comparing the last two arguments of <code>ptsAtLeast l v</code> and reports <code>The left-hand side σ is not definitionally equal to the right-hand side (Heap.singleton l v).write l\' w</code>.',
        src:'example (l l\' : Loc) (v w : Val) (σ : Store) (hne : l ≠ l\') :\n    ptsAtLeast l v σ (Heap.write (Heap.singleton l v) l\' w) := by\n  show Heap.write (Heap.singleton l v) l\' w l = some v\n  rw [write_other (Heap.singleton l v) l\' l w hne, singleton_same]'}
     ],
     pitfall:'Getting the disequality the wrong way round. <code>write_other</code> is stated with the hypothesis <code>hne : x ≠ l</code> — read address first, written address second — so proving <code>(9 : Loc) ≠ 4</code> instead and handing it over gives <code>Application type mismatch: The argument hne has type 9 ≠ 4 but is expected to have type 4 ≠ 9</code>, and then a second error saying the goal is still open. The two propositions are interchangeable by <code>Ne.symm</code> and are not the same term; the message names both, which is the fastest way to see which order a lemma wants.',
     variants:'Change the value and the claim becomes false: <code>¬ ptsAtLeast 4 5 (fun _ => 0) twoCells</code> holds instead, and every line of this proof reappears in it pointed at a hypothesis. The one new joint is the <code>show</code>, which can only be pointed at a goal; after <code>intro h</code> the same definitional step is made by restating the hypothesis at the type you want it, <code>have h4 : twoCells 4 = some 5 := h</code>. <code>unfold twoCells at h4</code> and the two rewrites <code>at h4</code> then leave <code>h4 : some 3 = some 5</code>, which <code>simp at h4</code> closes. Change the address to the outer cell and the claim is true again but shorter — <code>ptsAtLeast 9 7 (fun _ => 0) twoCells</code> needs only <code>write_same</code>, because the lookup is at the address the write was made at and never reaches the heap underneath. Drop the <code>have</code> and the disequality does not disappear, it moves: <code>rw [write_other]</code> fires and leaves <code>⊢ 4 ≠ 9</code> behind for <code>simp</code>. Drop it from the version with variables above and there is nothing to prove towards, because that statement is false — take <code>l</code> and <code>l\'</code> equal and <code>w</code> different from <code>v</code>, and the write on top answers <code>some w</code> where the claim wants <code>some v</code>. Reaching for the other law with a write on the left does not help either: <code>write_same</code>\'s pattern is <code>Heap.write ?h ?l ?v ?l</code> — the same address twice — so aiming it at a write at 9 read at 4 gives <code>Did not find an occurrence of the pattern</code>.'
    },

    /* -------------------------------------------------------- the refutation --- */

    {t:'p', h:'Half of the separation is established. The other half is the claim that <code>twoCells</code> is <i>not</i> the one-cell heap, and that is a different kind of statement. The positive claim was settled by computation, because every address in it is a numeral. Aim the same tactic at the negative one.'},

    {t:'code', tag:'sketch', cap:'The first thing to try.',
     src:'example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by\n  simp [ptsExactly, twoCells, Heap.write, Heap.singleton]'},

    {t:'state', cap:'What it leaves, with the <code>file:line:column</code> prefix dropped here and everywhere on this page. Two further warnings follow, reporting <code>Heap.write</code> and <code>Heap.singleton</code> as unused arguments.',
     src:'error: unsolved goals\n⊢ ¬(Heap.singleton 4 3).write 9 7 = Heap.singleton 4 3'},

    {t:'p', h:'The unused arguments are the diagnosis. <code>simp</code> unfolded <code>ptsExactly</code> and <code>twoCells</code>, arrived at a negated equation between two functions, and stopped — neither heap operation was ever applied to an address, so neither definition had anything to rewrite. Two functions are unequal when they differ <i>somewhere</i>, and no tactic will choose the somewhere for you. That choice is the entire content of the proof, and it is the same choice every refutation about heaps in this course comes down to.'},

    {t:'steps', title:'Refuting an equation between heaps',
     items:[
       {k:'Assume it', h:'<code>intro h</code>. A disequality is an implication into <code>False</code>, so the equation you want to refute becomes a hypothesis and the goal becomes <code>False</code>. Nothing has been decided yet; you have swapped a negative goal for a positive assumption.'},
       {k:'Choose the address', h:'The step with content. Look at the two heaps and find one address at which they answer differently. It is never the address the statement is about — at that address they agree, which is what makes the claim non-trivial in the first place.'},
       {k:'Apply both sides there', h:'<code>congrFun h x</code> takes an equation between two functions and produces the equation between their values at <code>x</code>: two terms of type <code>Option Val</code>, which is a type with two constructors and no equations between them.'},
       {k:'Reduce, and collide the constructors', h:'Each side is a lookup in a heap built by the operations, so the lookup laws take both apart. Aim for <code>some _ = none</code>, and hand it to <code>some_ne_none</code>, which is exactly the statement that those two constructors are different.'}
     ]},

    {t:'p', h:'It returns wherever two heaps have to be told apart. Unit 13 uses it to show that a heap holding one cell is not the empty heap, writing the third move as a rewrite by the assumed equation rather than as a <code>congrFun</code>. Unit 14 uses it to refute the rule that would let you forget half of what you hold, and the address it applies both sides at is the cell being forgotten. Unit 31 runs it forwards instead of backwards: <code>congrFun</code> at an arbitrary address followed by <code>erase_other</code> — the two steps of exercise <code>x18</code> — to prove that a heap whose erasure at <code>l</code> is empty must have been the one cell <code>l</code> all along.'},

    {t:'ex',
     id:'x17', name:'it does not satisfy the exact reading', hard:false,
     why:'This is the proof that the two readings are different predicates rather than two ways of saying one thing, so it is the proof that the question this unit asks is a real question. The shape — assume, apply at a chosen point, collide two constructors — is the one you will use in Units 13, 14 and 31, where the heaps are abstract and the address is the only thing you get to choose.',
     setup:'The same context as before. The four moves above, in order; the third of them is <code>congrFun</code>, which Unit 03 introduced as the converse of <code>funext</code>.',
     goal:'example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by',
     hints:[
       'Unfolded, the goal is <code>twoCells = Heap.singleton 4 3 → False</code>: assume the two-cell heap is the one-cell heap, and derive a contradiction. Both sides are functions of type <code>Loc → Option Val</code>, so the assumption says they agree at every address.',
       'Two functions that are equal are equal everywhere, so it is enough to find one address where they cannot be. Address 4 is not it — both answer <code>some 3</code> there, and that is what the loose reading already established. Address 9 is: the two-cell heap answers <code>some 7</code>, and a one-cell heap at 4 answers nothing at 9.',
       '<code>intro</code>, then <code>congrFun</code> at the address you chose, then the lookup laws on the resulting hypothesis — <code>write_same</code> for the left-hand side and <code>singleton_other</code> for the right — and <code>some_ne_none</code> to turn the collision into <code>False</code>. <code>rw … at</code> aims a rewrite at a hypothesis rather than at the goal.',
       '<code>intro h</code> leaves <code>h : ptsExactly 4 3 (fun x => 0) twoCells</code> and <code>⊢ False</code>. Then <code>have h9 := congrFun h 9</code> gives <code>h9 : twoCells 9 = Heap.singleton 4 3 9</code> — the assumption, read at one address.'
     ],
     sol:'example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by\n  intro h\n  have hne : (9 : Loc) ≠ 4 := by simp\n  have h9 := congrFun h 9\n  unfold twoCells at h9\n  rw [write_same, singleton_other 4 9 3 hne] at h9\n  exact some_ne_none 7 h9',
     solNote:'<code>congrFun h 9</code> is applied to a hypothesis whose type is <code>ptsExactly 4 3 (fun x => 0) twoCells</code> rather than a visible equation. Lean reduces through the definition to find the <code>=</code>, the same transparency <code>show</code> and <code>rw [hp]</code> used earlier.',
     expl:'The whole proof is the choice of 9. Everything after it is bookkeeping: the left-hand side is a write at 9 read at 9, which is <code>write_same</code> and answers <code>some 7</code>; the right-hand side is a one-cell heap at 4 read at 9, which is <code>singleton_other</code> and answers <code>none</code>. The two constructors of <code>Option</code> are distinct, so the hypothesis is absurd and <code>some_ne_none 7</code> — the statement <code>some 7 ≠ none</code> — takes it to <code>False</code>. Had you chosen 4 instead, both sides would have reduced to <code>some 3</code> and the hypothesis would have been true.',
     walk:[
       {tac:'intro h', h:'Turned the negation into an assumption. <code>h</code> is the claim that the two heaps are equal, and the goal is now <code>False</code>.'},
       {tac:'have hne : (9 : Loc) ≠ 4 := by simp', h:'The disequality <code>singleton_other</code> will want, in the orientation it wants it: read address first.'},
       {tac:'have h9 := congrFun h 9', h:'Spent the assumption at one address. This is the only line that uses <code>h</code>, and the address in it is the whole of the argument: <code>h9 : twoCells 9 = Heap.singleton 4 3 9</code>.'},
       {tac:'unfold twoCells at h9', h:'Exposed the operations inside the hypothesis, giving <code>h9 : (Heap.singleton 4 3).write 9 7 9 = Heap.singleton 4 3 9</code>. <code>at h9</code> is what points the tactic at a hypothesis instead of at the goal.'},
       {tac:'rw [write_same, singleton_other 4 9 3 hne] at h9', h:'Two rewrites in one call, both aimed at <code>h9</code>. The first collapsed the left-hand side to <code>some 7</code>; the second collapsed the right-hand side to <code>none</code>, leaving <code>h9 : some 7 = none</code>. Neither rewrite touched the goal, which is still <code>False</code>.'},
       {tac:'exact some_ne_none 7 h9', h:'<code>some_ne_none 7</code> has type <code>some 7 ≠ none</code>, which is <code>some 7 = none → False</code>; applying it to <code>h9</code> is a term of type <code>False</code>, which is the goal.'}
     ],
     deep:[
       {t:'trace', title:'The assumption, spent at one address',
        start:'⊢ ¬ptsExactly 4 3 (fun x => 0) twoCells',
        steps:[
          {tac:'intro h',
           state:'h : ptsExactly 4 3 (fun x => 0) twoCells\n⊢ False',
           h:'The negation is gone from the goal and the equation is in the context.'},
          {tac:'have hne : (9 : Loc) ≠ 4 := by simp  then  have h9 := congrFun h 9',
           state:'h : ptsExactly 4 3 (fun x => 0) twoCells\nhne : 9 ≠ 4\nh9 : twoCells 9 = Heap.singleton 4 3 9\n⊢ False',
           h:'The choice of address, made. From here nothing is decided; both sides only have to be reduced.'},
          {tac:'unfold twoCells at h9',
           state:'h : ptsExactly 4 3 (fun x => 0) twoCells\nhne : 9 ≠ 4\nh9 : (Heap.singleton 4 3).write 9 7 9 = Heap.singleton 4 3 9\n⊢ False',
           h:'A write at 9 read at 9 on the left, a one-cell heap at 4 read at 9 on the right. One law each.'},
          {tac:'rw [write_same] at h9',
           state:'h : ptsExactly 4 3 (fun x => 0) twoCells\nhne : 9 ≠ 4\nh9 : some 7 = Heap.singleton 4 3 9\n⊢ False',
           h:'The left-hand side answers what was written there. The heap that was written into was never examined.'},
          {tac:'rw [singleton_other 4 9 3 hne] at h9',
           state:'h : ptsExactly 4 3 (fun x => 0) twoCells\nhne : 9 ≠ 4\nh9 : some 7 = none\n⊢ False',
           h:'Two distinct constructors of <code>Option Val</code>, standing on either side of an equals sign. The proof is finished; the last line only says so to Lean.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The same proof with 4 chosen instead of 9 — the address the two heaps agree at.',
        src:'example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by\n  intro h\n  have hne : (4 : Loc) ≠ 9 := by simp\n  have h4 := congrFun h 4\n  unfold twoCells at h4\n  rw [write_other (Heap.singleton 4 3) 9 4 7 hne, singleton_same] at h4'},
       {t:'state', cap:'Every step succeeds and the proof is nowhere. The hypothesis is true, so no further rewriting will ever make it absurd.',
        src:'error: unsolved goals\nh : ptsExactly 4 3 (fun x => 0) twoCells\nhne : 4 ≠ 9\nh4 : some 3 = some 3\n⊢ False'}
     ],
     pitfall:'Choosing the address the statement is about. At 4 both heaps answer <code>some 3</code>, every rewrite still fires, and you arrive at <code>h4 : some 3 = some 3</code> with the goal untouched — a proof that has gone somewhere and achieved nothing. The tactics give no warning, because nothing went wrong: a true hypothesis was derived from a hypothesis. The address at which two heaps differ has to be found by looking at the two heaps, and there is no tactic for it. The second mistake is mechanical and announces itself: drop <code>unfold twoCells at h9</code> and the next line fails with <code>Did not find an occurrence of the pattern Heap.write ?h ?l ?v ?l in the target expression twoCells 9 = Heap.singleton 4 3 9</code>. <code>congrFun h 9</code> saw straight through the definition of <code>ptsExactly</code> on the line before, so it is natural to expect <code>rw</code> to see through <code>twoCells</code> here. It does not: <code>rw</code> matches the term as written, and what is written is a name.',
     variants:'Drop the outer write from <code>twoCells</code> and the claim becomes false: <code>ptsExactly 4 3 (fun _ => 0) (Heap.singleton 4 3)</code> is closed by <code>rfl</code>, and the <code>congrFun</code> attack now fails at every address, which is what refuting a true statement feels like. Reverse the equation, so the goal is <code>¬ (Heap.singleton 4 3 = twoCells)</code>, and every line still works with the two sides swapped, except the last: <code>congrFun</code> does not care which way round an equation is, but <code>some_ne_none</code> does, so the final line becomes <code>exact some_ne_none 7 h9.symm</code>. Replace <code>Heap.singleton 4 3</code> by <code>Heap.singleton 9 7</code> in the statement and 9 stops being a witness — both heaps answer <code>some 7</code> there — while 4 becomes one, reducing to <code>some 3 = none</code>.'
    },

    {t:'p', h:'So the two readings are two predicates, and a heap separates them. Which of the two to adopt is still open, and adopting one is a choice — a definition is judged by which theorems survive it, and the theorem to try these two against is the one this unit opened with.'},

    /* ------------------------------------------------------------- the test --- */

    {t:'sec', s:'The test: can deallocation be specified?'},

    {t:'txt', cap:'The specification of deallocation, in the shape Unit 22 makes precise: a claim about memory before, a command, a claim about memory after. The only thing at issue here is what the left-hand claim means.',
     src:'    {  l holds v  }      free l      {  memory is empty  }'},

    {t:'p', h:'Under the exact reading the rule is a theorem, and its proof is <code>erase_singleton</code> with one rewrite in front of it. The precondition says the heap <i>is</i> the cell being freed, the rewrite replaces it by that cell, and the theorem does the rest.'},

    {t:'code', tag:'illustration', cap:'The free rule under the exact reading. Two rewrites, and the second is Unit 06\'s theorem unchanged.',
     src:'example (l : Loc) (v : Val) (σ : Store) (h : Heap) (hp : ptsExactly l v σ h) :\n    Heap.erase h l = Heap.empty := by\n  rw [hp, erase_singleton]'},

    {t:'p', h:'Under the loose reading the precondition is satisfied by <code>twoCells</code> — that is exercise <code>x16</code>, at address 4 with value 3. So if the rule holds under that reading it holds of <code>twoCells</code> in particular, and the heap left behind after freeing cell 4 is the empty heap. Cell 9 is still holding 7.'},

    {t:'ex',
     id:'x18', name:'after free, the heap is not empty', hard:false,
     why:'This is the refutation the unit exists to produce: under the loose reading the rule for deallocation is false, and you are the one who proved it. Every later appeal to exactness — Unit 13\'s definition of <code>l ↦ v</code>, Unit 23\'s insistence that a rule mention only the memory it touches — rests on this exercise, and points back at it by name.',
     setup:'Nothing new: the four moves of the refutation idiom, with <code>erase_other</code> in place of <code>singleton_other</code>. One lookup on this page needs no law at all, and finding which is part of the exercise.',
     goal:'example : Heap.erase twoCells 4 ≠ Heap.empty := by',
     hints:[
       'The goal is <code>Heap.erase twoCells 4 = Heap.empty → False</code>. On the left, the two-cell heap with cell 4 deallocated; on the right, the heap that is undefined everywhere. The claim is that those two are not the same function.',
       'The erase was at 4, so it left address 9 alone, and address 9 is holding 7. The empty heap holds nothing at 9. That is the address the two functions differ at, and it is the address that was never mentioned in the precondition — which is the point of the exercise.',
       'Assume, apply at 9 with <code>congrFun</code>, and then take the left-hand side apart in two steps: <code>erase_other</code> to get past the erase, and <code>write_same</code> to read the write. The right-hand side needs no lemma — <code>Heap.empty 9</code> reduces to <code>none</code> on its own, and <code>exact</code> checks up to reduction.',
       '<code>intro h</code> leaves <code>h : twoCells.erase 4 = Heap.empty</code> and <code>⊢ False</code>; then <code>have h9 := congrFun h 9</code> gives <code>h9 : twoCells.erase 4 9 = Heap.empty 9</code>, an equation between two lookups.'
     ],
     sol:'example : Heap.erase twoCells 4 ≠ Heap.empty := by\n  intro h\n  have hne : (9 : Loc) ≠ 4 := by simp\n  have h9 := congrFun h 9\n  rw [erase_other twoCells 4 9 hne] at h9\n  unfold twoCells at h9\n  rw [write_same] at h9\n  exact some_ne_none 7 h9',
     solNote:'The last line closes a goal about <code>Heap.empty 9</code> using a lemma about <code>none</code>. Nothing bridges them but reduction: <code>Heap.empty</code> is <code>fun _ => none</code>, so <code>Heap.empty 9</code> and <code>none</code> are the same term to Lean, and <code>exact</code> checks types up to that. This is why the empty heap needed no lookup law of its own in Unit 05.',
     expl:'Freeing cell 4 does nothing at address 9 — that is <code>erase_other</code>, the law that an erase is transparent away from its own address — so the left-hand side is whatever <code>twoCells</code> answers at 9, which is <code>some 7</code> by <code>write_same</code>. The right-hand side is <code>none</code>. The precondition never said anything about address 9, the command never touched it, and the postcondition claims it is gone: the failure is exactly the gap between what the precondition pinned down and what the postcondition asserts.',
     walk:[
       {tac:'intro h', h:'The disequality became a hypothesis and the goal became <code>False</code>.'},
       {tac:'have hne : (9 : Loc) ≠ 4 := by simp', h:'The disequality <code>erase_other</code> wants, read address first.'},
       {tac:'have h9 := congrFun h 9', h:'The assumed equation between heaps, applied at 9. Every remaining line works on <code>h9</code>.'},
       {tac:'rw [erase_other twoCells 4 9 hne] at h9', h:'Removed the erase from the left-hand side, leaving <code>h9 : twoCells 9 = Heap.empty 9</code>. The erase was at 4 and the reading is at 9, so it contributed nothing — which is the mathematical content of the counterexample.'},
       {tac:'unfold twoCells at h9', h:'Exposed the operations, giving <code>(Heap.singleton 4 3).write 9 7 9</code> on the left. It comes after the previous line rather than before it because <code>erase_other</code> matches whatever heap it is given, and giving it the name is shorter than giving it the definition.'},
       {tac:'rw [write_same] at h9', h:'The write at 9, read at 9, answers what was written: <code>h9 : some 7 = Heap.empty 9</code>.'},
       {tac:'exact some_ne_none 7 h9', h:'<code>Heap.empty 9</code> reduces to <code>none</code>, so <code>h9</code> is a proof of <code>some 7 = none</code>, and <code>some_ne_none 7</code> turns it into <code>False</code>.'}
     ],
     deep:[
       {t:'trace', title:'The cell nobody mentioned',
        start:'⊢ twoCells.erase 4 ≠ Heap.empty',
        steps:[
          {tac:'intro h  then  have hne  then  have h9 := congrFun h 9',
           state:'h : twoCells.erase 4 = Heap.empty\nhne : 9 ≠ 4\nh9 : twoCells.erase 4 9 = Heap.empty 9\n⊢ False',
           h:'The equation, read at 9. <code>twoCells.erase 4</code> is how Lean prints <code>Heap.erase twoCells 4</code>.'},
          {tac:'rw [erase_other twoCells 4 9 hne] at h9',
           state:'h : twoCells.erase 4 = Heap.empty\nhne : 9 ≠ 4\nh9 : twoCells 9 = Heap.empty 9\n⊢ False',
           h:'The command is gone from the hypothesis. What is left says: the two-cell heap at 9, and the empty heap at 9, are equal.'},
          {tac:'unfold twoCells at h9  then  rw [write_same] at h9',
           state:'h : twoCells.erase 4 = Heap.empty\nhne : 9 ≠ 4\nh9 : some 7 = Heap.empty 9\n⊢ False',
           h:'<code>some 7</code> against a heap that is <code>none</code> everywhere. Nothing further needs rewriting; the last line is a type check.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'Aiming <code>simp</code> at it, with every definition in the bracket.',
        src:'example : Heap.erase twoCells 4 ≠ Heap.empty := by\n  simp [twoCells, Heap.erase, Heap.write, Heap.singleton, Heap.empty]'},
       {t:'state', cap:'The name <code>twoCells</code> was unfolded and nothing else happened. Four warnings follow, one for each heap operation, reporting it as an unused argument.',
        src:'error: unsolved goals\n⊢ ¬((Heap.singleton 4 3).write 9 7).erase 4 = Heap.empty'},
       {t:'p', h:'Nothing in the goal tells a tactic which address to name, which is why move two of the idiom has no Lean in it.'},
       {t:'code', tag:'illustration', cap:'The rule itself, refuted in one statement rather than in two halves. <code>hpre</code> is exercise <code>x16</code>, <code>hrule</code> applied to it is the rule doing what it promises, and everything from <code>h9</code> down is this exercise. <code>Ne.symm hne</code> converts the disequality one half wants into the orientation the other half wants, which is the only line that exists because the two are being glued.',
        src:'example : ¬ (∀ (l : Loc) (v : Val) (σ : Store) (h : Heap),\n    ptsAtLeast l v σ h → Heap.erase h l = Heap.empty) := by\n  intro hrule\n  have hne : (4 : Loc) ≠ 9 := by simp\n  have hpre : ptsAtLeast 4 3 (fun _ => 0) twoCells := by\n    show twoCells 4 = some 3\n    unfold twoCells\n    rw [write_other (Heap.singleton 4 3) 9 4 7 hne, singleton_same]\n  have hpost := hrule 4 3 (fun _ => 0) twoCells hpre\n  have h9 := congrFun hpost 9\n  rw [erase_other twoCells 4 9 (Ne.symm hne)] at h9\n  unfold twoCells at h9\n  rw [write_same] at h9\n  exact some_ne_none 7 h9'}
     ],
     pitfall:'Choosing address 4, where the command was. <code>erase_same</code> takes the left-hand side to <code>none</code>, the right-hand side is <code>none</code>, and the hypothesis is <code>none = Heap.empty 4</code>. Handing that to <code>some_ne_none</code> gives <code>Application type mismatch: The argument h4 has type none = Heap.empty 4 but is expected to have type some 7 = none</code>. The command did exactly what it promised at the address it was given; the counterexample lives at the address nobody mentioned.',
     variants:'Free cell 9 instead of 4 and the claim is still true, with 4 as the witness and <code>write_other</code> and <code>singleton_same</code> doing the reducing — the two cells are symmetric in this respect. Free both, and the claim reverses: <code>Heap.erase (Heap.erase twoCells 4) 9 = Heap.empty</code> is provable, by <code>funext</code> and a split on each of the two addresses. That is the shape of the repair the exact reading makes — you may promise memory is empty afterwards exactly when the precondition accounted for all of it.'
    },

    {t:'p', h:'To refute "for every heap satisfying the precondition, the postcondition holds afterwards" you need a heap that satisfies the precondition and for which the postcondition fails. Exercise <code>x16</code> is the first half and exercise <code>x18</code> is the second, about the same heap. Without the first half the refutation would be of nothing: had no heap satisfied the loose precondition, the rule would have been true vacuously — useless rather than false, and nothing would follow about which reading to take.'},

    {t:'detail', title:'Could the loose reading be repaired instead?', open:false,
     blocks:[
       {t:'p', h:'Two repairs suggest themselves, and pricing them is what leaves exactness as the only move.'},
       {t:'p', h:'<b>Weaken the postcondition.</b> Do not promise memory is empty; promise only that <code>l</code> is unallocated. That is true under the loose reading — and it is true for a reason that destroys it.'},
       {t:'code', tag:'illustration', cap:'The weakened rule. The proof does not mention the precondition.',
        src:'example (l : Loc) (σ : Store) (h : Heap) (hp : ptsAtLeast l 3 σ h) :\n    Heap.erase h l l = none := erase_same h l'},
       {t:'state', cap:'Lean\'s report on the binder <code>hp</code>. The <code>Note:</code> line about disabling the linter is dropped.',
        src:'warning: Variable name `hp` is not explicitly referenced.\n\nThe binding can be removed (if unused) or named `_` (if used implicitly).'},
       {t:'p', h:'The precondition is never referenced, because <code>erase_same</code> holds of every heap whatever. A rule whose proof ignores its precondition tells you nothing you did not know before running the command, and in particular it never lets you conclude that a program gave back everything it took: after <code>n</code> deallocations you would know <code>n</code> addresses are unallocated and still nothing about the rest of memory.'},
       {t:'p', h:'<b>Add a clause.</b> Keep the loose reading and conjoin "and nothing else is allocated". That works, and it is the exact reading with more words.'},
       {t:'code', tag:'illustration', cap:'The two clauses together imply the exact reading: <code>funext</code>, then a split on the address, with the first clause answering at <code>l</code> and the second answering everywhere else. The converse holds too, by the same two lookup laws used the other way.',
        src:'example (l : Loc) (v : Val) (σ : Store) (h : Heap)\n    (hat : ptsAtLeast l v σ h) (hrest : ∀ x, x ≠ l → h x = none) :\n    ptsExactly l v σ h := by\n  show h = Heap.singleton l v\n  funext x\n  by_cases hx : x = l\n  · rw [hx, singleton_same]\n    exact hat\n  · rw [singleton_other l x v hx]\n    exact hrest x hx'},
       {t:'p', h:'So the second repair is not an alternative to exactness, it is a longer spelling of it — and a worse one, because the clause it adds is a <code>∀</code> over all addresses, which every later proof would have to carry and instantiate. <code>ptsExactly</code> says the same thing as a single equation between heaps, which <code>rw</code> can use in one step. That is the whole argument for stating it as an equation.'}
     ]},

    /* ------------------------------------------------------------- footprint --- */

    {t:'sec', s:'Footprint'},

    {t:'defn', term:'Footprint',
     h:'The <b>footprint</b> of a claim about memory is the part of memory the claim pins down. Under the exact reading, the footprint of <i>l holds v</i> is the single cell <code>l</code>, and the claim determines the heap completely. Under the loose reading there is no such part, and so no footprint: the claim fixes what is stored at <code>l</code> but not how far the heap extends, and it is satisfied by heaps of every size.',
     cap:'Posed here. Unit 13 makes the choice into a definition, and Unit 23 shows what it buys.'},

    {t:'p', h:'That is what exercise <code>x18</code> is about, stated in general. A specification is a claim about the state before and a claim about the state after. If the claim before does not determine how much memory there is, the claim after cannot describe what is left, because what is left depends on what was there — and the counterexample is always the same one: the cell nobody mentioned. Exactness is the price of being able to say anything at all about memory after a command runs.'},

    {t:'note', kind:'key', title:'The choice, and where it is spent',
     h:'From here on this course reads a claim about memory in the first person: <i>this is what I hold</i>, not <i>this is what happens to be true</i>. That is the register in which a rule can be stated about the smallest heap a command touches — the discipline Unit 23 is named after, and the reason its rules are short enough to compose.'},

    {t:'dod', h:'You can write the two readings of <i>l holds v</i> as Lean predicates at <code>Store → Heap → Prop</code> and say how many heaps satisfy each. You can exhibit a heap that separates them and prove both halves, citing lookup laws rather than unfolding operations. You can refute an equation between two heaps by naming the address at which they differ, applying both sides to it with <code>congrFun</code>, and colliding <code>some</code> against <code>none</code> — and you can say why choosing the wrong address produces a true hypothesis and no proof. You can state the rule for deallocation, prove it under the exact reading, refute it under the loose one, and say why the refutation is not vacuous. You can say what a footprint is and why a claim without one supports no promise about what survives.'},

    {t:'p', h:'The exact reading survives the test and the loose one does not, so <code>l ↦ v</code> is going to mean <i>the heap is this one cell</i>. But then an assertion talks about all of the memory it holds, so combining two of them means cutting memory in two — and nothing you have can cut a heap.'}

  ]
});
