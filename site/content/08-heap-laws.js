registerChapter({
  id: 'heap-laws',
  num: '06',
  phase: 'Phase 1 · The resource algebra',
  title: 'Equations between heaps',
  blurb: 'Eleven equations close the interface. Four fall out of one schema, three are commutation laws, and the two of those that carry a disequality are what the frame rule is made of.',

  orient: {
    youWill: [
      'Prove an equation between two whole heaps with the three moves you already have, and say what <code>heap_ext</code> adds to <code>funext</code>.',
      'Read one schema — a second operation at <code>l</code> leaves no trace of the first — and instantiate it four ways for four of the eleven laws.',
      'Prove <code>write_comm</code> by hand and point at the one line where the disequality is spent.',
      'Refute the same statement with its disequality dropped, by applying both sides at a single address.',
      'Say which laws need a disequality and which do not, and predict which from what the two operations put at a shared address.',
      'Choose between <code>simp</code>, hand-driven <code>rw [if_pos]</code> and citing the lookup laws by name — and see <code>unfold</code> leave a term <code>rw</code> cannot match.'
    ],
    needs: [
      'Unit 05: the four definitions and the six lookup equations, and the rule that from Unit 07 on the definitions are not unfolded.',
      'Unit 04: <code>funext</code>, <code>by_cases</code>, <code>&lt;;&gt;</code>, and the rule for choosing <code>simp</code> over hand-driven <code>rw</code>.',
      'Unit 03: <code>if_pos</code> and <code>if_neg</code>, <code>congrFun</code>, <code>Ne.symm</code>, <code>unfold</code>, <code>simp only</code>.'
    ],
    payoff: 'Unit 23\'s rules for assignment and deallocation are <code>write_singleton</code> and <code>erase_singleton</code> with a triple wrapped around them — three lines each, no case split. Unit 25\'s proof that <code>Heap.write</code> is local runs two of this page\'s proof shapes again at the scale of a whole frame heap, and Unit 27 turns locality into the frame rule.'
  },

  blocks: [

    /* ------------------------------------------------------------- brief --- */

    {t:'p', h:'Writing twice to the same cell, and writing to two different cells. Neither question is about a single lookup, so neither is settled by the six equations you proved last unit: each one is an equation between two whole <i>heaps</i>, and a heap is a function. You have proved equations between functions already — <code>update_shadow</code> and <code>update_comm</code> were exactly that — and the three moves that did it are the three moves here, with one type changed. The principle behind the first of them has a name at this type, and it is the statement every proof on this page is an instance of.'},

    {t:'code', tag:'verified', cap:'<code>funext</code> with <code>Loc → Option Val</code> filled in. No proof below cites it: the tactic does the same job in one step, and naming the theorem is for the reader rather than for Lean.',
     src:'theorem heap_ext {h₁ h₂ : Heap} (h : ∀ l, h₁ l = h₂ l) : h₁ = h₂ := funext h'},

    {t:'p', h:'Eleven equations and the interface is closed. Four of them come out of a single schema and can be written down before any of them is proved. Three are commutation laws, and two of those three carry a disequality — which is the fact the frame rule will be built from, twenty-one units from here. Two of them, <code>write_singleton</code> and <code>erase_singleton</code>, are the whole content of Unit 23\'s rules for assignment and deallocation; they are proved here, in the heap layer, so that Unit 23 can be three lines and do no pointwise reasoning inside a Hoare proof. That layering is the working discipline of the rest of the course, and this is where it starts. There is no new tactic on this page. The vocabulary is now sufficient, and what a lab like this adds is judgement about which member of it to reach for.'},

    /* ----------------------------------------------------- worked example --- */

    {t:'sec', s:'One theorem, three proofs'},

    {t:'p', h:'Take the smallest interesting equation between heaps: writing <code>w</code> at <code>l</code> into the one-cell heap holding <code>v</code> at <code>l</code> gives the one-cell heap holding <code>w</code> at <code>l</code>. It is small enough that three different proofs of it fit on one page, and the three differ in ways that decide how every later proof is written.'},

    {t:'code', tag:'sketch', cap:'Three attempts, in the order a reader tries them. All three fail, and each failure says something different.',
     src:'example (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := rfl\n\nexample (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  simp [Heap.write, Heap.singleton]\n\nexample (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  simp [Heap.write, Heap.singleton]'},

    {t:'state', cap:'The three errors, in order. The <code>file:line:column</code> prefix is dropped here and everywhere on this page.',
     src:'error: Type mismatch\n  rfl\nhas type\n  ?m.3 = ?m.3\nbut is expected to have type\n  (Heap.singleton l v).write l w = Heap.singleton l w\n\nerror: `simp` made no progress\n\nerror: unsolved goals\nl : Loc\nv w : Val\nx : Loc\n⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none'},

    {t:'p', h:'Read them in order. <code>rfl</code> fails because the two sides are functions built by different chains of <code>if</code>, and reduction cannot get inside a conditional whose condition mentions the variable <code>x</code> that <code>funext</code> has not yet produced. Bare <code>simp</code> fails harder: with no <code>funext</code> there is no address to test, so neither <code>Heap.write</code> nor <code>Heap.singleton</code> has an argument to be applied to and nothing rewrites at all. The third is the informative one. <code>funext x</code> was supplied, both definitions were unfolded, and what survives is an equation between two conditionals with the same undecided condition. <code>simp</code> does not split an <code>if</code> whose condition it cannot settle; it needs to be told which side of <code>x = l</code> it is on. That is the case split, and it is the second of the three moves.'},

    {t:'code', tag:'verified', cap:'The proof. Three moves, two of them on one line.',
     src:'theorem write_singleton (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]'},

    {t:'trace', title:'Route one: the goal, pointwise, twice',
     start:'l : Loc\nv w : Val\n⊢ (Heap.singleton l v).write l w = Heap.singleton l w',
     steps:[
       {tac:'funext x',
        state:'l : Loc\nv w : Val\nx : Loc\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x',
        h:'An equation between two heaps becomes an equation between two <code>Option Val</code>s at an arbitrary address <code>x</code>. Everything after this is about one address.'},
       {tac:'by_cases hx : x = l',
        state:'case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x',
        h:'The first of two goals. The statement has not changed; what changed is that <code>hx</code> is now available to settle every condition in it.'},
       {tac:'simp [Heap.write, Heap.singleton, hx]', state:'No goals.',
        h:'Unfold both operations, rewrite <code>x</code> to <code>l</code> using <code>hx</code>, collapse three conditionals on <code>l = l</code>, and close <code>some w = some w</code>.'},
       {tac:'(case neg)',
        state:'case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x',
        h:'The second goal, reached by the <code>&lt;;&gt;</code>. The same text, and a hypothesis pointing the other way.'},
       {tac:'simp [Heap.write, Heap.singleton, hx]', state:'No goals.',
        h:'Same call, opposite branches: all three conditionals collapse to their else-branch, leaving <code>none = none</code>.'}
     ],
     done:'No goals.'},

    {t:'p', h:'The two branches want the same text, so <code>&lt;;&gt;</code> earns its place and the proof is two lines. Now the same theorem with the conditionals driven by hand, which is what Unit 04\'s rule says to do when the branches diverge — here they do not, so this route is longer on purpose, to show what the short one is hiding.'},

    {t:'code', tag:'illustration', cap:'Route two. <code>simp only [Heap.write, Heap.singleton]</code> unfolds and stops; every step after it is a named rewrite.',
     src:'example (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  simp only [Heap.write, Heap.singleton]\n  by_cases hx : x = l\n  · rw [if_pos hx, if_pos hx]\n  · rw [if_neg hx, if_neg hx, if_neg hx]'},

    {t:'trace', title:'Route two: three conditionals, taken down one at a time',
     start:'l : Loc\nv w : Val\nx : Loc\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x',
     steps:[
       {tac:'simp only [Heap.write, Heap.singleton]',
        state:'l : Loc\nv w : Val\nx : Loc\n⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none',
        h:'Three conditionals: the write on the left, the singleton nested inside its else-branch, and the singleton on the right. This is the goal <code>simp</code> alone got stuck on, reached deliberately.'},
       {tac:'rw [if_pos hx]  (case pos)',
        state:'case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ some w = if x = l then some w else none',
        h:'<code>if_pos</code> takes a <i>proof of the condition</i> and rewrites the first conditional it matches — the outer one on the left — to its then-branch. The nested singleton went with the else-branch that was discarded.'},
       {tac:'rw [if_pos hx]', state:'No goals.',
        h:'The only conditional left is the one on the right. Collapsing it leaves <code>some w = some w</code>, and <code>rw</code>\'s trailing <code>rfl</code> closes it.'},
       {tac:'rw [if_neg hx]  (case neg)',
        state:'case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then some v else none) = if x = l then some w else none',
        h:'The else-branch this time, so the nested singleton is exposed rather than discarded. That is why this branch needs three rewrites and the other needed two.'},
       {tac:'rw [if_neg hx]',
        state:'case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ none = if x = l then some w else none',
        h:'The exposed singleton, gone. <code>rw</code> always takes the leftmost match, which is why the same text can be written three times and mean three different conditionals.'},
       {tac:'rw [if_neg hx]', state:'No goals.', h:'And the right-hand side, leaving <code>none = none</code>.'}
     ],
     done:'No goals.'},

    {t:'cmp',
     left: {t:'Route one — <code>simp</code>', kind:'good', tag:'sketch',
       h:'Two lines. The <code>&lt;;&gt;</code> is available because the two branches want the same call. Nothing in the proof records <i>where</i> the hypothesis was spent: <code>hx</code> goes into a bracket and <code>simp</code> decides what to do with it. That is the right trade when the route is not the content.',
       src:'funext x\nby_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]'},
     right:{t:'Route two — <code>rw [if_pos]</code> / <code>rw [if_neg]</code>', tag:'sketch',
       h:'Five lines, and each conditional is named as it falls. The asymmetry — two rewrites on one side, three on the other — is visible, and it is a real fact about the statement: at <code>l</code> the write hides the singleton, away from <code>l</code> it does not. Route one proves the theorem and conceals that.',
       src:'funext x\nsimp only [Heap.write, Heap.singleton]\nby_cases hx : x = l\n· rw [if_pos hx, if_pos hx]\n· rw [if_neg hx, if_neg hx, if_neg hx]'}},

    {t:'p', h:'Both routes unfold the definitions, and there is a third that does not. Unit 05 left six lookup equations with the promise that they replace the definitions; the third route takes the promise literally and cites them by name.'},

    {t:'code', tag:'illustration', cap:'Route three. Neither <code>Heap.write</code> nor <code>Heap.singleton</code> appears in a bracket; the four lemmas are Unit 05\'s.',
     src:'example (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  by_cases hx : x = l\n  · rw [hx, write_same, singleton_same]\n  · rw [write_other (Heap.singleton l v) l x w hx, singleton_other l x v hx,\n        singleton_other l x w hx]'},

    {t:'trace', title:'Route three: the positive branch, through the interface',
     start:'case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x',
     steps:[
       {tac:'rw [hx]',
        state:'case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ (Heap.singleton l v).write l w l = Heap.singleton l w l',
        h:'Rewriting with the hypothesis itself replaces <code>x</code> by <code>l</code> throughout, which puts both reads <i>at</i> the write point — the shape <code>write_same</code> and <code>singleton_same</code> match.'},
       {tac:'rw [write_same]',
        state:'case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ some w = Heap.singleton l w l',
        h:'The left-hand side is gone in one step, and the heap it was written into — <code>Heap.singleton l v</code> — was never examined. That is what <code>write_same</code> being unconditional in <code>h</code> means.'},
       {tac:'rw [singleton_same]', state:'No goals.',
        h:'And the right-hand side, leaving <code>some w = some w</code>.'}
     ],
     done:'No goals.'},

    {t:'p', h:'The negative branch is the mirror image: <code>write_other</code> turns the left-hand side into a read of <code>Heap.singleton l v</code>, and two uses of <code>singleton_other</code> turn both remaining reads into <code>none</code>. The explicit arguments are there because those two lemmas take the read point as an argument and nothing in the goal forces it — Lean must be told that <code>x</code> is the point and <code>hx</code> is the proof.'},

    {t:'p', h:'Three routes, one verdict. Route three is the only one whose text survives an edit to the definitions: write <code>Heap.write</code> with the conditional the other way round, or with the equation flipped to <code>l = x</code>, and routes one and two both break while route three does not mention the definition at all. Unit 38 changes the model outright, and what survives it is exactly what was proved through the interface. Reuse is the habit, and the eleven equations below exist so that later proofs have something to reuse.'},

    {t:'detail', title:'Then why does the proof above put <code>Heap.write</code> in a <code>simp</code> bracket?', open:false,
     blocks:[
       {t:'p', h:'Unit 05 closed with a rule: the four definitions do not go into a <code>simp</code> bracket again. The proof of <code>write_singleton</code> puts two of them there, and ten of the eleven proofs of the laws below name at least one — in a <code>simp</code> bracket, in a <code>simp only</code>, or in an <code>unfold</code>. That is not an oversight, and pretending otherwise would leave you with a rule you cannot trust.'},
       {t:'p', h:'The rule has one exception and this unit is it. While the algebra of an operation is still being established, the definition is the only thing there is to argue from: an equation between whole heaps cannot be derived from six lookup laws unless some proof somewhere connects the lookup laws to the operation, and that proof has to look at the operation. What the rule forbids is unfolding <i>after</i> the algebra exists — in a proof about programs, or assertions, or splitting, where a heap operation appears as a step and its definition is an implementation detail. From Unit 07 on, no proof in this course unfolds <code>Heap.write</code>, <code>Heap.erase</code> or <code>Heap.singleton</code>. Route three is a demonstration that even here it is avoidable; the corpus proofs take the shorter road because this is the last page on which the shorter road is allowed.'},
       {t:'p', h:'<code>Heap.empty</code> is outside the rule, and stays usable in a bracket for the rest of the course. It has no conditional to unfold and no lookup law of its own, so naming it can only take <code>Heap.empty x</code> to <code>none</code> — which is a step Unit 05 showed is <code>rfl</code>. Two later proofs take exactly that step and nothing else.'},
       {t:'p', h:'The one lemma below whose corpus proof is written route-three style is <code>write_of_eq</code>, exercise <code>x14</code>, and the reason is not tidiness: its hypothesis is about the heap rather than about the address, so <code>simp</code> has nothing to collapse and the lookup laws are what move the goal.'}
     ]},

    /* ---------------------------------------------------------- schema --- */

    {t:'sec', s:'Four laws from one schema'},

    {t:'p', h:'Before proving anything, look at what has to be true. Both <code>Heap.write</code> and <code>Heap.erase</code> decide what happens at <code>l</code> in their then-branch, and neither consults the heap it is given there. So if two of them are applied at the <i>same</i> address, one after the other, the second decides the answer at that address and the first is invisible. Away from <code>l</code> both are transparent. Two operations, two positions, four instances.'},

    {t:'txt', cap:'One schema, four instances, four theorems. <code>‥</code> stands for the value argument, which a write has and an erase does not. The names on the right are the ones the course uses; three of the four are exercises below.',
     src:'    OP₂ ( OP₁ h l ‥ ) l ‥   =   OP₂ h l ‥\n\n    OP₁      OP₂       the law                                        name\n    ─────────────────────────────────────────────────────────────────────────────────\n    write    write     (h.write l v₁).write l v₂  =  h.write l v₂     write_shadow\n    write    erase     (h.write l v ).erase l     =  h.erase l        erase_write_same\n    erase    write     (h.erase l   ).write l v   =  h.write l v      write_erase_same\n    erase    erase     (h.erase l   ).erase l     =  h.erase l        erase_erase'},

    {t:'p', h:'Each of the four is one instance of a single fact about the then-branch, and each has the same two-line proof. Two more come from the same source with <code>h</code> taken to be <code>Heap.empty</code>. Writing into the empty heap makes a one-cell heap — that is <code>write_empty</code> — so the first row read at <code>Heap.empty</code> is <code>write_singleton</code>. The second row read there gives <code>(Heap.singleton l v).erase l = Heap.empty.erase l</code>, and erasing from a heap with nothing in it changes nothing, so the right-hand side collapses and the line becomes <code>erase_singleton</code>. What is <i>not</i> an instance of the schema is anything involving two different addresses, which is where the rest of the unit goes.'},

    /* ------------------------------------------------------- exercises --- */

    {t:'sec', s:'The laws'},

    {t:'ex',
     id:'m1-5', name:'write_shadow', hard:false,
     why:'Last write wins. Unit 23\'s rule for <code>[l] := e</code> carries an old value in its precondition and no trace of it in its postcondition, and what licenses the disappearance is this equation at <code>h = Heap.empty</code> — which is <code>write_singleton</code>, two exercises down. Proving the general row first is what makes that one free. It is also the first row of the schema, so proving it is proving the pattern the next three follow.',
     setup:'The three moves, and one <code>simp</code> call that has to serve both branches. The editor starts you at <code>:= by</code>.',
     goal:'theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by',
     hints:[
       'Both sides are heaps, so the goal is an equation between two functions of type <code>Loc → Option Val</code>. Unfolded and read at an address <code>x</code>, the left is <code>if x = l then some v₂ else (if x = l then some v₁ else h x)</code> and the right is <code>if x = l then some v₂ else h x</code>. Nothing is assumed about <code>h</code>.',
       'Fix an address and ask what each side answers there. At <code>l</code> both give <code>v₂</code>, because the outer write decides and the inner one is inside the branch that is discarded. Away from <code>l</code> both writes are transparent and both sides are whatever <code>h</code> answers. Two addresses, two arguments, and the second is the same on both sides.',
       'Three tactics, and all three are in <code>update_shadow</code>: <code>funext</code> to produce the address, <code>by_cases</code> to settle <code>x = l</code>, <code>simp</code> to collapse what the split has decided. Before writing the third, ask Unit 04\'s question — do the two branches want the same call, or different ones? The answer decides whether <code>&lt;;&gt;</code> is available or two focus dots are needed.',
       'The first line is <code>funext x</code>, and it leaves <code>⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x</code> with <code>x : Loc</code> in the context. One more line finishes: split on <code>x = l</code>, and hand both branches to a single <code>simp</code> whose bracket carries <code>Heap.write</code> and the case hypothesis. Leave the hypothesis out of that bracket and both branches survive, still carrying an undecided <code>if x = l</code>.'
     ],
     sol:'theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, hx]',
     solNote:'Character for character the proof of <code>update_shadow</code>, with <code>update</code> replaced by <code>Heap.write</code>. The <code>Option</code> in the codomain cost nothing here, because neither branch ever produces a <code>none</code>.',
     expl:'Only one of the two branches has any content. At <code>x = l</code> the outer write answers <code>some v₂</code> on both sides and the inner write is sitting in the else-branch that the outer conditional throws away — that is where "last write wins" lives, and it is a fact about the <i>shape</i> of the definition, not about heaps. At <code>x ≠ l</code> every conditional takes its else-branch and both sides reduce to <code>h x</code>, so the equation is <code>h x = h x</code>. The two branches want the same call — unfold, settle the condition, take a branch — so <code>simp</code> with <code>hx</code> in the bracket serves both and <code>&lt;;&gt;</code> is the right combinator.',
     walk:[
       {tac:'funext x', h:'Turned an equation between two heaps into an equation between their values at an arbitrary <code>x</code>, and put <code>x</code> in the context to split on. Without it there is no conditional to work with, because the <code>if</code> inside <code>Heap.write</code> only appears once the function is applied.'},
       {tac:'by_cases hx : x = l', h:'Produced two goals with identical statements and opposite hypotheses, <code>hx : x = l</code> and <code>hx : ¬x = l</code>. Each conditional in the goal mentions exactly the proposition <code>hx</code> settles, which is why one split does for all three of them.'},
       {tac:'<;> simp [Heap.write, hx]', h:'Ran the same call on both goals. In the positive branch it rewrote <code>x</code> to <code>l</code>, turned all three conditions into <code>True</code>, took the then-branches and closed <code>some v₂ = some v₂</code>. In the negative branch it turned them into <code>False</code>, took the else-branches and closed <code>h x = h x</code>.'}
     ],
     deep:[
       {t:'trace', title:'The positive branch, one rewrite at a time',
        start:'case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x',
        steps:[
          {tac:'simp only [Heap.write]',
           state:'case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then some v₂ else if x = l then some v₁ else h x) = if x = l then some v₂ else h x',
           h:'Both writes unfolded and both applications carried out. Three conditionals, one undecided condition, repeated.'},
          {tac:'simp only [hx]',
           state:'case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (if True then some v₂ else if True then some v₁ else h l) = if True then some v₂ else h l',
           h:'The hypothesis, spent: <code>x</code> becomes <code>l</code>, so each condition becomes <code>l = l</code>, which <code>simp</code> settles to <code>True</code> without being asked.'},
          {tac:'simp only [↓reduceIte]', state:'No goals.',
           h:'Then-branches taken. <code>some v₂ = some v₂</code>, and the inner write — the value <code>v₁</code> — was discarded unexamined.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The negative branch runs the same three steps and reaches <code>(if False then some v₂ else if False then some v₁ else h x) = if False then some v₂ else h x</code>, which collapses to <code>h x = h x</code>. Both writes are transparent there, which is the half of the statement that has nothing to do with shadowing.'},
       {t:'code', tag:'sketch', cap:'The bracket without <code>hx</code>. Both goals survive, unchanged in shape and undecided in condition.',
        src:'example (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write]'},
       {t:'state', src:'error: unsolved goals\ncase pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then some v₂ else if x = l then some v₁ else h x) = if x = l then some v₂ else h x\n\ncase neg\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then some v₂ else if x = l then some v₁ else h x) = if x = l then some v₂ else h x'}
     ],
     pitfall:'Splitting on the wrong thing. <code>by_cases hv : v₁ = v₂</code> is a legal move, and <code>&lt;;&gt; simp [Heap.write, hv]</code> after it leaves two goals rather than none. The negative branch is the unfolded statement with its conditionals still standing; the positive branch is <code>⊢ x = l → ¬x = l → some v₂ = h x</code>, where <code>simp</code> has pulled both conditions out as <i>antecedents</i> instead of deciding them, because nothing in the context says which way <code>x = l</code> goes. That residue is true and <code>simp</code> will not close it. The conditional in <code>Heap.write</code> tests the <i>address</i>, so the address is what a case split has to be about. The general rule for the whole page: split on exactly the proposition the definitions test.',
     variants:'Move the two writes to different addresses and the statement is false: instantiate <code>¬ ∀ (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val), Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write h l₂ v₂</code> at <code>Heap.empty</code>, <code>0</code>, <code>1</code>, <code>5</code>, <code>6</code> and apply both sides at <code>0</code> — the left answers <code>some 5</code>, which the outer write at <code>1</code> left alone, and the right answers <code>none</code>. The correct statement for different addresses is <code>write_comm</code>, two exercises down, and it needs a hypothesis. Swap the order of the two values, so that the goal reads <code>Heap.write h l v₁</code> on the right, and the proof fails in the positive branch alone, at <code>⊢ v₂ = v₁</code> — <code>simp</code> collapses every conditional and then strips both <code>some</code>s, and what is left is exactly the false part. The negative branch still closes, so the two branches diverge, and <code>&lt;;&gt;</code> would be the wrong combinator even if the statement were repairable.'
    },

    {t:'p', h:'Second row of the schema, with the outer operation changed from a write to an erase.'},

    {t:'ex',
     id:'m1-6', name:'erase_write_same', hard:false,
     why:'Writing to a cell and then freeing it is the same as freeing it: a write that is undone leaves nothing behind. That is the second row of the schema, and the exercise is here as much for the other thing it teaches — which operations have to go into a <code>simp</code> bracket, including the one whose value the conclusion has no room for. Get that wrong and <code>simp</code> stops and hands you back a lookup. Reading a stuck goal that way, and answering it with a lookup law rather than a definition, is how every proof in Unit 25 is written.',
     setup:'Same three moves. Both operations have to be told to <code>simp</code>, even though the value the write stored never appears in the conclusion.',
     goal:'theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.erase (Heap.write h l v) l = Heap.erase h l := by',
     hints:[
       'Read both sides at an address <code>x</code>. The left is <code>if x = l then none else (if x = l then some v else h x)</code> — the erase decides first, and the write is inside the branch it discards. The right is <code>if x = l then none else h x</code>. The value <code>v</code> appears on the left and not on the right.',
       'At <code>l</code> both sides are <code>none</code>: the erase overrides whatever the write put there. Away from <code>l</code> the erase is transparent, and so is the write — but now you need to know that, so the write cannot be ignored.',
       'The same three moves as <code>write_shadow</code>, in the same order and with the same combinator. What changes is the bracket. <code>simp</code> unfolds only what it is handed, so count the operations occurring anywhere in the goal — including the one that is sitting inside a branch rather than at the head — and add the case hypothesis.',
       'The first line is <code>funext x</code>, leaving <code>⊢ (h.write l v).erase l x = h.erase l x</code>. Then split on <code>x = l</code> and give both branches one <code>simp</code> under <code>&lt;;&gt;</code>, with three entries in the bracket. Drop <code>Heap.write</code> from it and the positive branch closes while the negative one stops at <code>⊢ h.write l v x = h x</code>.'
     ],
     sol:'theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.erase (Heap.write h l v) l = Heap.erase h l := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]',
     expl:'The two branches divide the work unevenly, and the division is the lesson. At <code>l</code> the outer erase answers <code>none</code> on both sides and the write is in the discarded branch, so <code>Heap.write</code> is not needed at all — this is the schema, and it is where "the write is undone" lives. Away from <code>l</code> the erase is transparent on both sides and what is left is <code>Heap.write h l v x = h x</code>, which is <code>write_other</code>: a genuine fact about the write, needing the disequality. So the write is invisible in the conclusion and indispensable in the proof, and it is the branch where nothing interesting happens that needs it.',
     walk:[
       {tac:'funext x', h:'Equation between heaps to equation between lookups at <code>x</code>.'},
       {tac:'by_cases hx : x = l', h:'Two goals. Both conditionals in the goal test <code>x = l</code>, so one split settles both.'},
       {tac:'<;> simp [Heap.erase, Heap.write, hx]', h:'Positive branch: both sides collapse to <code>none</code> and <code>Heap.write</code> in the bracket does nothing. Negative branch: both erases collapse to their else-branch, leaving <code>Heap.write h l v x = h x</code>, and <code>Heap.write</code> with <code>hx</code> takes that to <code>h x = h x</code>.'}
     ],
     deep:[
       {t:'trace', title:'The two branches from the same unfolded goal',
        start:'h : Heap\nl : Loc\nv : Val\n⊢ (h.write l v).erase l = h.erase l',
        steps:[
          {tac:'funext x  then  by_cases hx : x = l',
           state:'case pos\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (h.write l v).erase l x = h.erase l x',
           h:'The positive goal, before anything is unfolded.'},
          {tac:'simp only [Heap.erase, Heap.write]',
           state:'case pos\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then none else if x = l then some v else h x) = if x = l then none else h x',
           h:'Three conditionals again. The write sits in the else-branch of the erase, which is why it survives to be printed and not to be used.'},
          {tac:'simp [hx]', state:'No goals.',
           h:'Then-branches on both sides: <code>none = none</code>. The subterm <code>some v</code> was never touched.'},
          {tac:'(case neg)  simp only [Heap.erase, Heap.write]',
           state:'case neg\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then none else if x = l then some v else h x) = if x = l then none else h x',
           h:'Identical text, opposite hypothesis.'},
          {tac:'simp [hx]', state:'No goals.',
           h:'Else-branches everywhere, and the inner conditional — the write — has to be collapsed too. That is the step the previous branch did not need.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The bracket without <code>Heap.write</code>, to see which branch depends on it.',
        src:'example (h : Heap) (l : Loc) (v : Val) :\n    Heap.erase (Heap.write h l v) l = Heap.erase h l := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, hx]'},
       {t:'state', cap:'One goal of two survives, and it is the negative branch. The residue is <code>write_other</code>, unproved because <code>Heap.write</code> was withheld.',
        src:'error: unsolved goals\ncase neg\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ h.write l v x = h x'},
       {t:'p', h:'That residue is a lemma you have. <code>rw [write_other h l x v hx]</code> closes it, which is route three from the worked example arriving unbidden: the moment <code>simp</code> stops, what it hands back is a lookup, and the six lookup equations are exactly the theorems about lookups.'}
     ],
     pitfall:'Assuming that because <code>v</code> does not appear in the conclusion, <code>Heap.write</code> does not appear in the proof. The bracket is not a list of things mentioned in the goal, it is a list of definitions <code>simp</code> is allowed to unfold, and the goal <i>does</i> contain <code>Heap.write</code> — inside a branch that only one of the two cases discards. The general rule: every operation occurring anywhere in the goal, including under an <code>if</code>, needs to be in the bracket unless you have checked that every branch throws it away.',
     variants:'Erase at a different address and the statement is false as written: <code>Heap.erase (Heap.write h l v) l\'</code> still holds <code>v</code> at <code>l</code>, and <code>Heap.erase h l\'</code> does not. Instantiate at <code>Heap.empty</code>, <code>l = 0</code>, <code>l\' = 1</code>, <code>v = 7</code>, apply both sides at <code>0</code>, and the two answers are <code>some 7</code> and <code>none</code>. The true statement there is a commutation law, <code>erase_write_comm</code>, and it needs <code>l ≠ l\'</code> — that is exercise <code>x15</code>. Reverse the order of the two operations and you get <code>write_erase_same : Heap.write (Heap.erase h l) l v = Heap.write h l v</code>, which is the third row of the schema, is true, and has the same two-line proof; there the erase is the operation that is discarded.'
    },

    {t:'p', h:'Two addresses is a different question, and it is the one the rest of the course is built on.'},

    {t:'ex',
     id:'m1-7', name:'write_comm', hard:false,
     why:'Two writes to different cells can be done in either order. That sentence, generalised from two writes to two arbitrary commands and from "different cells" to "regions of memory that do not overlap", is the frame rule. Unit 25 proves the heap half of it for a single write: writing into a heap and then adding the rest of memory gives the same heap as adding the rest first. That is this statement with the second write replaced by a whole frame heap, and it opens the same way — <code>funext</code>, then a split on whether the read point is the write point. Unit 27 turns it into the frame rule. This is also the first place a disequality appears in a statement about heaps, and it is handed to you here; from Unit 08 on you have to derive it.',
     setup:'Hand-driven, because the branches diverge and the point of the exercise is <i>where</i> the hypothesis is spent. <code>unfold Heap.write</code> puts the conditionals where <code>rw [if_pos]</code> and <code>rw [if_neg]</code> can reach them. Three regions to cover: <code>x = l₁</code>, <code>x = l₂</code>, and neither.',
     goal:'theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by',
     hints:[
       'Read at an address <code>x</code>. The left is <code>if x = l₂ then some v₂ else (if x = l₁ then some v₁ else h x)</code> — the outer write is the one at <code>l₂</code> — and the right is the same with the two swapped. The context has <code>hne : l₁ ≠ l₂</code>, a fact about the two write points and not about <code>x</code>.',
       'Three regions, not two. At <code>l₁</code> both sides answer <code>v₁</code>, but the two sides reach that answer differently: one takes an else-branch first and the other a then-branch. At <code>l₂</code> the mirror image. Everywhere else both sides are <code>h x</code>. The hypothesis is needed exactly where you know <code>x</code> is one write point and have to conclude it is not the other.',
       '<code>funext</code>, <code>unfold Heap.write</code>, then <code>by_cases</code> twice, nested rather than chained. The first region needs a <code>have</code> producing a disequality from the hypothesis, and each region is closed by <code>rw</code> with <code>if_pos</code> and <code>if_neg</code>. This is <code>update_comm</code> with one name changed.',
       '<code>funext x</code> then <code>unfold Heap.write</code> leaves <code>⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x</code> — four conditionals, two per side, and the outer one on the left tests <code>l₂</code> while the outer one on the right tests <code>l₁</code>. Now <code>by_cases hx₁ : x = l₁</code>, and in the positive branch <code>have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne</code>. That <code>have</code> is the only line in the proof that mentions <code>hne</code>, and after it the branch is three rewrites.'
     ],
     sol:'theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by\n  funext x\n  unfold Heap.write\n  by_cases hx₁ : x = l₁\n  · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne\n    rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]\n  · by_cases hx₂ : x = l₂\n    · rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]\n    · rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]',
     solNote:'The proof of <code>update_comm</code> with <code>update</code> replaced by <code>Heap.write</code> and the variable names changed. If you wrote the one-liner instead, the comparison is in <i>Why it works</i>: it compiles, and it hides the line this exercise exists for.',
     expl:'The proof is eight lines, one of content and seven of bookkeeping, and the line of content is <code>have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne</code>. Everything else is deciding conditionals whose conditions a hypothesis already settles. What that <code>have</code> does is convert a fact about the write points into a fact about the read point: <code>hne</code> says <code>l₁ ≠ l₂</code>, and in the first region <code>hx₁</code> says the read point <i>is</i> <code>l₁</code>, so the read point is not <code>l₂</code> and the write at <code>l₂</code> is transparent there. In the second region the same conversion is not needed, because <code>hx₁</code> is already a disequality — <code>¬x = l₁</code> — and it is the one the rewrite wants. The asymmetry between the two regions is an artefact of which case <code>by_cases</code> was run on first; the mathematics is symmetric.',
     walk:[
       {tac:'funext x', h:'Equation between heaps to equation between lookups. Now there are two write points and one read point, and the read point is the variable.'},
       {tac:'unfold Heap.write', h:'Replaced all four occurrences by their bodies and carried out the applications that left, leaving <code>(if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x</code>. <code>unfold</code> rather than <code>simp only</code> because nothing is to be simplified — the conditionals are wanted exactly as they stand, so that <code>rw</code> can name them one at a time.'},
       {tac:'by_cases hx₁ : x = l₁', h:'Split on the read point being the first write point. Two goals with the same statement.'},
       {tac:'have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne', h:'<b>The only line that uses <code>hne</code>.</b> <code>rw [hx₁]</code> turned the subgoal <code>x ≠ l₂</code> into <code>l₁ ≠ l₂</code>, which <code>hne</code> is. Non-aliasing enters the proof here and nowhere else.'},
       {tac:'rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]', h:'Left-hand side: the outer write at <code>l₂</code> is not at the read point, so its else-branch; then the inner write at <code>l₁</code> is, so its then-branch, giving <code>some v₁</code>. Right-hand side: the outer write at <code>l₁</code> is at the read point, one step, <code>some v₁</code>. Closed by the trailing <code>rfl</code>.'},
       {tac:'by_cases hx₂ : x = l₂', h:'Inside the negative branch of the first split, the second region. <code>hx₁ : ¬x = l₁</code> is already what the rewrites need, so no <code>have</code>.'},
       {tac:'rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]', h:'The mirror of the first region: then-branch on the left in one step, else-then on the right.'},
       {tac:'rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]', h:'The third region, where the read point is neither write point: four else-branches, two on each side, leaving <code>h x = h x</code>. No hypothesis about <code>l₁</code> and <code>l₂</code> is needed in this region, and it is the largest of the three: most of the address space is not what the theorem is about.'}
     ],
     deep:[
       {t:'trace', title:'The first region, rewrite by rewrite',
        start:'h : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\n⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =\n    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x',
        steps:[
          {tac:'by_cases hx₁ : x = l₁  then  have hx₂ : x ≠ l₂ := …',
           state:'case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x ≠ l₂\n⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =\n    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x',
           h:'The goal is untouched; the context now has both facts about the read point. Everything after this is mechanical.'},
          {tac:'rw [if_neg hx₂]',
           state:'case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x ≠ l₂\n⊢ (if x = l₁ then some v₁ else h x) = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x',
           h:'The leftmost conditional testing <code>x = l₂</code> is the outer one on the left. Its else-branch exposes the inner write.'},
          {tac:'rw [if_pos hx₁]',
           state:'case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x ≠ l₂\n⊢ some v₁ = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x',
           h:'Left-hand side finished.'},
          {tac:'rw [if_pos hx₁]', state:'No goals.',
           h:'The same text again, now matching the right-hand side, which reaches <code>some v₁</code> in one step because its write at <code>l₁</code> is outermost.'}
        ],
        done:'No goals.'},
       {t:'p', h:'There is a proof that closes all four goals with a single call, and comparing it with the eight-line one is the point of having both.'},
       {t:'code', tag:'illustration', cap:'Compiles. Four goals from the two nested splits, all closed by the same call.',
        src:'example (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by\n  funext x\n  by_cases hx₁ : x = l₁ <;> by_cases hx₂ : x = l₂ <;>\n    simp [Heap.write, hx₁, hx₂, hne, hne.symm]'},
       {t:'p', h:'It needs the hypothesis in <i>both</i> orientations. <code>hne : l₁ ≠ l₂</code> and <code>hne.symm : l₂ ≠ l₁</code> are different terms, <code>simp</code> matches text, and one of the four goals arrives with the sides the other way round. Drop <code>hne.symm</code> and that goal survives:'},
       {t:'state', cap:'The surviving goal after <code>simp [Heap.write, hx₁, hx₂, hne]</code>. It is the region where the read point is <code>l₂</code> and not <code>l₁</code>, and the residue is an implication whose antecedent <code>hne.symm</code> would have refuted.',
        src:'error: unsolved goals\ncase pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : x = l₂\n⊢ l₂ = l₁ → v₂ = v₁'},
       {t:'p', h:'The one-liner is shorter and it spends <code>hne</code> in a place you cannot point at. The eight-line proof spends it on one line, and that line is the whole reason this theorem is in the course. Unit 25 asks you to find the corresponding line in a proof about commands; a reader who has only seen the one-liner has nothing to look for.'},
       {t:'p', h:'The hypothesis was assumed, so the honest thing is to check that it was needed.'},
       {t:'code', tag:'verified', cap:'The refutation. Both sides are heaps, so <code>congrFun</code> applies them at one address; at address <code>0</code>, after writing <code>1</code> and then <code>2</code>, the two sides disagree.',
        src:'example : ¬ ∀ (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val),\n    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by\n  intro hc\n  have hbad := congrFun (hc Heap.empty 0 0 1 2) 0\n  simp [Heap.write] at hbad'},
       {t:'trace', title:'How a refutation about heaps is shaped',
        start:'⊢ ¬∀ (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val), (h.write l₁ v₁).write l₂ v₂ = (h.write l₂ v₂).write l₁ v₁',
        steps:[
          {tac:'intro hc',
           state:'hc : ∀ (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val), (h.write l₁ v₁).write l₂ v₂ = (h.write l₂ v₂).write l₁ v₁\n⊢ False',
           h:'Suppose it. <code>¬P</code> is <code>P → False</code>, so the claim goes into the context and the goal becomes <code>False</code>.'},
          {tac:'have hbad := congrFun (hc Heap.empty 0 0 1 2) 0',
           state:'hc : ∀ (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val), (h.write l₁ v₁).write l₂ v₂ = (h.write l₂ v₂).write l₁ v₁\nhbad : (Heap.empty.write 0 1).write 0 2 0 = (Heap.empty.write 0 2).write 0 1 0\n⊢ False',
           h:'Two choices, made in one line. <code>hc Heap.empty 0 0 1 2</code> instantiates the claim at one location twice and two <i>different</i> values, producing an equation between two heaps; <code>congrFun … 0</code> applies both sides at address <code>0</code>, producing an equation between two lookups. That second step is the converse of <code>funext</code>, and it is what turns a false claim about functions into a false claim about values.'},
          {tac:'simp [Heap.write] at hbad', state:'No goals.',
           h:'The left is <code>some 2</code>, the right is <code>some 1</code>, and <code>2 = 1</code> is false — so <code>hbad</code> becomes <code>False</code> and closes the goal.'}
        ],
        done:'No goals.'},
       {t:'p', h:'One location twice was not enough on its own. With the same value written by both, the claim is true and needs no hypothesis at all:'},
       {t:'code', tag:'illustration', cap:'Compiles. The disequality is doing less work than it looks: what makes two writes commute is that they do not disagree, and different addresses is only one way of not disagreeing.',
        src:'example (h : Heap) (l₁ l₂ : Loc) (v : Val) :\n    Heap.write (Heap.write h l₁ v) l₂ v = Heap.write (Heap.write h l₂ v) l₁ v := by\n  funext x\n  by_cases h₁ : x = l₁ <;> by_cases h₂ : x = l₂ <;> simp [Heap.write, h₁, h₂]'},
       {t:'p', h:'So a commutation law needs a disequality exactly when the two operations would put different things at a shared address. Two writes disagree, so <code>write_comm</code> needs one. An erase and a write disagree — <code>none</code> against <code>some v</code> — so the mixed law will need one too. Two erases both put <code>none</code>, so <code>erase_comm</code> should need nothing. That third prediction is the one to check, because a law that needs nothing is the easiest kind to be wrong about:'},
       {t:'code', tag:'verified', cap:'Four regions from the two splits, no hypothesis relating <code>l₁</code> and <code>l₂</code>, and the region where they coincide closes like the other three because both sides answer <code>none</code> there.',
        src:'theorem erase_comm (h : Heap) (l₁ l₂ : Loc) :\n    Heap.erase (Heap.erase h l₁) l₂ = Heap.erase (Heap.erase h l₂) l₁ := by\n  funext x\n  by_cases h₁ : x = l₁ <;> by_cases h₂ : x = l₂ <;> simp [Heap.erase, h₁, h₂]'},
       {t:'p', h:'You can now predict which of the eleven laws carry a hypothesis without proving any of them.'}
     ],
     pitfall:'Writing the two splits as <code>by_cases hx₁ : x = l₁ &lt;;&gt; by_cases hx₂ : x = l₂</code> and then trying to drive the four goals by hand. The <i>first</i> goal to arrive is the impossible region, carrying both <code>hx₁ : x = l₁</code> and <code>hx₂ : x = l₂</code>, and the two rewrites its shape asks for take it to <code>⊢ some v₂ = some v₁</code> and stop. Nothing has gone wrong: the region is empty, because <code>hne</code> makes those two hypotheses contradictory. But <code>if_pos</code> and <code>if_neg</code> only decide conditionals, and no sequence of them will notice that the context is inconsistent. Nest the splits, as the solution does, and the impossible region never appears: the second split happens inside the branch where <code>x ≠ l₁</code> is already known.',
     variants:'Drop <code>hne</code> and the statement is false; the refutation is above, and it needs the two values to differ as well as the two addresses to coincide. Keep <code>hne</code> but make the two values equal and the statement becomes true <i>without</i> the hypothesis, because at a shared address the two writes agree about what to put there — that is the second compiled example above, and it is the sharpest way to see what the disequality is actually for. Reverse it to <code>hne : l₂ ≠ l₁</code> and the proof breaks at exactly one line, the <code>have</code>: <code>exact hne</code> reports <code>Type mismatch … has type l₂ ≠ l₁ but is expected to have type l₁ ≠ l₂</code>, and <code>exact hne.symm</code> repairs it. Every other line is untouched, which is the sharpest statement of where the hypothesis is spent.'
    },

    {t:'p', h:'Back to one address, for the two laws Unit 23 is made of.'},

    {t:'ex',
     id:'m1-8', name:'write_singleton / erase_singleton', hard:false,
     why:'These two are Unit 23\'s rules for assignment and deallocation, computed twenty units early. That rule will say: from a heap holding exactly <code>v</code> at <code>l</code>, an assignment of <code>w</code> to <code>l</code> lands in a heap holding exactly <code>w</code> at <code>l</code>. Its proof will be this equation with a triple wrapped around it — three lines, no <code>funext</code>, no case split, no conditional. Every piece of pointwise reasoning that proof would otherwise need is being done here, in the heap layer, once. That is the layering discipline of the rest of the course.',
     setup:'Two theorems in one editor. The first is the worked example from the top of this page, so write it from memory rather than scrolling. The second has a bracket with a fourth entry in it, and the way to find out why is to leave it out.',
     goal:'theorem write_singleton (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  sorry\n\ntheorem erase_singleton (l : Loc) (v : Val) :\n    Heap.erase (Heap.singleton l v) l = Heap.empty := by',
     hints:[
       'Both goals are equations between heaps, so both are functions of type <code>Loc → Option Val</code>. Unfolded and read at an address <code>x</code>, the first is <code>(if x = l then some w else if x = l then some v else none) = if x = l then some w else none</code> and the second is <code>(if x = l then none else if x = l then some v else none) = Heap.empty x</code>. That right-hand side is the only side on this page that is an operation with no conditional in it.',
       'The first: at <code>l</code> both sides answer <code>w</code>, and away from <code>l</code> both answer nothing. The second: erasing the only cell of a one-cell heap. At <code>l</code> the erase answers nothing and so does the empty heap; away from <code>l</code> the singleton answers nothing and so does the empty heap — the same answer, reached two different ways. Both are the schema at <code>h = Heap.empty</code>.',
       'The three moves, with <code>&lt;;&gt;</code>. Each bracket lists every operation occurring in the goal — on the left and on the right — plus the hypothesis.',
       'The first is the worked example three sections up; write it from memory. For the second, <code>funext x</code> leaves <code>⊢ (Heap.singleton l v).erase l x = Heap.empty x</code>, and that <code>Heap.empty x</code> on the right is what to look at: it is an applied term now, and it was not one before. Then split on <code>x = l</code> and give both branches one <code>simp</code> under <code>&lt;;&gt;</code>. Count the bracket: three operations and the hypothesis. Drop <code>Heap.empty</code> and <i>both</i> branches survive, each one an equation whose right-hand side <code>simp</code> was not allowed to look at.'
     ],
     sol:'theorem write_singleton (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]\n\ntheorem erase_singleton (l : Loc) (v : Val) :\n    Heap.erase (Heap.singleton l v) l = Heap.empty := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]',
     solNote:'<code>erase_singleton</code> is true of the <i>one-cell</i> heap, and of nothing bigger. Erasing <code>l</code> from a heap that also holds <code>l\'</code> does not give <code>Heap.empty</code>, and the gap between those two statements is the whole subject of the next unit.',
     expl:'Both proofs are the schema with <code>h</code> instantiated to <code>Heap.empty</code> and one conditional collapsed, and the interesting half is the second one\'s bracket. <code>Heap.empty</code> has no conditional and no address argument — it is <code>fun _ => none</code> — so it looks like nothing that needs unfolding. But <code>simp</code> works on the goal as written, and as written the right-hand side is the constant <code>Heap.empty x</code>, not <code>none</code>. Until <code>Heap.empty</code> is unfolded, <code>simp</code> is being asked to prove <code>none = Heap.empty x</code> with no information about <code>Heap.empty</code> at all. The entry in the bracket is what supplies it.',
     walk:[
       {tac:'funext x  (both proofs)', h:'Equation between heaps to equation between lookups at <code>x</code>. In <code>erase_singleton</code> this is what makes <code>Heap.empty</code> into an applied term, which is why it can then be unfolded.'},
       {tac:'by_cases hx : x = l  (both proofs)', h:'The single conditional in each operation tests <code>x = l</code>, so one split settles every one of them.'},
       {tac:'<;> simp [Heap.write, Heap.singleton, hx]', h:'<i>In <code>write_singleton</code>.</i> Positive branch: three conditionals to their then-branches, <code>some w = some w</code>. Negative branch: three else-branches, <code>none = none</code>.'},
       {tac:'<;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]', h:'<i>In <code>erase_singleton</code>.</i> Positive branch: the erase takes its then-branch, giving <code>none</code>, and <code>Heap.empty l</code> unfolds to <code>none</code>. Negative branch: the erase is transparent, exposing the singleton, which takes <i>its</i> else-branch, also <code>none</code> — and the right-hand side is <code>none</code> again. Both branches close on <code>none = none</code>, having got there by different routes.'}
     ],
     deep:[
       {t:'trace', title:'erase_singleton, both branches from the unfolded goal',
        start:'l : Loc\nv : Val\n⊢ (Heap.singleton l v).erase l = Heap.empty',
        steps:[
          {tac:'funext x  then  by_cases hx : x = l  then  simp only [Heap.erase, Heap.singleton, Heap.empty]',
           state:'case pos\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then none else if x = l then some v else none) = none',
           h:'Three operations unfolded. <code>Heap.empty</code> contributed the bare <code>none</code> on the right — that is the whole of its contribution, and without it the right-hand side would still read <code>Heap.empty x</code>.'},
          {tac:'simp [hx]', state:'No goals.', h:'Then-branch on the left: <code>none = none</code>.'},
          {tac:'(case neg, same unfolding)',
           state:'case neg\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then none else if x = l then some v else none) = none',
           h:'Identical text, opposite hypothesis.'},
          {tac:'simp [hx]', state:'No goals.',
           h:'Else-branch of the erase exposes the singleton, whose else-branch is <code>none</code>. Two conditionals collapsed rather than one.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The bracket without <code>Heap.empty</code>.',
        src:'example (l : Loc) (v : Val) :\n    Heap.erase (Heap.singleton l v) l = Heap.empty := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, hx]'},
       {t:'state', cap:'Both goals survive, and both residues are entirely about the right-hand side. The left was finished in each case; what <code>simp</code> could not do is recognise that <code>Heap.empty</code> answers <code>none</code>.',
        src:'error: unsolved goals\ncase pos\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ none = Heap.empty l\n\ncase neg\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ none = Heap.empty x'}
     ],
     pitfall:'Reaching for <code>rfl</code> on <code>Heap.empty x = none</code> inside the proof and concluding that <code>Heap.empty</code> therefore does not need to be in the bracket. The equation <i>is</i> closed by <code>rfl</code> — Unit 05 showed exactly that — but <code>simp</code> does not try <code>rfl</code> on subterms it has no rule for; it rewrites with what it is given. A definition that reduces is not a definition <code>simp</code> unfolds unasked. The other way to lose an entry is to drop the namespace, and it does not fail uniformly: <code>simp [erase, singleton, empty, hx]</code> reports <code>Unknown identifier `erase`</code> and <code>Unknown identifier `empty`</code>, and about <code>singleton</code> says only <code>This simp argument is unused</code> — it resolved, to a library name that has nothing to do with heaps. Three of the four operations fail loudly and one fails quietly.',
     variants:'Replace <code>Heap.empty</code> in <code>erase_singleton</code> by an arbitrary heap and you have written something false. Replace the singleton by an arbitrary heap — <code>Heap.erase h l = Heap.empty</code> — and it is false as soon as <code>h</code> holds anything anywhere else: take <code>h</code> to be <code>Heap.singleton 0 1</code> and <code>l</code> to be <code>1</code>, and the left still answers <code>some 1</code> at address <code>0</code> while <code>Heap.empty</code> answers <code>none</code>. That is the observation the next unit opens on. Write <code>write_singleton</code> with the write at a different address, <code>Heap.write (Heap.singleton l v) l\' w</code>, and there is no singleton on the right at all: the result is a two-cell heap, and this course has no notation for one until Unit 14.'
    },

    {t:'p', h:'A free win from the schema, and then the first proof on this page driven by a hypothesis about the <i>heap</i> rather than about an address.'},

    {t:'ex',
     id:'x14', name:'erase_erase, write_of_eq', hard:false,
     why:'<code>erase_erase</code> is the fourth row of the schema and costs two lines — take it, and notice that a law you can predict from the shape of a definition is still a law you have to prove. <code>write_of_eq</code> is different in kind: its hypothesis is a fact about what the heap already holds, and that fact is what drives the positive branch. Every locality proof in Unit 25 has this shape — a hypothesis saying the heap agrees with something at a point, used at exactly that point — so this is the pattern to recognise rather than the theorem to remember.',
     setup:'Two theorems. The first is three moves. The second cannot be, in its positive branch: there is no conditional there to collapse, only a hypothesis to spend, so the branches diverge and hand-driven <code>rw</code> is the move. Note the implicit binders on the second — <code>{h : Heap}</code> — which mean Lean infers <code>h</code>, <code>l</code> and <code>v</code> from the type of <code>hl</code>.',
     goal:'theorem erase_erase (h : Heap) (l : Loc) :\n    Heap.erase (Heap.erase h l) l = Heap.erase h l := by\n  sorry\n\ntheorem write_of_eq {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :\n    Heap.write h l v = h := by',
     hints:[
       'The first: erasing twice at the same address is erasing once. The second: if <code>h</code> already holds <code>v</code> at <code>l</code>, then writing <code>v</code> at <code>l</code> changes nothing — the two heaps <code>Heap.write h l v</code> and <code>h</code> are the same function. At an address <code>x</code>, the left of the second is <code>if x = l then some v else h x</code> and the right is <code>h x</code>.',
       'For the second, take the two regions separately. Away from <code>l</code> the write is transparent and the equation is <code>h x = h x</code> — the hypothesis is not needed. At <code>l</code> the left is <code>some v</code>, the right is <code>h l</code>, and the hypothesis says precisely that those are equal, in the other order.',
       'The first is <code>write_shadow</code>\'s proof with one definition changed. For the second: <code>funext</code>, <code>by_cases</code>, then in the positive branch rewrite with the case hypothesis to put the read point <i>at</i> <code>l</code>, cite <code>write_same</code>, and finish with <code>hl</code> turned round. The negative branch is one citation of <code>write_other</code>.',
       'Second theorem: <code>funext x</code>, <code>by_cases hx : x = l</code>, and in the positive branch <code>rw [hx, write_same]</code>, which leaves <code>⊢ some v = h l</code>. That equation is in your context already, written the other way round, and one term-level suffix turns it round. The negative branch is a single <code>rw</code> citing <code>write_other</code>, with the read point and the disequality supplied explicitly because nothing in the goal fixes them; its trailing <code>rfl</code> closes the goal.'
     ],
     sol:'theorem erase_erase (h : Heap) (l : Loc) :\n    Heap.erase (Heap.erase h l) l = Heap.erase h l := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, hx]\n\ntheorem write_of_eq {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :\n    Heap.write h l v = h := by\n  funext x\n  by_cases hx : x = l\n  · rw [hx, write_same]\n    exact hl.symm\n  · rw [write_other h l x v hx]',
     solNote:'<code>write_of_eq</code> is the only corpus proof on this page that never unfolds a definition. It cites <code>write_same</code> and <code>write_other</code> by name, which is route three from the worked example, and it does so because it has to: <code>simp</code> can collapse a conditional whose condition is settled, and here the thing that has to be used is a hypothesis about <code>h</code>, which no conditional tests.',
     expl:'The two theorems divide along the line this unit is about. <code>erase_erase</code> is decided entirely by the shape of the definition — the outer erase writes <code>none</code> at <code>l</code> regardless of what is underneath, so the inner one is invisible there — and its proof knows nothing except that shape. <code>write_of_eq</code> is decided by the heap: the write is invisible not because of where it is but because of what was already there, and the proof has to reach into the context for a fact about <code>h</code>. That is why one is a <code>&lt;;&gt;</code> one-liner and the other is a five-line proof with two visibly different branches.',
     walk:[
       {tac:'funext x  (erase_erase)', h:'Equation between heaps to equation at an address.'},
       {tac:'by_cases hx : x = l <;> simp [Heap.erase, hx]', h:'Positive: both sides <code>none</code>, the inner erase discarded by the outer one\'s then-branch. Negative: three else-branches, <code>h x = h x</code>. Same call both ways.'},
       {tac:'funext x  (write_of_eq)', h:'The same first move, and the last thing the two proofs have in common.'},
       {tac:'by_cases hx : x = l', h:'Two goals, and this time they will be closed by different tactics — which is what makes <code>&lt;;&gt;</code> unavailable and the focus dots necessary.'},
       {tac:'rw [hx, write_same]', h:'<code>rw [hx]</code> replaced <code>x</code> by <code>l</code> throughout, turning the goal into <code>h.write l v l = h l</code> — a read at the write point, which is the shape <code>write_same</code> matches. <code>rw [write_same]</code> then replaced the left-hand side by <code>some v</code>, leaving <code>⊢ some v = h l</code>.'},
       {tac:'exact hl.symm', h:'<b>The line the hypothesis is spent on.</b> <code>hl : h l = some v</code> is that equation the other way round, and <code>.symm</code> turns it round. Nothing about the write survives into this step.'},
       {tac:'rw [write_other h l x v hx]', h:'The negative branch, in one citation: away from <code>l</code> the write answers what <code>h</code> answers, so the goal becomes <code>h x = h x</code> and <code>rw</code>\'s trailing <code>rfl</code> closes it. The hypothesis <code>hl</code> is not used here, which is the honest reading of the theorem — the write is transparent away from <code>l</code> whatever <code>h</code> holds.'}
     ],
     deep:[
       {t:'trace', title:'write_of_eq, the branch the hypothesis pays for',
        start:'h : Heap\nl : Loc\nv : Val\nhl : h l = some v\n⊢ h.write l v = h',
        steps:[
          {tac:'funext x  then  by_cases hx : x = l',
           state:'case pos\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nx : Loc\nhx : x = l\n⊢ h.write l v x = h x',
           h:'A read at an unknown address, with two facts available: one about the address, one about the heap.'},
          {tac:'rw [hx]',
           state:'case pos\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nx : Loc\nhx : x = l\n⊢ h.write l v l = h l',
           h:'Both occurrences of <code>x</code> replaced. The right-hand side is now <code>h l</code>, which is the exact term <code>hl</code> talks about — this rewrite is what makes the hypothesis applicable at all.'},
          {tac:'rw [write_same]',
           state:'case pos\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nx : Loc\nhx : x = l\n⊢ some v = h l',
           h:'The lookup law, cited rather than unfolded. What is left is <code>hl</code> reversed.'},
          {tac:'exact hl.symm', state:'No goals.', h:'And there is the fact about the heap, used once.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'illustration', cap:'A one-line proof of <code>write_of_eq</code> exists, and it hides the same thing route one hid.',
        src:'example {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :\n    Heap.write h l v = h := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, hx, hl]'},
       {t:'p', h:'It works because <code>hl</code> in the bracket is a rewrite rule turning <code>h l</code> into <code>some v</code>, and after the positive branch has collapsed its conditional that is exactly the rewrite needed. Drop <code>hl</code> from the bracket and the positive branch stops at <code>⊢ some v = h l</code> — the same goal the hand-driven proof reaches, arrived at without being asked for.'}
     ],
     pitfall:'On <code>erase_erase</code>, trying to skip the case split because both sides look like they should reduce. <code>simp [Heap.erase]</code> after <code>funext x</code> alone leaves <code>⊢ x = l → ¬x = l → none = h x</code>: <code>simp</code> pulled both conditions out as antecedents rather than deciding them, and the resulting goal is true but not closed. On <code>write_of_eq</code>, writing <code>exact hl</code> instead of <code>exact hl.symm</code>. Lean prints <code>Type mismatch</code> / <code>hl</code> / <code>has type</code> / <code>h l = some v</code> / <code>but is expected to have type</code> / <code>some v = h l</code> — the two propositions are on the last two lines, and the first line says only that they differ.',
     variants:'Drop <code>hl</code> from <code>write_of_eq</code> and the statement becomes <code>Heap.write h l v = h</code> for every heap, which is false at <code>Heap.empty</code>: the write allocates, so at <code>Heap.empty</code>, <code>l = 0</code>, <code>v = 7</code> the left answers <code>some 7</code> at <code>0</code> and the right answers <code>none</code>. The refutation is the <code>congrFun</code> pattern from <code>write_comm</code>\'s counterexample. Weaken <code>hl</code> to <code>defined h l</code> — the heap holds <i>something</i> at <code>l</code> — and the statement is false again, because the write can change the value: take <code>h</code> to be <code>Heap.singleton 0 1</code>, whose <code>defined</code> witness is <code>⟨1, singleton_same 0 1⟩</code>, and write <code>2</code> at <code>0</code>. Strengthen the conclusion of <code>erase_erase</code> to <code>Heap.erase (Heap.erase h l₁) l₂ = Heap.erase h l₂</code> with two addresses and it is false — at <code>Heap.singleton 0 1</code> with <code>l₁ = 0</code> and <code>l₂ = 1</code> the left is empty at <code>0</code> and the right is not. The true two-address statement is <code>erase_comm</code>, which needs no hypothesis, and the reason it needs none is that both erases put <code>none</code> at their address.'
    },

    {t:'p', h:'The last one has two halves: a law to prove, and a claim to write down and knock over.'},

    {t:'ex',
     id:'x15', name:'erase_write_comm, and the claim it is not', hard:false,
     why:'The mixed commutation law completes the eleven, and it is the one where <code>unfold</code> — which worked for <code>write_comm</code> three exercises ago — leaves a term <code>rw</code> cannot match. Meeting that once, deliberately, is worth more than a rule of thumb. The second half is your first design exercise about a false statement: you write the claim, and you refute it. Every refutation about heaps in this course has the shape you will use, and Unit 07 leans on it immediately.',
     setup:'First: prove the law. It is <code>write_comm</code>\'s three-region proof with one operation changed, but the first move is different and finding out why is the exercise. Then: the law needs <code>l ≠ l\'</code>. Delete the hypothesis, state what is left as a proposition that is <i>false</i>, and prove that it is false. Any correct statement of the false claim will be accepted; the one below is the obvious one.',
     goal:'theorem erase_write_comm (h : Heap) (l l\' : Loc) (v : Val) (hne : l ≠ l\') :\n    Heap.erase (Heap.write h l v) l\' = Heap.write (Heap.erase h l\') l v := by\n  sorry\n\n-- Now drop `hne`. State the claim that erase and write commute unconditionally,\n-- and refute it. Any correct statement will be accepted.\nexample : True := by',
     hints:[
       'The law, read at an address <code>x</code>: the left is <code>if x = l\' then none else (if x = l then some v else h x)</code>, with the erase outermost, and the right is <code>if x = l then some v else (if x = l\' then none else h x)</code>. Four conditionals, two per side, testing two different addresses, with <code>hne : l ≠ l\'</code> available and saying nothing about <code>x</code>. The second half asks for a <i>proposition</i>, not a proof: the same law with <code>hne</code> deleted, stated so that what you write is false — which means a negated universal over everything the law quantifies over, <code>¬ ∀ (h : Heap) (l l\' : Loc) (v : Val), …</code>.',
       'Three regions again: the read point is <code>l\'</code>, or it is <code>l</code>, or it is neither, and the hypothesis is needed only in the first — it is the region where you know the read point is one of the two operation points and have to conclude it is not the other. For the refutation: the claim can fail only where the hypothesis was, so make the two addresses equal. At a single address the two sides do opposite things, one ending with the cell erased and the other with the cell written, so any heap exhibits it and the cheapest is the one with no cells.',
       'For the law, the first move is <b>not</b> <code>unfold</code>. Try it and read the error; then use <code>simp only</code> with both definitions, which does the same unfolding and one more thing. After that it is <code>by_cases</code> twice, nested, a <code>have</code> converting <code>hne</code> into a fact about the read point, and <code>rw</code> with <code>if_pos</code> and <code>if_neg</code>. The proposition to arrive at in the second half is <code>¬ ∀ (h : Heap) (l l\' : Loc) (v : Val), Heap.erase (Heap.write h l v) l\' = Heap.write (Heap.erase h l\') l v</code>, and its proof is <code>intro</code>, then an instantiation, then <code>congrFun</code> at an address, then <code>simp … at</code>.',
       'The law: <code>funext x</code>, <code>simp only [Heap.write, Heap.erase]</code>, then <code>by_cases hx : x = l\'</code> with <code>have hxl : x ≠ l := by rw [hx]; exact fun hc => hne hc.symm</code> — watch the orientation, because <code>rw [hx]</code> leaves the subgoal as <code>l\' ≠ l</code> and <code>hne</code> points the other way. The refutation: <code>intro hc</code>, then <code>have hbad := congrFun (hc Heap.empty 0 0 7) 0</code>, which puts <code>hbad : (Heap.empty.write 0 7).erase 0 0 = (Heap.empty.erase 0).write 0 7 0</code> into the context; one <code>simp … at hbad</code> with both definitions reduces that to <code>none = some 7</code> and closes the goal.'
     ],
     sol:'theorem erase_write_comm (h : Heap) (l l\' : Loc) (v : Val) (hne : l ≠ l\') :\n    Heap.erase (Heap.write h l v) l\' = Heap.write (Heap.erase h l\') l v := by\n  funext x\n  simp only [Heap.write, Heap.erase]\n  by_cases hx : x = l\'\n  · have hxl : x ≠ l := by rw [hx]; exact fun hc => hne hc.symm\n    rw [if_pos hx, if_neg hxl, if_pos hx]\n  · by_cases hxl : x = l\n    · rw [if_neg hx, if_pos hxl, if_pos hxl]\n    · rw [if_neg hx, if_neg hxl, if_neg hxl, if_neg hx]\n\nexample : ¬ ∀ (h : Heap) (l l\' : Loc) (v : Val),\n    Heap.erase (Heap.write h l v) l\' = Heap.write (Heap.erase h l\') l v := by\n  intro hc\n  have hbad := congrFun (hc Heap.empty 0 0 7) 0\n  simp [Heap.erase, Heap.write] at hbad',
     solNote:'It is tempting to say this law is proved the same way as <code>erase_write_same</code> and leave it at that. It is not: the same way starts with <code>unfold</code>, and <code>unfold</code> does not work here. A law you have not run through Lean is a law you have not checked, and this is the one that would have caught you.',
     expl:'The proof is <code>write_comm</code>\'s three regions with the outer operation changed from a write to an erase, and everything about it is routine except the first move. <code>unfold Heap.write Heap.erase</code> replaces both names by their bodies, but the inner operation appears in the goal as an <i>argument</i> — <code>Heap.erase (Heap.write h l v) l\'</code> — so unfolding it produces a lambda sitting where a heap was, and the application of that lambda to the read point is left standing as <code>(fun x => if x = l then some v else h x) x</code>. That term is equal to a conditional and is not <i>written</i> as one, and <code>rw</code> matches written form. A function written out and immediately applied, like that one, is called a <b>redex</b>, and carrying it out — substituting the argument into the body — is <b>beta-reduction</b>. <code>unfold</code> does not do it. <code>simp only</code> with the same two names does the same unfolding and then beta-reduces, which is the whole difference between them here. This did not arise in <code>write_comm</code> because both operations there were writes and one <code>unfold</code> reached them in the order that leaves no redex.',
     walk:[
       {tac:'funext x', h:'Equation between heaps to equation at an address.'},
       {tac:'simp only [Heap.write, Heap.erase]', h:'Unfolded both definitions <i>and</i> applied the resulting functions to <code>x</code>, leaving three conditionals and no lambda. This is the line the exercise exists for; <code>unfold</code> here leaves a fourth term that no <code>if_pos</code> or <code>if_neg</code> can touch.'},
       {tac:'by_cases hx : x = l\'', h:'First region: the read point is the erase point.'},
       {tac:'have hxl : x ≠ l := by rw [hx]; exact fun hc => hne hc.symm', h:'The hypothesis, spent, in the orientation the goal needs. <code>rw [hx]</code> turns the subgoal into <code>l\' ≠ l</code>; <code>hne</code> is <code>l ≠ l\'</code>, so the proof supplied is the function taking a proof of <code>l\' = l</code>, reversing it, and feeding it to <code>hne</code>. That is what <code>≠</code> unfolds to — a function into <code>False</code>.'},
       {tac:'rw [if_pos hx, if_neg hxl, if_pos hx]', h:'Left: the erase fires, giving <code>none</code>. Right: the write does not fire, exposing the erase, which does, also giving <code>none</code>.'},
       {tac:'by_cases hxl : x = l', h:'Second region, inside the branch where the read point is not <code>l\'</code>.'},
       {tac:'rw [if_neg hx, if_pos hxl, if_pos hxl]', h:'Left: the erase is transparent, then the write fires. Right: the write fires immediately. Both <code>some v</code>.'},
       {tac:'rw [if_neg hx, if_neg hxl, if_neg hxl, if_neg hx]', h:'Third region, four else-branches, <code>h x = h x</code>.'},
       {tac:'intro hc  (the refutation)', h:'Assumed the unconditional claim, leaving <code>False</code> to prove.'},
       {tac:'have hbad := congrFun (hc Heap.empty 0 0 7) 0', h:'Instantiated at the one heap with no cells, with the write point and the erase point both <code>0</code>, then applied both sides at <code>0</code>. <code>congrFun</code> is what turns a claim about heaps into a claim about a lookup.'},
       {tac:'simp [Heap.erase, Heap.write] at hbad', h:'On the left the erase comes last and answers <code>none</code>; on the right the write comes last and answers <code>some 7</code>. Constructors differ, so <code>hbad</code> becomes <code>False</code> and the goal closes.'}
     ],
     deep:[
       {t:'trace', title:'The first region, where the hypothesis is spent',
        start:'case pos\nh : Heap\nl l\' : Loc\nv : Val\nhne : l ≠ l\'\nx : Loc\nhx : x = l\'\nhxl : x ≠ l\n⊢ (if x = l\' then none else if x = l then some v else h x) = if x = l then some v else if x = l\' then none else h x',
        steps:[
          {tac:'rw [if_pos hx]',
           state:'case pos\nh : Heap\nl l\' : Loc\nv : Val\nhne : l ≠ l\'\nx : Loc\nhx : x = l\'\nhxl : x ≠ l\n⊢ none = if x = l then some v else if x = l\' then none else h x',
           h:'The leftmost conditional testing <code>x = l\'</code> is the outer one on the left, and it is the erase. Its then-branch is <code>none</code>, and the write nested inside the else-branch went with it.'},
          {tac:'rw [if_neg hxl]',
           state:'case pos\nh : Heap\nl l\' : Loc\nv : Val\nhne : l ≠ l\'\nx : Loc\nhx : x = l\'\nhxl : x ≠ l\n⊢ none = if x = l\' then none else h x',
           h:'On the right the write is outermost and it does <i>not</i> fire — this is the rewrite <code>hxl</code> was manufactured for, and the only place in the proof where <code>hne</code> has any effect. Its else-branch exposes the erase.'},
          {tac:'rw [if_pos hx]', state:'No goals.',
           h:'The exposed erase fires, giving <code>none = none</code>. Both sides reach the same answer, by opposite routes: on the left the erase was applied last, on the right it was applied first and the write missed.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The same proof with <code>unfold</code> in place of <code>simp only</code>. It fails, and it fails in the two regions where the exposed operation is the inner one.',
        src:'example (h : Heap) (l l\' : Loc) (v : Val) (hne : l ≠ l\') :\n    Heap.erase (Heap.write h l v) l\' = Heap.write (Heap.erase h l\') l v := by\n  funext x\n  unfold Heap.write Heap.erase\n  by_cases hx : x = l\'\n  · have hxl : x ≠ l := by rw [hx]; exact fun hc => hne hc.symm\n    rw [if_pos hx, if_neg hxl, if_pos hx]\n  · by_cases hxl : x = l\n    · rw [if_neg hx, if_pos hxl, if_pos hxl]\n    · rw [if_neg hx, if_neg hxl, if_neg hxl, if_neg hx]'},
       {t:'state', cap:'The first of the two complaints — the second is the same failure in the third region, with different metavariable numbers. The pattern is a conditional; the target has a lambda applied to an argument where the conditional should be. Those are the same value and not the same text.',
        src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  if x = l then ?m.75 else ?m.76\nin the target expression\n  (fun x => if x = l then some v else h x) x = some v\n\ncase pos\nh : Heap\nl l\' : Loc\nv : Val\nhne : l ≠ l\'\nx : Loc\nhx : ¬x = l\'\nhxl : x = l\n⊢ (fun x => if x = l then some v else h x) x = some v'},
       {t:'p', h:'Swapping the order to <code>unfold Heap.erase Heap.write</code> does not fix it; it moves the redex to the other side of the equation, where the same rewrites fail for the same reason. The goal after that variant reads <code>(if x = l\' then none else if x = l then some v else h x) = if x = l then some v else (fun x => if x = l\' then none else h x) x</code>. Whichever name is unfolded first, the operation that was an argument leaves a redex behind.'},
       {t:'trace', title:'The refutation',
        start:'⊢ ¬∀ (h : Heap) (l l\' : Loc) (v : Val), (h.write l v).erase l\' = (h.erase l\').write l v',
        steps:[
          {tac:'intro hc',
           state:'hc : ∀ (h : Heap) (l l\' : Loc) (v : Val), (h.write l v).erase l\' = (h.erase l\').write l v\n⊢ False',
           h:'The claim in the context, <code>False</code> as the goal.'},
          {tac:'have hbad := congrFun (hc Heap.empty 0 0 7) 0',
           state:'hc : ∀ (h : Heap) (l l\' : Loc) (v : Val), (h.write l v).erase l\' = (h.erase l\').write l v\nhbad : (Heap.empty.write 0 7).erase 0 0 = (Heap.empty.erase 0).write 0 7 0\n⊢ False',
           h:'Two instantiations and one application. The heap is arbitrary, so <code>Heap.empty</code> is the cheapest choice; the addresses are the interesting choice, and taking both to be <code>0</code> is precisely deleting the hypothesis.'},
          {tac:'simp [Heap.erase, Heap.write] at hbad', state:'No goals.',
           h:'<code>hbad</code> reduces to <code>none = some 7</code>, which is false by constructor distinctness, so <code>simp</code> turns the hypothesis into <code>False</code> and uses it.'}
        ],
        done:'No goals.'}
     ],
     pitfall:'Getting the orientation of <code>hne</code> wrong in the <code>have</code>. After <code>rw [hx]</code> the subgoal is <code>l\' ≠ l</code> and the hypothesis is <code>l ≠ l\'</code>, so <code>exact hne</code> fails with <code>Type mismatch … has type l ≠ l\' but is expected to have type l\' ≠ l</code>, and something has to reverse it. The corpus writes the reversal by hand as <code>fun hc => hne hc.symm</code>; <code>exact hne.symm</code> is the same proof under a library name and compiles too. In <code>write_comm</code> the orientation happened to come out right, which is exactly the kind of luck not to rely on. For the refutation: choosing two <i>different</i> addresses. Instantiate at <code>0</code> and <code>1</code> rather than <code>0</code> and <code>0</code> and nothing reports an error at the <code>have</code> — the <code>simp</code> succeeds, because at different addresses the two sides really are equal. It leaves <code>hbad : True</code> in the context and the goal still reading <code>False</code>, and the only complaint is <code>unsolved goals</code>. The claim is false only where the hypothesis was, and the hypothesis said the addresses differ, so the counterexample has to make them equal.',
     variants:'Two other statements of the false claim are equally correct and equally accepted. You may fix the heap and the value and quantify over the addresses only — <code>¬ ∀ l l\' : Loc, Heap.erase (Heap.write Heap.empty l 7) l\' = Heap.write (Heap.erase Heap.empty l\') l 7</code> — which is weaker and needs the same three lines. Or you may state the single instance, <code>Heap.erase (Heap.write Heap.empty 0 7) 0 ≠ Heap.write (Heap.erase Heap.empty 0) 0 7</code>, which is the sharpest form: it names the counterexample in the statement, so the proof is <code>intro</code>, <code>congrFun</code> at <code>0</code>, <code>simp</code>, with nothing to instantiate. The universally quantified version is the one to prefer when the point is that the <i>law</i> fails; the single instance is the one to prefer when the point is that a particular program is wrong, and Unit 07 uses that form.'
    },

    /* ------------------------------------------------------ the interface --- */

    {t:'sec', s:'The interface, closed'},

    {t:'tbl',
     cap:'The eleven equations between heaps. Together with Unit 05\'s six lookup equations they are everything this course knows about memory. Two of the eleven carry a hypothesis about addresses; one carries a hypothesis about the heap; the other eight are unconditional.',
     head:['name', 'statement', 'hypothesis'],
     rows:[
       ['<code>write_shadow</code>', '<code>(h.write l v₁).write l v₂ = h.write l v₂</code>', '—'],
       ['<code>erase_write_same</code>', '<code>(h.write l v).erase l = h.erase l</code>', '—'],
       ['<code>write_erase_same</code>', '<code>(h.erase l).write l v = h.write l v</code>', '—'],
       ['<code>erase_erase</code>', '<code>(h.erase l).erase l = h.erase l</code>', '—'],
       ['<code>write_empty</code>', '<code>Heap.write Heap.empty l v = Heap.singleton l v</code>', '—'],
       ['<code>write_singleton</code>', '<code>Heap.write (Heap.singleton l v) l w = Heap.singleton l w</code>', '—'],
       ['<code>erase_singleton</code>', '<code>Heap.erase (Heap.singleton l v) l = Heap.empty</code>', '—'],
       ['<code>erase_comm</code>', '<code>(h.erase l₁).erase l₂ = (h.erase l₂).erase l₁</code>', '—'],
       ['<code>write_comm</code>', '<code>(h.write l₁ v₁).write l₂ v₂ = (h.write l₂ v₂).write l₁ v₁</code>', '<code>l₁ ≠ l₂</code>'],
       ['<code>erase_write_comm</code>', '<code>(h.write l v).erase l\' = (h.erase l\').write l v</code>', '<code>l ≠ l\'</code>'],
       ['<code>write_of_eq</code>', '<code>Heap.write h l v = h</code>', '<code>h l = some v</code>']
     ]},

    {t:'p', h:'Read the third column. Eight of the eleven need nothing at all. Of the three that do, two are commutation laws with two addresses in them, and the third is about what the heap already holds. The remaining commutation law, <code>erase_comm</code>, also has two addresses and still needs nothing — and the reason is the one you already have: two erases put the same thing at a shared address, namely <code>none</code>, and neither of the other two pairs does. A disequality is needed exactly where two operations would disagree.'},

    {t:'note', kind:'key', title:'Where each of these is spent',
     h:'<code>write_singleton</code> and <code>erase_singleton</code> are Unit 23\'s rules for assignment and deallocation; those proofs are three lines and contain no <code>funext</code>, and <code>write_singleton</code> is cited again in Units 29, 31 and 37. Those two are the only ones a later unit calls by name. The other nine are not spent, they are held — an interface you can use without checking is one that was finished before it was needed, and the moment a fact is missing from it you are back to unfolding. Two of the nine survive a second way, as shapes rather than as citations. <code>write_comm</code> is the argument Unit 25 runs again with the second write replaced by a whole frame heap; <code>write_of_eq</code> is the shape of the other half of that same proof — a hypothesis saying the heap holds something at a point, spent at exactly that point. Unit 25 is the last pointwise reasoning about heaps in the course, and none of it happens inside a Hoare proof.'},

    /* --------------------------------------------------- retrospective --- */

    {t:'sec', s:'Retrospective'},

    {t:'detail', title:'Why is <code>Heap</code> a function into <code>Option</code>, and not a primitive partial map?', open:false,
     blocks:[
       {t:'p', h:'Because of the eleven proofs on this page. Ten of them are <code>funext</code>, then a case split, then a decision about a conditional; the eleventh replaces that last step by citing two equations that were themselves proved that way. Every step of that is available only because a heap is a function and its operations are conditionals. A packaged partial map — a domain predicate together with a value function defined on it — makes every one of these equations into a pair of equations, the second of which does not typecheck until the first is proved, and <code>rw</code> stops finding its patterns because every value now travels wrapped in the proof that says it is there at all. The price of the <code>Option</code> encoding is the ambiguity in <code>none</code> and the loss of <code>rfl</code>; what it buys is that <code>funext</code>, <code>by_cases</code> and <code>if_pos</code> are the entire proof method, on this page and everywhere after it.'}
     ]},

    {t:'detail', title:'Which of the eleven needs a hypothesis, and why only those?', open:false,
     blocks:[
       {t:'p', h:'Three of them: <code>write_comm</code>, <code>erase_write_comm</code> and <code>write_of_eq</code>. The first two are commutation laws whose operations disagree at a shared address, and the disequality is what rules the shared address out. <code>erase_comm</code> is a commutation law whose operations agree — both put <code>none</code> — and it needs nothing. <code>write_of_eq</code> is the odd one: its hypothesis is about the heap rather than the addresses, and it says the write is redundant rather than that it is elsewhere.'},
       {t:'p', h:'The general statement is that two operations commute when the parts of memory they touch are separate, <i>or</i> when they agree wherever those parts meet. Both halves matter later. The first becomes the frame rule, in Unit 27. The second is why <code>write_comm</code> with a single value is unconditional, and Unit 38 takes it seriously: it builds resource models that are not heaps, and in some of them two owners may hold the same cell provided neither changes it.'}
     ]},

    {t:'detail', title:'What does "the interface is closed" forbid you from doing?', open:false,
     blocks:[
       {t:'p', h:'Putting <code>Heap.write</code>, <code>Heap.erase</code> or <code>Heap.singleton</code> into a <code>simp</code> bracket, or into an <code>unfold</code>, in any proof from Unit 07 onwards. Seventeen equations — six lookups and eleven between heaps — are what remains, and a proof that needs a fact not among them needs a new lemma stated in the same style, proved here in the same way, and added to the list. <code>Heap.empty</code> is exempt for the reason given above: it has no conditional and no lookup law, so naming it asks for one reduction and nothing else.'},
       {t:'p', h:'The reason is not neatness. A proof that unfolds <code>Heap.write</code> is a proof about how <code>Heap.write</code> was written: with the equation as <code>x = l</code> rather than <code>l = x</code>, with the value in the then-branch, with the heap consulted in the else-branch. Any of those could have been chosen differently, and every such proof would break.'}
     ]},

    {t:'dod', h:'You can prove an equation between two heaps by the three moves, and say what <code>heap_ext</code> is. You can generate four of the eleven laws from one schema before proving any of them, and say why two more come from the same schema at <code>Heap.empty</code>. You can prove <code>write_comm</code> by hand and point at the single line that spends the disequality. You can refute the same statement without it, by <code>congrFun</code> at one address, and say why the counterexample needs two different values. You can predict which laws carry a hypothesis from what the two operations put at a shared address. You can choose between <code>simp</code>, hand-driven <code>rw</code>, and citing the lookup laws by name, and you know that <code>unfold</code> leaves a redex when the operation it unfolds is an argument rather than a head.'},

    {t:'p', h:'Every law so far is about one heap, and <code>write_comm</code> had its disequality handed to it. In a real program nobody hands it to you. To <i>derive</i> such a fact rather than assume it, memory has to be splittable — and before we can split a heap we had better decide what it means to hold one.'}

  ]
});
