registerChapter({
  id: 'heap',
  num: '05',
  phase: 'Phase 1 · The resource algebra',
  title: 'Memory as a partial function',
  blurb: 'Four operations on memory, and the six equations that replace them — after this unit you read a heap through its laws and never through its definition.',

  orient: {
    youWill: [
      'Say what <code>h l = none</code> means, in both of its readings, and why nothing in the model separates them.',
      'Read the four operations off a two-by-two table and predict, before proving anything, which laws come in pairs and which operation has none.',
      'Declare things inside a <code>namespace</code>, put <code>Heap.write</code> in a <code>simp</code> bracket, and read <code>h.write l v</code> in a goal as the term <code>Heap.write h l v</code>.',
      'Prove all six lookup equations, each in one <code>simp</code>, and tell the two residues <code>⊢ x = l → some v = h x</code> and <code>⊢ ¬x = l</code> apart by saying what <code>simp</code> could refute in one and not in the other.',
      'Say what each operation does to the domain of a heap, and why none of them asks whether the address was yours to begin with.'
    ],
    needs: [
      'Unit 04: <code>update_same</code> and <code>update_other</code> — their one-line <code>simp</code> proofs, and the residue left when the disequality is withheld. <code>funext</code> appears here once, in a fold.',
      'Unit 02: <code>Option</code>, <code>some</code>, <code>none</code>, constructor distinctness, and <code>defined</code>.',
      'Unit 00: <code>Heap</code>, <code>Loc</code>, <code>Val</code> and why the codomain was widened.'
    ],
    payoff: 'Every heap proof for the rest of the course goes through these six equations. Unit 06 closes the interface with five equations between whole heaps; from Unit 07 on, no proof unfolds a heap operation again.'
  },

  blocks: [

    /* ------------------------------------------------- picking up unit 04 --- */

    {t:'p', h:'<code>update f x v</code> could put a value at a point. It could not take one away, and there was no point it could be asked about that held nothing: <code>f : Nat → Nat</code> answers everywhere, with a value. Memory does not. At any moment most addresses hold nothing at all, and the operation that gives a cell up is one a program actually performs. Both of those need a codomain with room for an absent value, which is what Unit 00 settled when it declared <code>Heap</code>.'},

    {t:'code', tag:'verified', cap:'From Unit 00. Nothing here is new; what is new is that there are now operations on it.',
     src:'abbrev Heap  := Loc → Option Val'},

    {t:'p', h:'So a heap answers every address, and its answer at <code>l</code> is either <code>some v</code> or <code>none</code>. The first is unambiguous: <code>l</code> holds <code>v</code>. The second is not. It can be read as <i>address <code>l</code> has never been allocated</i>, and it can be read as <i>address <code>l</code> is allocated but is not part of the memory this heap describes</i> — someone else\'s cell. Nothing in the type distinguishes them, and nothing later in the course will.'},

    {t:'note', kind:'key', title:'The ambiguity in <code>none</code> is a design decision, not an oversight',
     h:'A heap in this course is never "the memory of the machine". It is <i>the part of memory some argument is about</i>, and <code>none</code> says "not that part". Unit 27 proves that a fact established about a small heap survives when the rest of memory is put back around it. If <code>none</code> meant <i>genuinely unallocated</i>, that would be false: the small heap would be asserting something about cells it does not hold, and adding those cells would contradict it. The conflation is what makes a heap divisible.'},

    {t:'p', h:'The alternative is a codomain with three answers rather than two — <code>some v</code>, <code>unallocated</code>, <code>elsewhere</code>. Every operation below would then have to say which of the two negative tags it produces, and every way of putting two heaps side by side would have to say which tag wins when one heap says <code>unallocated</code> and the other says <code>elsewhere</code>. That last question has no answer, because the distinction is not a property of a heap at all: whether an address you do not hold is unallocated or held by somebody else depends on who else is there. A heap that reported it could not be read without knowing what surrounds it — and reading a heap without knowing what surrounds it is the one thing this course exists to do. Two answers, and the loss of information, are what that buys.'},

    /* ---------------------------------------------------- four operations --- */

    {t:'sec', s:'Four operations'},

    {t:'p', h:'Four things have to be expressible before anything can be said. A heap holding nothing, to start an argument from. A heap holding exactly one cell, the smallest thing that can be owned. Changing what one address holds. Removing an address altogether. Reading is not on the list: reading at <code>l</code> is the application <code>h l</code>, and its result is an <code>Option Val</code> precisely because a read can find nothing.'},

    {t:'code', tag:'verified', cap:'The whole of memory\'s interface, and the last time in this course that any of these four bodies is looked at.',
     src:'namespace Heap\n\ndef empty : Heap := fun _ => none\n\ndef singleton (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else none\n\ndef write (h : Heap) (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else h x\n\ndef erase (h : Heap) (l : Loc) : Heap :=\n  fun x => if x = l then none else h x\n\nend Heap'},

    {t:'p', h:'<code>namespace Heap … end Heap</code> prefixes every name declared between the two lines: the four definitions above are <code>Heap.empty</code>, <code>Heap.singleton</code>, <code>Heap.write</code> and <code>Heap.erase</code>. That is the only thing it does. Without it each definition would have to carry its type in its own name — <code>heapWrite</code>, <code>heapErase</code> — and the short names would be spent globally, in a course where three more operations join <code>Heap</code> in Unit 08 and a second type gets a namespace of its own in Unit 18. The prefix is not optional decoration: outside the namespace the short name does not resolve at all.'},

    {t:'code', tag:'sketch', cap:'Two commands, the second one deliberately broken.',
     src:'#check Heap.write\n#check write'},

    {t:'state', cap:'The <code>file:line:column</code> prefix is dropped here and everywhere on this page. The second message is §<i>errors</i>\'s first entry, and this is its commonest cause: the name exists, in a namespace you are not inside.',
     src:'Heap.write (h : Heap) (l : Loc) (v : Val) : Heap\n\nerror(lean.unknownIdentifier): Unknown identifier `write`'},

    {t:'p', h:'In a goal the traffic runs the other way: Lean prints <code>Heap.write h l v</code> as <code>h.write l v</code>. The condition is the one Unit 01 gave for <code>h.symm</code> — head <code>N.f</code>, first explicit argument of type <code>N</code> — and only two of the four operations meet it. <code>Heap.write</code> and <code>Heap.erase</code> take a heap first and get the short display. <code>Heap.singleton l v</code> has no heap argument to move and prints in full, and so does <code>Heap.empty</code>. The same page of a proof will therefore show you both spellings, and they are not two kinds of thing.'},

    {t:'state', cap:'Two goals, from two <code>trace_state</code> runs. The same operation is written <code>Heap.write</code> in the source and <code>h.write</code> in the display; the one below it never changes its spelling.',
     src:'h : Heap\nl x : Loc\nv : Val\n⊢ h.write l v x = h x\n\nl x : Loc\nv : Val\n⊢ Heap.singleton l v x = none'},

    /* --------------------------------------------------------- the table --- */

    {t:'p', h:'Three of the four bodies have one shape between them. Each is <code>fun x => if x = l then A else B</code>, with two choices for the then-branch — the address gets a value, or the address gets nothing — and two for the else-branch — everywhere else is empty, or everywhere else is whatever <code>h</code> said. Two choices twice is four combinations, and the fourth, where the address gets nothing and so does everywhere else, is <code>Heap.empty</code> with its conditional collapsed.'},

    {t:'tbl',
     cap:'The then-branch decides what happens at <code>l</code>; the else-branch decides what happens everywhere else. <code>Heap.empty</code> is the cell where both branches agree, so its <code>if</code> was dropped and its argument <code>l</code> with it.',
     head:['at <code>l</code> ↓ &nbsp; elsewhere →', '<code>none</code> — nothing', '<code>h x</code> — whatever <code>h</code> held'],
     rows:[
       ['<code>some v</code> — a value', '<code>Heap.singleton l v</code><br><span class="dg-note">build one cell</span>', '<code>Heap.write h l v</code><br><span class="dg-note">change one cell</span>'],
       ['<code>none</code> — nothing', '<code>Heap.empty</code><br><span class="dg-note">build no cells</span>', '<code>Heap.erase h l</code><br><span class="dg-note">remove one cell</span>']
     ]},

    {t:'p', h:'The table predicts the shape of what is provable before any of it is proved. Three operations have a genuine conditional, so each of them has two lookup equations and not one: what you get reading <i>at</i> <code>l</code>, which is the then-branch, and what you get reading anywhere <i>else</i>, which is the else-branch and needs a hypothesis saying that the address really is elsewhere. Three operations, two equations each, is the six theorems this unit proves. <code>Heap.empty</code> has no conditional and therefore no pair: its answer does not depend on where you read, and the single fact about it is closed by reduction with no theorem at all.'},

    {t:'code', tag:'illustration', cap:'No <code>simp</code>, no tactic block. Unit 02\'s rule says reduction stops at a conditional whose condition mentions a variable; here there is no conditional to stop at.',
     src:'example (l : Loc) : Heap.empty l = none := rfl'},

    {t:'detail', title:'Why not one operation, with an <code>Option</code> argument?', open:false,
     blocks:[
       {t:'p', h:'The right-hand column of the table differs only in its then-branch, so the two operations in it can be merged by making that branch an argument. Two definitions become one, and the two pairs of lookup laws become one pair.'},
       {t:'code', tag:'illustration', cap:'Both equations hold by <code>rfl</code>: the merged operation really does have the other two as instances.',
        src:'def upd (h : Heap) (l : Loc) (o : Option Val) : Heap :=\n  fun x => if x = l then o else h x\n\nexample (h : Heap) (l : Loc) (v : Val) : Heap.write h l v = upd h l (some v) := rfl\nexample (h : Heap) (l : Loc)           : Heap.erase h l   = upd h l none     := rfl\n\ntheorem upd_same (h : Heap) (l : Loc) (o : Option Val) : upd h l o l = o := by\n  simp [upd]'},
       {t:'p', h:'What it costs is visible in the statement of <code>upd_same</code>: its right-hand side is <code>o</code>, a variable. Every later use of it lands you with an equation about an unknown <code>Option Val</code> rather than about a value or about nothing, and getting from there to either one is a case analysis that has to be done again at every use.'},
       {t:'code', tag:'sketch', cap:'The merged form of "after a write, the cell holds the value written". It is not provable, because nothing says the thing written was a value.',
        src:'example (h : Heap) (l : Loc) (v : Val) (o : Option Val) :\n    upd h l o l = some v := by\n  simp [upd]'},
       {t:'state', src:'error: unsolved goals\nh : Heap\nl : Loc\nv : Val\no : Option Val\n⊢ o = some v'},
       {t:'p', h:'With the operations kept apart, the same statement is <code>write_same</code>, it is unconditional, and the case analysis was done once — when <code>Heap.write</code> and <code>Heap.erase</code> were written as two definitions instead of one. Merging saves two lines here and spends them at every call site. That trade is a general one and this course takes it in the same direction every time: pay at the definition, not at the use.'}
     ]},

    /* ---------------------------------------------------------- domains --- */

    {t:'sec', s:'What each operation does to the domain'},

    {t:'p', h:'The set of addresses at which a heap answers <code>some</code> is its <b>domain of definition</b>, and it is the only feature of a heap that this course ever cuts up. <code>defined h l</code> is the predicate that says <code>l</code> is in it. Each of the four operations can be described by what it does to that set, and every description except <code>Heap.empty</code>\'s is a theorem — proved at the end of this unit, once there is something to prove one from.'},

    {t:'dl', items:[
      {k:'<code>Heap.empty</code>', h:'Domain empty. No address is in it, and <code>Heap.empty x = none</code> holds at every <code>x</code> by reduction alone.'},
      {k:'<code>Heap.singleton l v</code>', h:'Domain exactly <code>{l}</code>. One address in, every other address out — the smallest heap that holds anything.'},
      {k:'<code>Heap.write h l v</code>', h:'Domain the domain of <code>h</code> together with <code>l</code>. If <code>l</code> was already in it the set does not change and only the stored value does; if it was not, the write <i>allocated</i> it.'},
      {k:'<code>Heap.erase h l</code>', h:'Domain the domain of <code>h</code> with <code>l</code> taken out. If <code>l</code> was not in it to begin with, nothing changes at all.'}
    ]},

    {t:'svg', cap:'One heap and three heaps built from it. Filled boxes are the domain; blank boxes are addresses answering <code>none</code>. The changed box in each of the lower three rows is the only difference from the top row.',
     src:'\n<svg viewBox="0 0 600 254" role="img" aria-label="A heap, and the heaps produced by write, erase and singleton">\n  <g class="dg">\n    <text x="176" y="16" class="dg-lab">addresses</text>\n    <g class="dg-t sm">\n      <text x="202" y="34" text-anchor="middle" class="dg-note">0</text>\n      <text x="262" y="34" text-anchor="middle" class="dg-note">1</text>\n      <text x="322" y="34" text-anchor="middle" class="dg-note">2</text>\n      <text x="382" y="34" text-anchor="middle" class="dg-note">3</text>\n      <text x="442" y="34" text-anchor="middle" class="dg-note">4</text>\n      <text x="502" y="34" text-anchor="middle" class="dg-note">5</text>\n    </g>\n    <g class="dg-cells">\n      <text x="8" y="66" class="dg-t">h</text>\n      <rect class="dg-box" x="176" y="44" width="52" height="34" rx="5"/>\n      <rect class="a"      x="236" y="44" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="44" width="52" height="34" rx="5"/>\n      <rect class="a"      x="356" y="44" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="416" y="44" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="44" width="52" height="34" rx="5"/>\n      <text x="262" y="66" text-anchor="middle" class="dg-t">7</text>\n      <text x="382" y="66" text-anchor="middle" class="dg-t">4</text>\n      <text x="540" y="66" class="dg-note">…</text>\n\n      <text x="8" y="118" class="dg-t">h.write 4 9</text>\n      <rect class="dg-box" x="176" y="96" width="52" height="34" rx="5"/>\n      <rect class="a"      x="236" y="96" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="96" width="52" height="34" rx="5"/>\n      <rect class="a"      x="356" y="96" width="52" height="34" rx="5"/>\n      <rect class="b"      x="416" y="96" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="96" width="52" height="34" rx="5"/>\n      <text x="262" y="118" text-anchor="middle" class="dg-t">7</text>\n      <text x="382" y="118" text-anchor="middle" class="dg-t">4</text>\n      <text x="442" y="118" text-anchor="middle" class="dg-t">9</text>\n      <text x="540" y="118" class="dg-note">…</text>\n\n      <text x="8" y="170" class="dg-t">h.erase 1</text>\n      <rect class="dg-box" x="176" y="148" width="52" height="34" rx="5"/>\n      <rect class="b"      x="236" y="148" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="148" width="52" height="34" rx="5"/>\n      <rect class="a"      x="356" y="148" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="416" y="148" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="148" width="52" height="34" rx="5"/>\n      <text x="382" y="170" text-anchor="middle" class="dg-t">4</text>\n      <text x="540" y="170" class="dg-note">…</text>\n\n      <text x="8" y="222" class="dg-t">Heap.singleton 2 5</text>\n      <rect class="dg-box" x="176" y="200" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="236" y="200" width="52" height="34" rx="5"/>\n      <rect class="a"      x="296" y="200" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="356" y="200" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="416" y="200" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="200" width="52" height="34" rx="5"/>\n      <text x="322" y="222" text-anchor="middle" class="dg-t">5</text>\n      <text x="540" y="222" class="dg-note">…</text>\n    </g>\n  </g>\n</svg>'},

    {t:'p', h:'Two things in that picture were impossible one unit ago. The third row has a <i>smaller</i> domain than the first: deallocation is a thing memory can do, and a total function <code>Nat → Nat</code> has no domain to shrink, which is why <code>update</code> had no counterpart of <code>Heap.erase</code>. And all four rows exist at once. <code>h.write 4 9</code> does not modify <code>h</code>; it is a different function, and <code>h</code> goes on answering exactly what it answered before. "The heap after the write" is a term, not an event, and every theorem below is an equation between terms of that kind.'},

    {t:'code', tag:'illustration', cap:'Both lines hold, in the same file, at the same time. The write did not reach back into <code>Heap.empty</code>.',
     src:'example : Heap.empty 3 = none := rfl\nexample : Heap.write Heap.empty 3 7 3 = some 7 := rfl'},

    /* --------------------------------------------------------- ownership --- */

    {t:'p', h:'The second of those lines is the one to look at twice. Address 3 held nothing, and the write put a value there anyway — <code>Heap.write</code> allocates. Read the definition again and you can see why: it consults <code>h</code> only in the else-branch, so at the address being written it never asks what was there. <code>Heap.erase</code> is the same in reverse. Erasing an address that held nothing is permitted and does nothing, and the definition never checks.'},

    {t:'note', kind:'key', title:'Nothing in the model imposes ownership. Preconditions do.',
     h:'On paper you would say that writing to an unallocated address is an error and that freeing one twice is a bug. Neither statement is in any of the four definitions, and putting it there would be a mistake: an operation that could fail returns a different type, and then every equation about it is an equation between failures rather than between heaps. The requirement is restored where it belongs — in the <i>precondition</i> of the rule that governs the command. Unit 23 writes the rule for assignment, and its precondition will say that the address is held; a program that writes where it holds nothing does not satisfy it, and the rule says nothing about that program. This is the first appearance of a pattern the second half of the course runs on: the model is permissive, and the logic is what forbids.'},

    /* ------------------------------------------------------- six equations --- */

    {t:'sec', s:'Six equations, and then the definitions go away'},

    {t:'p', h:'What follows are the six theorems the table predicted, and they are the point of the unit. Each is one <code>simp</code> call, and nothing below is a tactic you have not already used — this unit adds none. That the proofs are short is not a sign that they do not matter: it is what building an interface looks like. After this page, every proof about memory in this course is allowed to know these six equations and nothing else about how the four operations are written, and the four exercises below are where you install them. Three of the six read at the address the operation names and carry no hypothesis; three read somewhere else and need one. Take them one operation at a time, smallest heap first.'},

    {t:'ex',
     id:'m1-1',
     name:'singleton_same',
     hard:false,
     why:'The smallest true statement about memory in the course, and the one Unit 13 turns into an assertion: the points-to predicate is defined from <code>Heap.singleton</code>, and this equation is what makes it usable. It is also your first proof with <code>Option</code> in the codomain, so it is where you find out that widening the codomain changed nothing about the shape of the proof.',
     setup:'The four definitions are in scope, inside the namespace <code>Heap</code>. You are outside it, so write the qualified names. Replace the <code>sorry</code> the editor starts you with.',
     goal:'theorem singleton_same (l : Loc) (v : Val) :\n    Heap.singleton l v l = some v := by',
     hints:[
       'The goal says: the one-cell heap built at <code>l</code> holding <code>v</code>, read at <code>l</code> itself, answers <code>some v</code>. Unfolded, the left-hand side is <code>if l = l then some v else none</code>. There are no hypotheses; <code>l</code> and <code>v</code> are arbitrary.',
       'The condition is an equation between a term and itself, so it holds, so the then-branch is taken, and the then-branch is <code>some v</code>. There is no case to consider. This is <code>update_same</code>\'s argument with a <code>some</code> wrapped round the answer.',
       'One <code>simp</code> call. A definition is not in <code>simp</code>\'s rule set unless you put it there, and the definition you need is the one the goal names.',
       '<code>simp [Heap.singleton]</code>, and nothing after it. It replaces the name by its body, settles <code>l = l</code>, collapses the conditional to <code>some v</code>, and closes <code>some v = some v</code>.'
     ],
     sol:'theorem singleton_same (l : Loc) (v : Val) :\n    Heap.singleton l v l = some v := by\n  simp [Heap.singleton]',
     solNote:'Two rewrites fired: <code>Heap.singleton</code>, and the built-in rule that collapses a conditional whose condition has been settled. <code>simp</code> settles <code>l = l</code> without being asked.',
     expl:'Identical in structure to <code>update_same</code> — the definition unfolds, the condition is an equation between a term and itself, the then-branch is taken — and the only difference is that both sides of the closing equation now sit under <code>some</code>. That difference costs nothing here, because <code>some</code> is applied to both sides. It costs something in the next exercise, where the branch <code>simp</code> has to dispose of puts <code>some</code> on one side and <code>none</code> on the other.',
     walk:[
       {tac:'simp [Heap.singleton]', h:'Replaced <code>Heap.singleton</code> by its body and applied it to <code>l</code>, leaving <code>(if l = l then some v else none) = some v</code>; recognised <code>l = l</code>; collapsed the conditional to its then-branch; closed <code>some v = some v</code>.'}
     ],
     deep:[
       {t:'p', h:'The same proof with the two rules separated, so the goal between them prints. <code>simp only [ … ]</code> runs the rules named and no others.'},
       {t:'trace', title:'Two named rules, one goal state between them',
        start:'l : Loc\nv : Val\n⊢ Heap.singleton l v l = some v',
        steps:[
          {tac:'simp only [Heap.singleton]',
           state:'l : Loc\nv : Val\n⊢ (if True then some v else none) = some v',
           h:'The definition was unfolded and the argument substituted — and the condition is already <code>True</code>, which is <code>simp</code> recognising <code>l = l</code> rather than anything the definition did.'},
          {tac:'simp only [↓reduceIte]',
           state:'No goals.',
           h:'A conditional on <code>True</code> collapses to its then-branch, leaving <code>some v = some v</code>, which closes.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Close to free, but not free. <code>rfl</code> does not close it, and the failure says exactly where reduction gave up:'},
       {t:'code', tag:'sketch', src:'example (l : Loc) (v : Val) :\n    Heap.singleton l v l = some v := by\n  rfl'},
       {t:'state', cap:'Reduction reaches the conditional and stops, because deciding <code>l = l</code> runs <code>Nat.decEq</code>, which takes cases on both arguments, and a variable has no cases. That the same variable stands on both sides makes no difference.',
        src:'error: Tactic `rfl` failed: The left-hand side\n  Heap.singleton l v l\nis not definitionally equal to the right-hand side\n  some v\n\nl : Loc\nv : Val\n⊢ Heap.singleton l v l = some v'}
     ],
     pitfall:'Writing <code>simp</code> with empty brackets. The goal mentions <code>Heap.singleton</code>, <code>simp</code> has no rule about it, and so it cannot see the conditional at all: the answer is <code>`simp` made no progress</code>, which reads as though the goal were hard when in fact <code>simp</code> never got inside it. Dropping the namespace inside the bracket is the second version, and it is worse than it looks. <code>simp [empty]</code> reports <code>Unknown identifier `empty`</code> and then <code>`simp` made no progress</code> — two messages, and the first one tells you what to fix. <code>simp [singleton]</code> reports only the second, because <code>singleton</code> is a name Lean already has: <code>@singleton</code> is core\'s <code>Singleton.singleton</code>, and <code>simp</code> takes the rules of a function that has nothing to do with heaps. A short name that resolves to the wrong thing fails more quietly than one that does not resolve at all. The third version copies the whole term out of the goal: <code>simp [Heap.singleton l v]</code>. What goes in the bracket is a rule — an equation, or something that unfolds to one — and <code>Heap.singleton l v</code> is a heap. Lean says so exactly: <code>Invalid simp theorem: Expected a proposition, but found Heap</code>, and then <code>`simp` made no progress</code>, because after rejecting the argument it was left with no rules again.',
     variants:'Change the read point to a variable <code>x</code> and the statement becomes false without a hypothesis: at any <code>x</code> other than <code>l</code> the one-cell heap answers <code>none</code>, not <code>some v</code>. Add a hypothesis <code>hx : x = l</code> instead and the theorem is true again, with the proof <code>simp [Heap.singleton, hx]</code> — the extra rule doing what <code>simp</code> did for free here. Replace <code>some v</code> on the right by <code>v</code> and nothing happens: Lean inserts the <code>some</code> for you and proves the same theorem. The evidence is the goal display, which comes back reading <code>⊢ Heap.singleton l v l = some v</code> whichever way you typed it. That silent repair is convenient once and misleading afterwards — the codomain really is <code>Option Val</code>, and in a statement where the wrapper is the point you will want to have written it.'
    },

    {t:'p', h:'Reading the same heap anywhere else gives <code>none</code> — a one-cell heap holds one cell and no more. Stating that needs a second address and a hypothesis saying it is a different one, and the orientation of that hypothesis has to match the conditional in the definition.'},

    {t:'ex',
     id:'m1-2',
     name:'singleton_other',
     hard:false,
     why:'This is the equation that says a one-cell heap is <i>only</i> one cell, and everything that treats heaps as resources rests on it: Unit 08 needs it to decide when two one-cell heaps overlap, and Unit 13 needs it to say that owning a cell means owning nothing else. Its <code>simp</code> also leaves a residue you will meet in almost every failed heap proof, and this is the cheapest place to learn to read one.',
     setup:'The hypothesis is <code>hne : x ≠ l</code>, in that order: the point being read on the left, the heap\'s own address on the right. Look at the conditional in <code>Heap.singleton</code> before deciding the order does not matter.',
     goal:'theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.singleton l v x = none := by',
     hints:[
       'The goal says: the one-cell heap built at <code>l</code>, read at a point <code>x</code> known to differ from <code>l</code>, answers <code>none</code>. Unfolded, the left-hand side is <code>if x = l then some v else none</code>. The context holds <code>hne : x ≠ l</code>, which is <code>¬ (x = l)</code>.',
       'The condition of the conditional is exactly the proposition the hypothesis denies, so the else-branch is taken, and the else-branch is <code>none</code>, which is the right-hand side. No case split: the case was decided in the statement.',
       'One <code>simp</code> call again, and its brackets take more than definitions. A hypothesis put there is used as a rewrite rule, and what <code>simp</code> does with a negated equation is rewrite the equation it denies to <code>False</code> wherever it occurs.',
       '<code>simp [Heap.singleton, hne]</code>, and nothing after it. Leave <code>hne</code> out and the goal is not left unfinished in the usual way — <code>simp</code> hands back a strictly smaller one, and the panel below says which.'
     ],
     sol:'theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.singleton l v x = none := by\n  simp [Heap.singleton, hne]',
     solNote:'Three rules where the last proof had two, and the extra one is neither a definition nor a lemma: it is a hypothesis out of the local context. Putting it in the bracket is the only way <code>simp</code> looks at it — a hypothesis sitting in the context is not a rule until you name it.',
     expl:'Three rules against <code>singleton_same</code>\'s two, and the extra one is the hypothesis. The interesting part is what happens when it is missing. <code>simp</code> does not give up on the conditional: it splits it, discovers that the then-branch would require <code>some v = none</code>, refutes that outright because <code>some</code> and <code>none</code> are different constructors, and reports what is left — the bare disequality it could not supply. The residue is therefore not "the goal minus some progress"; it is precisely the missing hypothesis, written out.',
     walk:[
       {tac:'simp [Heap.singleton, hne]', h:'Unfolded <code>Heap.singleton</code> to leave <code>(if x = l then some v else none) = none</code>; used <code>hne</code> to rewrite the condition <code>x = l</code> to <code>False</code>; collapsed the conditional to its else-branch <code>none</code>; closed <code>none = none</code>.'}
     ],
     deep:[
       {t:'trace', title:'Three named rules, two goal states between them',
        start:'l x : Loc\nv : Val\nhne : x ≠ l\n⊢ Heap.singleton l v x = none',
        steps:[
          {tac:'simp only [Heap.singleton]',
           state:'l x : Loc\nv : Val\nhne : x ≠ l\n⊢ (if x = l then some v else none) = none',
           h:'Unfolded and stopped. Unlike <code>singleton_same</code>, the condition survives: <code>x</code> and <code>l</code> are two different variables and nothing about the shape of the term decides them.'},
          {tac:'simp only [hne]',
           state:'l x : Loc\nv : Val\nhne : x ≠ l\n⊢ (if False then some v else none) = none',
           h:'The entire contribution of the hypothesis, and it is one rewrite: the proposition in the condition became <code>False</code>.'},
          {tac:'simp only [↓reduceIte]',
           state:'No goals.',
           h:'The else-branch this time, leaving <code>none = none</code>.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Now the same call with <code>hne</code> withheld:'},
       {t:'code', tag:'sketch', src:'example (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.singleton l v x = none := by\n  simp [Heap.singleton]'},
       {t:'state', cap:'The hypothesis is sitting in the context, unused. <code>simp</code> does not go looking for it.',
        src:'error: unsolved goals\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ ¬x = l'},
       {t:'p', h:'That the residue is the hypothesis itself, and not an implication with the hypothesis on the left, is a fact about this goal and not about <code>simp</code>. It can be checked directly: the two are the same proposition.'},
       {t:'code', tag:'illustration', cap:'Closes. So <code>simp [Heap.singleton]</code> reduces the goal exactly to the disequality, losing nothing and adding nothing.',
        src:'example (l x : Loc) (v : Val) : Heap.singleton l v x = none ↔ ¬ x = l := by\n  simp [Heap.singleton]'}
     ],
     pitfall:'Stating the hypothesis as <code>l ≠ x</code>. Same mathematical fact, different term, and the conditional in the goal asks about <code>x = l</code>. Lean then answers twice: first the residue, identical to what you get with no hypothesis at all — which is the tell — and then, separately, <code>warning: This simp argument is unused:</code> naming <code>hne</code>. The second message is the diagnosis; the repair is <code>hne.symm</code>.',
     variants:'Drop <code>hne</code> and the statement is false at exactly one point: take <code>x = l</code> and the left-hand side is <code>some v</code>. Every other address still satisfies it, which is what the residue was telling you. Replace <code>none</code> on the right by <code>some w</code> for a fresh <code>w</code> and the statement is false everywhere the hypothesis allows: <code>simp [Heap.singleton, hne]</code> reduces it to <code>⊢ False</code>, which is <code>simp</code> saying that it got all the way to the contradiction and there is nothing left to assume.'
    },

    {t:'p', h:'The same two questions of <code>Heap.write</code>. The statements are <code>update_same</code> and <code>update_other</code> with <code>Option</code> in the codomain, and the proofs are those proofs unchanged — but the second residue is not the one the last exercise gave you.'},

    {t:'ex',
     id:'m1-3',
     name:'write_same / write_other',
     hard:false,
     why:'These two are the entire content of the assignment rule. Unit 06 combines them into a single equation between whole heaps — writing to the cell of a one-cell heap gives a one-cell heap — and Unit 23\'s rule for assignment is that equation, applied once, with nothing else in the proof. Every piece of pointwise reasoning that rule would otherwise need is being done here instead, in the heap layer, which is why the Unit 23 proof is three lines and contains no conditional at all.',
     setup:'Two theorems in one editor. The first has no hypothesis; the second has <code>hne : x ≠ l</code>, again with the read point on the left. Replace each <code>sorry</code>.',
     goal:'theorem write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.write h l v l = some v := by\n  sorry\n\ntheorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.write h l v x = h x := by',
     hints:[
       'The first goal says: after writing <code>v</code> at <code>l</code>, reading at <code>l</code> gives <code>some v</code>; unfolded, <code>if l = l then some v else h l</code>. The second says: reading anywhere else gives what <code>h</code> gave; unfolded, <code>if x = l then some v else h x</code>, with <code>hne : x ≠ l</code> in the context. The heap <code>h</code> is arbitrary in both — nothing is assumed about what it held.',
       'In the first the condition is an equation between a term and itself, so the then-branch is taken. In the second the hypothesis denies the condition, so the else-branch is taken and it is <code>h x</code> on the nose. Neither needs a case split, and neither cares what <code>h</code> held at <code>l</code> before.',
       'One <code>simp</code> call each, with the same brackets you used for the two <code>singleton</code> laws and the definition changed. The second one needs its hypothesis by name.',
       '<code>simp [Heap.write]</code> and <code>simp [Heap.write, hne]</code>. Leave <code>hne</code> out of the second and what comes back is <code>⊢ x = l → some v = h x</code>, which is <i>not</i> the residue <code>singleton_other</code> gave you.'
     ],
     sol:'theorem write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.write h l v l = some v := by\n  simp [Heap.write]\n\ntheorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.write h l v x = h x := by\n  simp [Heap.write, hne]',
     solNote:'Character for character the proofs of <code>update_same</code> and <code>update_other</code>, with one name changed. That is the whole of what widening the codomain cost.',
     expl:'The two proofs are the two branches of one conditional, each pinned by the statement rather than by a split. The part to extract is the difference between this exercise\'s residue and the last one\'s. Withhold the hypothesis from <code>singleton_other</code> and <code>simp</code> hands back <code>⊢ ¬x = l</code>; withhold it here and it hands back <code>⊢ x = l → some v = h x</code>. In both cases <code>simp</code> split the conditional and both cases left the then-branch to be discharged. In <code>singleton_other</code> that branch was <code>some v = none</code>, which <code>simp</code> refutes on its own — <code>some</code> and <code>none</code> are different constructors, which is Unit 02\'s <code>some_ne_none</code> — so the branch died and only its condition was left standing, negated. Here the branch is <code>some v = h x</code>, and <code>h</code> is an arbitrary heap: nothing refutes it and nothing proves it, so the implication survives intact. The extra step came from the shape of the goal, not from the tactic trying harder.',
     walk:[
       {tac:'simp [Heap.write]', h:'<i>In <code>write_same</code>.</i> Unfolded <code>Heap.write</code> at <code>l</code>, leaving <code>(if l = l then some v else h l) = some v</code>; settled <code>l = l</code>; collapsed to the then-branch; closed <code>some v = some v</code>. The else-branch <code>h l</code> was never looked at, which is why the theorem says nothing about what was there before.'},
       {tac:'simp [Heap.write, hne]', h:'<i>In <code>write_other</code>.</i> Unfolded to <code>(if x = l then some v else h x) = h x</code>; used <code>hne</code> to rewrite the condition to <code>False</code>; collapsed to the else-branch <code>h x</code>; closed <code>h x = h x</code>. The right-hand side <code>h x</code> was never touched — it is the same subterm before and after, which is why the equation closes by <code>rfl</code> once the conditional is gone.'}
     ],
     deep:[
       {t:'trace', title:'write_other, three named rules',
        start:'h : Heap\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ h.write l v x = h x',
        steps:[
          {tac:'simp only [Heap.write]',
           state:'h : Heap\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ (if x = l then some v else h x) = h x',
           h:'The display switched from <code>h.write l v x</code> to an explicit conditional the moment the name was unfolded. Same term throughout.'},
          {tac:'simp only [hne]',
           state:'h : Heap\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ (if False then some v else h x) = h x',
           h:'One rewrite, inside the condition. Nothing else in the goal moved.'},
          {tac:'simp only [↓reduceIte]', state:'No goals.',
           h:'Else-branch, leaving <code>h x = h x</code>.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The residue, with <code>hne</code> withheld:'},
       {t:'code', tag:'sketch', src:'example (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.write h l v x = h x := by\n  simp [Heap.write]'},
       {t:'state', src:'error: unsolved goals\nh : Heap\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ x = l → some v = h x'},
       {t:'cmp',
        left:{t:'<code>singleton_other</code> without its hypothesis',
          h:'<p>Residue: <code>⊢ ¬x = l</code></p><p>The surviving branch is <code>some v = none</code>. Different constructors, so <code>simp</code> refutes it and deletes the branch; the condition of a conditional whose then-branch is impossible must itself be false, and that is the whole residue.</p>'},
        right:{t:'<code>write_other</code> without its hypothesis',
          h:'<p>Residue: <code>⊢ x = l → some v = h x</code></p><p>The surviving branch is <code>some v = h x</code>, with <code>h</code> arbitrary. It is neither refutable nor provable, so it stays, and it stays under the condition that produced it. Read it as a bill: <i>if the two addresses coincide you still owe me this equation</i>.</p>'}},
       {t:'p', h:'Both bills are paid the same way, by naming a disequality in the bracket. What differs is how much of the goal <code>simp</code> could dispose of before presenting it, and that depended entirely on whether the else-branch of the definition was a constructor or an unknown.'}
     ],
     pitfall:'Expecting <code>write_same</code> to need a hypothesis saying that <code>l</code> was allocated. It does not, and adding one would be adding a hypothesis no proof consumes. <code>Heap.write</code> never consults <code>h</code> at the address it writes to, so the equation holds whatever <code>h l</code> was, including <code>none</code>. Write <code>(hd : defined h l)</code> in anyway and the proof still closes, but Lean objects: <code>warning: Variable name `hd` is not explicitly referenced.</code> Take that as the instruction it is. An unconsumed hypothesis is one every later lemma quoting this one has to manufacture, for nothing. The other mistake this exercise invites is mechanical: two theorems in one editor, and the bracket from the second pasted into the first. <code>simp [Heap.write, hne]</code> in <code>write_same</code> gives <code>Unknown identifier `hne`</code> — the name exists, but in the other theorem\'s context, and a context does not survive the blank line between two declarations.',
     variants:'Reverse <code>write_other</code>\'s hypothesis to <code>l ≠ x</code> and the proof stops closing, with the two-message pattern from <code>singleton_other</code>: the same residue as with no hypothesis, plus an unused-argument warning; <code>hne.symm</code> repairs it. Drop it entirely and the statement is false, at exactly the address <code>x = l</code>, where the left-hand side is <code>some v</code> and the right is whatever <code>h</code> held. The cheapest witness is <code>Heap.empty</code>: at <code>x = l</code> the left is <code>some v</code> and the right is <code>none</code>, and <code>Heap.empty</code> is a heap you can write down without assuming anything. Change <code>write_same</code>\'s right-hand side to <code>h l</code> and it is false in the other direction: reading at the address you wrote to gives what you wrote, not what was there.'
    },

    {t:'detail', title:'What a <code>Heap.write</code> that refused to allocate would cost', open:false,
     blocks:[
       {t:'p', h:'The permissive definition was a choice, and the alternative is writable. Make the operation check the domain and report failure by returning an <code>Option Heap</code>:'},
       {t:'code', tag:'illustration', cap:'The same fact as <code>write_same</code>, for the checking version. It is true, and this is what it takes.',
        src:'def writeOwned (h : Heap) (l : Loc) (v : Val) : Option Heap :=\n  if h l = none then none else some (Heap.write h l v)\n\ntheorem writeOwned_same (h h\' : Heap) (l : Loc) (v : Val)\n    (hw : writeOwned h l v = some h\') : h\' l = some v := by\n  unfold writeOwned at hw\n  by_cases hl : h l = none\n  · simp [hl] at hw\n  · simp [hl] at hw\n    rw [← hw]\n    simp [Heap.write]'},
       {t:'p', h:'Three lines became nine, and the statement gained a second heap variable and a hypothesis relating it to the first. Nothing in those extra lines is about memory; they are the unwrapping of the <code>Option</code>, done once here and repeated in every lemma about writing, and again in every lemma about a command containing a write. Five equations between heaps in Unit 06 would become five equations between <code>Option Heap</code>s, and each of them would carry the same case split.'},
       {t:'p', h:'What is bought is a check that is redundant by the time it fires. The rule for assignment will only ever be applied to a state its precondition accepts, and that precondition already says the address is held. So the definition would be paying, on every line of every proof, for a guarantee the logic supplies for free.'}
     ]},

    {t:'p', h:'The last pair is the one <code>update</code> could not have: giving a cell up.'},

    {t:'ex',
     id:'m1-4',
     name:'erase_same / erase_other',
     hard:false,
     why:'Deallocation, in two equations, and the same division of labour as the two <code>write</code> laws: one says what happened at the address, the other says nothing happened anywhere else. Unit 06 combines them into the statement that erasing the cell of a one-cell heap leaves the empty heap, and Unit 23\'s rule for freeing is that statement. The uniformity is the point — by the fourth exercise you should be able to write down both statements before reading them.',
     setup:'Again two theorems, and again only the second has a hypothesis. Nothing is assumed about whether <code>l</code> was in the domain of <code>h</code> to begin with.',
     goal:'theorem erase_same (h : Heap) (l : Loc) :\n    Heap.erase h l l = none := by\n  sorry\n\ntheorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :\n    Heap.erase h l x = h x := by',
     hints:[
       'The first goal says: after erasing <code>l</code>, reading at <code>l</code> gives <code>none</code>; unfolded, <code>if l = l then none else h l</code>. The second says reading anywhere else is unaffected; unfolded, <code>if x = l then none else h x</code>, with <code>hne : x ≠ l</code>. Neither statement mentions a value, because erasing does not produce one.',
       'The same two branches as every other law on this page: the first is pinned to the then-branch by an equation between a term and itself, the second to the else-branch by the hypothesis. Nothing new is required and nothing about the previous four proofs changes.',
       'One <code>simp</code> each, brackets as before, with the definition of this operation and — for the second only — the hypothesis.',
       '<code>simp [Heap.erase]</code> and <code>simp [Heap.erase, hne]</code>. Withhold <code>hne</code> from the second and the residue is <code>⊢ x = l → none = h x</code>, which is the <code>write_other</code> pattern rather than the <code>singleton_other</code> one.'
     ],
     sol:'theorem erase_same (h : Heap) (l : Loc) :\n    Heap.erase h l l = none := by\n  simp [Heap.erase]\n\ntheorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :\n    Heap.erase h l x = h x := by\n  simp [Heap.erase, hne]',
     solNote:'That is the interface complete: six equations, four proofs, one tactic. From here on the definitions above are not the thing you reason with.',
     expl:'<code>erase_same</code> is unconditional, and what it does not say matters as much as what it does. It does not say the address was allocated and is now free; it says that after the operation, reading there gives <code>none</code>, whatever was there before. Erasing an address that already held nothing satisfies it too. The domain shrank, or it did not, and the equation is indifferent — which is exactly the permissiveness the key note above described, met a second time and now in a theorem you proved.',
     walk:[
       {tac:'simp [Heap.erase]', h:'<i>In <code>erase_same</code>.</i> Unfolded <code>Heap.erase</code> at <code>l</code>, leaving <code>(if l = l then none else h l) = none</code>; settled <code>l = l</code>; collapsed to the then-branch <code>none</code>; closed <code>none = none</code>. The else-branch <code>h l</code> was never consulted, which is why no hypothesis about the old contents appears.'},
       {tac:'simp [Heap.erase, hne]', h:'<i>In <code>erase_other</code>.</i> Unfolded to <code>(if x = l then none else h x) = h x</code>; used <code>hne</code> to rewrite the condition to <code>False</code>; collapsed to the else-branch; closed <code>h x = h x</code>. Character for character the second half of <code>m1-3</code>, with one name changed and the then-branch now <code>none</code> instead of <code>some v</code> — which is why withholding <code>hne</code> here leaves <code>⊢ x = l → none = h x</code> and not the negated equation <code>singleton_other</code> left.'}
     ],
     deep:[
       {t:'trace', title:'erase_same, two named rules',
        start:'h : Heap\nl : Loc\n⊢ h.erase l l = none',
        steps:[
          {tac:'simp only [Heap.erase]',
           state:'h : Heap\nl : Loc\n⊢ (if True then none else h l) = none',
           h:'Unfolded, and the condition <code>l = l</code> is already <code>True</code> — the same free step as in <code>singleton_same</code> and <code>write_same</code>.'},
          {tac:'simp only [↓reduceIte]', state:'No goals.',
           h:'Then-branch, leaving <code>none = none</code>.'}
        ],
        done:'No goals.'},
       {t:'trace', title:'erase_other, three named rules',
        start:'h : Heap\nl x : Loc\nhne : x ≠ l\n⊢ h.erase l x = h x',
        steps:[
          {tac:'simp only [Heap.erase]',
           state:'h : Heap\nl x : Loc\nhne : x ≠ l\n⊢ (if x = l then none else h x) = h x',
           h:'Two variables in the condition and nothing to settle them.'},
          {tac:'simp only [hne]',
           state:'h : Heap\nl x : Loc\nhne : x ≠ l\n⊢ (if False then none else h x) = h x',
           h:'The hypothesis, spent.'},
          {tac:'simp only [↓reduceIte]', state:'No goals.', h:'Else-branch, leaving <code>h x = h x</code>.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Erasing something that was not there is a no-op, and the fact needs the three-move shape from Unit 04 rather than a lookup law, because it is an equation between two <i>heaps</i> and not between two lookups:'},
       {t:'code', tag:'illustration', cap:'One instance of it, and the first equation between whole heaps in this course — the shape Unit 06 is made of.',
        src:'example : Heap.erase Heap.empty 3 = Heap.empty := by\n  funext x\n  by_cases hx : x = 3 <;> simp [Heap.erase, Heap.empty, hx]'},
       {t:'p', h:'Dropping <code>hne</code> from <code>erase_other</code> leaves more than a stuck proof. It leaves a false statement, and the witness refuting it has to be a heap that actually held the address. <code>Heap.empty</code> will not do — erasing from it changes nothing anywhere, so the unrestricted claim holds for that heap. The smallest heap that does refute it is the one-cell heap.'},
       {t:'code', tag:'illustration', cap:'The unrestricted claim, refuted. <code>hall</code> is instantiated at the one-cell heap at address 3 and read at address 3, which is the point the hypothesis was excluding; that gives <code>hbad : (Heap.singleton 3 7).erase 3 3 = Heap.singleton 3 7 3</code>, and <code>simp</code> evaluates the two sides to <code>none</code> and <code>some 7</code>.',
        src:'example : ¬ ∀ (h : Heap) (l x : Loc), Heap.erase h l x = h x := by\n  intro hall\n  have hbad := hall (Heap.singleton 3 7) 3 3\n  simp [Heap.erase, Heap.singleton] at hbad'}
     ],
     pitfall:'Writing <code>erase_other</code>\'s conclusion as <code>Heap.erase h l x = none</code>. It reads plausibly — the heap has had something erased from it — and it is false, because erasing at <code>l</code> does nothing at <code>x</code>. <code>simp [Heap.erase, hne]</code> takes it as far as <code>⊢ h x = none</code> and stops there, which is the giveaway: the goal that survives is a claim about <code>h</code>, and no theorem about <code>Heap.erase</code> can settle a claim about <code>h</code>. <code>Heap.erase h l</code> is not <code>Heap.empty</code>; it is <code>h</code> with one address removed.',
     variants:'Reverse <code>erase_other</code>\'s hypothesis and you get the unused-argument warning and the unhelpful residue, repaired by <code>hne.symm</code>, exactly as in the two previous exercises. Drop it and the statement fails at <code>x = l</code>, where the left-hand side is <code>none</code> and the right is <code>h l</code> — false only when <code>h l</code> is <code>some</code> of something, so a counterexample needs an <code>h</code> that actually held the address; <code>Heap.singleton 3 7</code> at <code>l = x = 3</code> is the smallest one, and it is refuted in Lean in the panel above. Replace <code>none</code> in <code>erase_same</code> by <code>h l</code> and you have written that the erase changed nothing at <code>l</code>. <code>simp [Heap.erase]</code> gets as far as <code>⊢ none = h l</code> and stops, which is the honest answer: the claim holds exactly when <code>h l</code> was already <code>none</code>, and a hypothesis saying so is what closes it.'
    },

    {t:'detail', title:'The honest definition of a partial function, and what it does to <code>Heap.erase</code>', open:false,
     blocks:[
       {t:'p', h:'Unit 00 gave the reason for widening the codomain rather than packaging a domain, in the abstract. Now that the operations exist the cost can be pointed at. Packaged, a heap is a pair: a predicate saying which addresses are held, and a function defined only where that predicate holds. In Lean that is a <b>structure</b> — a named record with one field per component, written with <code>where</code> and a list of fields and their types.'},
       {t:'code', tag:'illustration', cap:'Compiles. The second field\'s type mentions the first field, which is where the trouble is.',
        src:'structure PHeap where\n  dom : Loc → Prop\n  val : (l : Loc) → dom l → Val'},
       {t:'p', h:'Under this definition <code>Heap.erase</code> cannot be written as a function on the second component alone: removing an address changes <code>dom</code>, and <code>val</code>\'s <i>type</i> mentions <code>dom</code>, so the new <code>val</code> lives in a different type from the old one. Every equation between two such heaps then splits into an equation between the domains and an equation between the value functions — and the second one does not even typecheck until the first has been proved. Every lemma acquires a transport along that proof, and <code>rw</code>, which matches text, stops finding its patterns.'},
       {t:'p', h:'Against that, the six equations you proved above are equations between <code>Option Val</code>s, and the three-move shape closes every equation between whole heaps. Faithfulness was traded for a proof method that does not break down.'},
       {t:'p', h:'One further consequence of the choice, and this one is about the keyword rather than the encoding. <code>Heap</code>, <code>Loc</code> and <code>Val</code> were declared with <code>abbrev</code>, which makes Lean unfold the names whenever it needs to. Declare the model with <code>def</code> instead and the four definitions above stop compiling — not because of <code>funext</code>, but because the conditional in each of them needs Lean to find a way of deciding <code>x = l</code>, and instance search looks through <code>abbrev</code> and refuses to look through <code>def</code>:'},
       {t:'code', tag:'sketch', cap:'Deliberately broken, and compiled on its own rather than against this chapter\'s context, since it redeclares the model.',
        src:'def Loc   := Nat\ndef Val   := Nat\ndef Heap  := Loc → Option Val\n\ndef Heap.write (h : Heap) (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else h x'},
       {t:'state', cap:'As far as instance search is concerned <code>Loc</code> is now a fresh type about which nothing decidable is known.',
        src:'error(lean.synthInstanceFailed): failed to synthesize instance of type class\n  Decidable (x = l)\n\nHint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.'}
     ]},

    {t:'detail', title:'Nothing here says a heap is finite', open:false,
     blocks:[
       {t:'p', h:'A <code>Heap</code> is any function at all from <code>Loc</code> to <code>Option Val</code>, and there is no constraint anywhere requiring all but finitely many addresses to answer <code>none</code>. Real memory is finite; this model is not, and the omission is deliberate.'},
       {t:'code', tag:'illustration', cap:'A perfectly good heap, in which every address is allocated.',
        src:'def everywhere : Heap := fun _ => some 1\n\nexample : ¬ ∃ l, everywhere l = none := by\n  intro ⟨l, hl⟩\n  simp [everywhere] at hl'},
       {t:'p', h:'Requiring finiteness would mean carrying a proof of it through every operation and — much worse — through every way of taking a heap apart, since both halves of a split would have to be shown finite. Nothing in the next thirty units needs it. The one thing it buys is a fresh address: in a finite heap some address is guaranteed to be unallocated, which is what an allocator needs in order to return anything. That is why the allocation of new cells is the one command this course does not verify, and why Unit 38 has to say what would change.'}
     ]},

    /* ------------------------------------------------------- the discipline --- */

    {t:'sec', s:'The interface, and the rule about it'},

    {t:'p', h:'The domain claims left standing above can now be settled, and settling them is the first test of what the six equations are for. A positive claim is an existential, so its proof supplies a witness — the value stored — together with the equation putting it there. A negative claim is a negation, so <code>intro</code> hands over a witness and the work is refuting it: the relevant law says that address answers <code>none</code>, and <code>some w = none</code> is refuted by Unit 02\'s <code>some_ne_none</code>. <code>Heap.empty</code> is absent below because it has no law to cite — <code>Heap.empty l</code> reduces to <code>none</code>, and the same refutation goes through with nothing rewritten at all.'},

    {t:'code', tag:'illustration', cap:'Four theorems about domains, and no proof names an operation. Every step is one of the six equations or Unit 02\'s constructor distinctness — which is what the rule below asks of every proof from here on.',
     src:'example (l : Loc) (v : Val) : defined (Heap.singleton l v) l :=\n  ⟨v, singleton_same l v⟩\n\nexample (l x : Loc) (v : Val) (hne : x ≠ l) : ¬ defined (Heap.singleton l v) x := by\n  intro ⟨w, hw⟩\n  rw [singleton_other l x v hne] at hw\n  exact absurd hw.symm (some_ne_none w)\n\nexample (h : Heap) (l : Loc) (v : Val) : defined (Heap.write h l v) l :=\n  ⟨v, write_same h l v⟩\n\nexample (h : Heap) (l : Loc) : ¬ defined (Heap.erase h l) l := by\n  intro ⟨v, hv⟩\n  rw [erase_same] at hv\n  exact absurd hv.symm (some_ne_none v)'},

    {t:'note', kind:'key', title:'From here on, the definitions are not the thing you reason with',
     h:'Six equations replace four definitions. That replacement is the point of the unit, and it comes with a rule: <code>Heap.write</code>, <code>Heap.erase</code>, <code>Heap.singleton</code> and <code>Heap.empty</code> do not go into a <code>simp</code> bracket again, except while the algebra of the operations themselves is still being established — which is Unit 06, and nowhere after it. Every proof from Unit 07 onwards cites the six laws by name. The reason is not tidiness. A proof that unfolds a definition is a proof about how the definition was written, and this one could have been written with the conditional the other way round, or with <code>x</code> and <code>l</code> swapped in it; a proof that cites <code>write_other</code> would survive that edit, and a proof that unfolds <code>Heap.write</code> would not. Unit 38 changes the model outright, and what survives is exactly what was proved through an interface.'},

    {t:'dod', h:'You can read <code>h l = none</code> in both of its senses and say why nothing in the model separates them. You can generate the four operations from the two-by-two table and say which of them has lookup laws and why <code>Heap.empty</code> has none. You can declare inside a <code>namespace</code>, resolve <code>Heap.write</code> from outside it, and read <code>h.write l v</code> in a goal as the term it abbreviates. You can prove all six lookup equations in one <code>simp</code> each, and when one of them fails you can read the residue and say whether it is <code>⊢ ¬x = l</code> or <code>⊢ x = l → some v = h x</code>, and what that difference tells you about the else-branch of the definition. You can say what each operation does to the domain, and that none of them asks permission — the requirement arrives later, in a precondition.'},

    {t:'p', h:'Six equations, and none of them mentions more than one lookup. What happens when you write twice to the same cell, or to two different cells? Those two facts are what the assignment rule and the frame rule are made of.'}

  ]
});
