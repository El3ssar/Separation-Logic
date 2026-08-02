registerChapter({
  id: 'exec',
  num: '19',
  phase: 'Phase 3 · Programs and their semantics',
  title: 'Running a command is a relation',
  blurb: 'Lean refuses to accept the interpreter, and the refusal is right for a reason the error message does not mention. What replaces it is a set of ten inference rules — and the first proofs you can do with them.',

  orient: {
    youWill: [
      'Read Lean\'s <code>fail to show termination</code> report on the naive interpreter and say which two parameters it tried and why each failed.',
      'Say what an <code>Option</code>-valued interpreter cannot express, and why abandoning the answer removes the termination problem instead of postponing it.',
      'Read <code>inductive Exec : Cmd → State → State → Prop</code> as ten inference rules, and read a proof of <code>Exec c s s\'</code> as a finite tree built out of the constructors.',
      'Say what distinguishes an <b>index</b> from a <b>parameter</b>, and produce the error Lean gives when you get it wrong.',
      'Take a derivation apart with <code>cases h</code>, read the <code>case</code> tag it prints, and name an inaccessible hypothesis with <code>rename_i</code>.',
      'Prove that a program which reads an unallocated address has <i>no</i> final state at all, and say why that means the semantics needs no error value.'
    ],
    needs: [
      'Unit 18: <code>Cmd</code>, <code>State</code>, <code>Atom.eval</code>, <code>BExpr.eval</code>, <code>Store.set</code>, <code>;;</code>, and structural recursion.',
      'Unit 02: <code>inductive</code>, constructors, pattern-matching <code>def</code>, and <code>cases</code> on a value.',
      'Unit 05: <code>Heap.empty</code>, <code>Heap.write</code>, <code>Heap.erase</code>, <code>Heap.singleton</code>.',
      'Unit 01: <code>∃</code>, <code>∧</code>, the anonymous constructor <code>⟨…⟩</code> and its flattening.'
    ],
    payoff: 'Every specification in the rest of the course is a statement about <code>Exec</code>. Unit 22 builds derivations out of these ten constructors; from Unit 24 on, nearly every proof begins by taking one apart, in exactly the way the four exercises below do. The last of them is the move the locality proof for <code>;;</code> opens with.'
  },

  blocks: [

    /* ============================================ the function that fails === */

    {t:'p', h:'Take the function first. Running a command turns one state into another, some commands have no answer, and Unit 00 already fixed how this course writes a function that may have no answer: widen the codomain. So the semantics is a <code>def</code> of type <code>Cmd → State → Option State</code>, written by pattern matching on the command, one clause per constructor, in the same style as <code>Atom.eval</code>.'},

    {t:'p', h:'Most of the clauses write themselves. <code>skip</code> hands back the state it was given. <code>assign x e</code> hands back the state with its store changed at <code>x</code>. <code>load x l</code> looks <code>l</code> up in the heap and answers <code>none</code> if nothing is there. <code>seq</code> runs the first command, and if that produced a state, runs the second one from it. Every recursive call in those clauses is at a <i>component</i> of the command it was given, so the recursion is structural and Lean asks for nothing. One clause is not like that.'},

    {t:'code', tag:'sketch', cap:'The <code>loop</code> clause calls itself at the <b>same</b> command. Everything else here is abbreviated to the catch-all last line, because the loop is the whole of the problem.',
     src:'def runBad : Cmd → State → Option State\n  | .skip, s => some s\n  | .loop b c, s =>\n      match b.eval s.store with\n      | true  =>\n          match runBad c s with\n          | some s\' => runBad (.loop b c) s\'\n          | none    => none\n      | false => some s\n  | _, _ => none'},

    {t:'state', cap:'What Lean answers. The position prefix is dropped, a convention every quoted message on this page follows. The last four lines are not part of the message — they are a goal, left for you.',
     src:'error: fail to show termination for\n  runBad\nwith errors\nfailed to infer structural recursion:\nCannot use parameter #1:\n  failed to eliminate recursive application\n    runBad (Cmd.loop b c) s\'\nCannot use parameter #2:\n  the type State does not have a `.brecOn` recursor\n\n\nfailed to prove termination, possible solutions:\n  - Use `have`-expressions to prove the remaining goals\n  - Use `termination_by` to specify a different well-founded relation\n  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal\nb : BExpr\nc : Cmd\ns s\' : State\n⊢ False'},

    {t:'p', h:'Lean tried structural recursion on each argument in turn and named both failures. Parameter #1 is the command: the offending call is <code>runBad (Cmd.loop b c) s\'</code>, and <code>Cmd.loop b c</code> is not a component of <code>Cmd.loop b c</code> — it is the thing itself, so nothing shrinks. Parameter #2 is the state, and a <code>structure</code> has one constructor and no recursion in it, so there is no smaller state to recurse into; that is what "does not have a <code>.brecOn</code> recursor" says. Having failed twice, Lean falls back on well-founded recursion, cannot find an order either, and hands you the residue as a goal: prove <code>False</code>.'},

    {t:'p', h:'The message names the repair. <code>termination_by</code> lets you supply a quantity that decreases at every recursive call, and Lean then only asks you to prove that it does. There is no such quantity here, and the reason is not a shortcoming of Lean: the program really might not stop, and a quantity that decreased at every step of a non-terminating run would be a natural number descending forever. The only way to get one is to invent it — carry a counter alongside the command, decrement it at each call, and answer <code>none</code> when it runs out. That is a real construction and Unit 21 builds it, but look at what it does to the type: the answer now depends on a number that is not part of the program.'},

    /* ------------------------------------------------- the second objection --- */

    {t:'p', h:'Set the termination problem aside, because there is a second objection to <code>Cmd → State → Option State</code> which survives every repair to the first. The result type has one way to say "no state". A program that reads an unallocated address gets <code>none</code>. A program that never stops gets <code>none</code>. Those are different things — one is the memory error this whole course is about, the other is a program that never gets round to being wrong — and the type has no room to tell them apart.'},

    {t:'code', tag:'illustration', cap:'A guard that is true whatever the store says, over a body that changes nothing. This command does not fault and does not finish.',
     src:'def forever : Cmd := .loop (.equals (.const 0) (.const 0)) .skip\n\nexample (σ : Store) : (BExpr.equals (.const 0) (.const 0)).eval σ = true := rfl'},

    {t:'p', h:'An interpreter that answered <code>none</code> for <code>forever</code> would be making a claim, and the claim would be indistinguishable from the one it makes about a bad <code>load</code>. Worse, it would be making the claim <i>eagerly</i>: to produce <code>none</code> for a program that runs forever, something has to decide, in finite time, that it runs forever. The fuel version does not decide it — it answers <code>none</code> when the counter runs out, which says nothing about the program at all.'},

    {t:'p', h:'Take the second objection seriously and the first one dissolves. Stop asking what a command <i>returns</i>. Ask instead which pairs of states it <i>connects</i>: which <code>s</code> and <code>s\'</code> are such that running <code>c</code> from <code>s</code> can finish in <code>s\'</code>. That is a three-place relation, not a function, and a relation is not computed, so there is nothing left for Lean to demand a termination proof of. A program that faults connects no states. A program that runs forever connects no states either. The relation says nothing about either, and saying nothing is an abstention; <code>none</code> was an assertion.'},

    {t:'cmp',
     left:{t:'The interpreter', h:'A <code>def</code> of type <code>Cmd → State → Option State</code>. You run it and get an answer. It must terminate, so a loop needs an invented counter; and <code>none</code> conflates two situations that a course about memory errors must keep apart.'},
     right:{t:'Chosen: the relation', kind:'good', h:'An <code>inductive</code> of type <code>Cmd → State → State → Prop</code>. You do not run it; you prove things about it. Nothing must terminate, because nothing computes. The price is that a fault and a divergence are both <i>absent</i> from it in the same way, and Unit 35 is where that price is paid.'}},

    /* ================================================================ rules === */

    {t:'sec', s:'Ten rules'},

    {t:'p', h:'Here is the relation. Its constructors are not ways of building a command — <code>Cmd</code> already has those. They are the ways a run can happen, and each one says: <i>under these premises, this run is legitimate</i>.'},

    {t:'code', cap:'The whole semantics of the language. Ten constructors, one per way of finishing a command — two for <code>ite</code> and two for <code>loop</code>, because those commands finish in two different ways depending on the guard.',
     src:'inductive Exec : Cmd → State → State → Prop where\n  | skip {s} : Exec .skip s s\n  | assign {s x e} :\n      Exec (.assign x e) s ⟨Store.set s.store x (e.eval s.store), s.heap⟩\n  | load {s x l v} (hl : s.heap l = some v) :\n      Exec (.load x l) s ⟨Store.set s.store x v, s.heap⟩\n  | write {s l e old} (hl : s.heap l = some old) :\n      Exec (.write l e) s ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩\n  | free {s l v} (hl : s.heap l = some v) :\n      Exec (.free l) s ⟨s.store, Heap.erase s.heap l⟩\n  | seq {s s\' s\'\' c₁ c₂} (h₁ : Exec c₁ s s\') (h₂ : Exec c₂ s\' s\'\') :\n      Exec (c₁ ;; c₂) s s\'\'\n  | iteTrue {s s\' b c₁ c₂} (hb : b.eval s.store = true) (h : Exec c₁ s s\') :\n      Exec (.ite b c₁ c₂) s s\'\n  | iteFalse {s s\' b c₁ c₂} (hb : b.eval s.store = false) (h : Exec c₂ s s\') :\n      Exec (.ite b c₁ c₂) s s\'\n  | loopFalse {s b c} (hb : b.eval s.store = false) :\n      Exec (.loop b c) s s\n  | loopTrue {s s\' s\'\' b c} (hb : b.eval s.store = true)\n      (hbody : Exec c s s\') (hrest : Exec (.loop b c) s\' s\'\') :\n      Exec (.loop b c) s s\'\''},

    {t:'anat', tag:'sketch', cap:'Three of the ten, pulled out on their own. The three between them use every device the other seven use.',
     src:'  | skip {s} : Exec .skip s s\n\n  | load {s x l v} (hl : s.heap l = some v) :\n      Exec (.load x l) s ⟨Store.set s.store x v, s.heap⟩\n\n  | loopTrue {s s\' s\'\' b c} (hb : b.eval s.store = true)\n      (hbody : Exec c s s\') (hrest : Exec (.loop b c) s\' s\'\') :\n      Exec (.loop b c) s s\'\'',
     parts:[
       {m:'{s}', h:'The braces make <code>s</code> implicit, so writing <code>Exec.skip</code> with no arguments is enough and Lean works out which state you meant from the statement you are proving. Every constructor here binds its states, commands and values this way, because each of them is recoverable — from the conclusion, or from the premises you supply — so nobody should have to type them.'},
       {m:'Exec .skip s s', h:'The same <code>s</code> twice. A constructor\'s conclusion is not a template with holes; it is a claim, and this one claims that the only runs of <code>skip</code> are the ones that change nothing. Everything the rule does is in the repetition of that letter.'},
       {m:'(hl : s.heap l = some v)', h:'A named, <b>explicit</b> argument whose type is a proposition — the rule\'s premise. To build a value of <code>Exec (.load x l) s …</code> you must supply a proof that address <code>l</code> holds something. There is no clause for the case where it does not, and that absence is the whole design.'},
       {m:'⟨Store.set s.store x v, s.heap⟩', h:'The state the rule concludes with is <i>computed</i> from the state it started with. Nothing quantifies over the final state of a <code>load</code>: it is determined by the rule, which is why the exercise below can invert this rule and read the answer off.'},
       {m:'(hbody : Exec c s s\')', h:'A premise which is itself a run. This is what makes a proof of <code>Exec</code> a tree rather than a list: the argument you supply here is another derivation, with its own premises underneath it.'},
       {m:'(hrest : Exec (.loop b c) s\' s\'\')', h:'The recursive premise is at the <b>same</b> command — the clause <code>runBad</code> choked on. It is legitimate here for a reason that has nothing to do with the command: the thing being built is a finite tree, and this subtree is strictly smaller than the tree it sits in whatever command labels it. A loop that never stops has no tree at all.'}
     ]},

    {t:'p', h:'The traditional way to write those clauses is with a horizontal line: premises above, conclusion below, and the name of the rule beside it. The Lean and the line are the same thing, and every paper on this subject uses the line, so the translation between them has to be automatic.'},

    {t:'txt', cap:'Five of the ten. The other five are read the same way: everything to the left of the final colon is above the line, and the type after the colon is below it.',
     src:'                                            hl : s.heap l = some v\n     ─────────────── skip             ────────────────────────────────────────── load\n      Exec .skip s s                   Exec (.load x l) s ⟨s.store.set x v, s.heap⟩\n\n\n       h₁ : Exec c₁ s s\'    h₂ : Exec c₂ s\' s\'\'\n     ──────────────────────────────────────────── seq\n              Exec (c₁ ;; c₂) s s\'\'\n\n\n       hb : b.eval s.store = true    h : Exec c₁ s s\'\n     ─────────────────────────────────────────────────── iteTrue\n              Exec (.ite b c₁ c₂) s s\'\n\n\n       hb : b.eval s.store = true\n       hbody : Exec c s s\'    hrest : Exec (.loop b c) s\' s\'\'\n     ─────────────────────────────────────────────────────────── loopTrue\n              Exec (.loop b c) s s\'\''},

    /* ------------------------------------------------- indices vs parameters --- */

    {t:'h3', s:'Indices, not parameters'},

    {t:'p', h:'Look at the header line again: <code>inductive Exec : Cmd → State → State → Prop</code>. The three arguments are written <i>after</i> the colon, and that is not a stylistic choice. An argument written before the colon, as <code>(M : Type)</code> is in <code>structure PCM (M : Type)</code>, is a <b>parameter</b>: it is fixed once for the whole declaration, and every constructor must conclude with that same letter in that position. An argument written after the colon is an <b>index</b>: each constructor may conclude with whatever it likes there.'},

    {t:'p', h:'That difference decides whether the declaration is even possible. <code>Exec.skip</code> concludes at the command <code>.skip</code>, <code>Exec.seq</code> concludes at <code>c₁ ;; c₂</code>, and the two are not the same command. Make the command a parameter and the declaration cannot be written at all.'},

    {t:'code', tag:'sketch', cap:'The command moved to the left of the colon, and a single constructor attempted.',
     src:'inductive ExecP (c : Cmd) : State → State → Prop where\n  | skip {s} : ExecP .skip s s'},

    {t:'state', cap:'Lean\'s answer, and its last line is the whole distinction in one sentence.',
     src:'error(lean.inductiveParamMismatch): Mismatched inductive type parameter in\n  ExecP Cmd.skip s s\nThe provided argument\n  Cmd.skip\nis not definitionally equal to the expected parameter\n  c\n\nNote: The value of parameter `c` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.'},

    {t:'p', h:'The same freedom is what makes the relation usable later. Because the command position is an index, a hypothesis <code>h : Exec .skip s s\'</code> carries the information that its command is <code>.skip</code>, and Lean can compare that against the index each constructor concludes with. Nine of the ten do not match, and they are discarded without your saying anything. Under a parameter there would be nothing to compare: the parameter is whatever you supplied, uniformly, and it distinguishes nothing. That comparison is the mechanism of the rest of this page.'},

    /* ============================================================ derivations === */

    {t:'sec', s:'A derivation is a term'},

    {t:'p', h:'<code>Exec c s s\'</code> is a proposition, so by Unit 01 a proof of it is a term of that type, and the only ways to build one are the ten constructors. A term built out of constructors, whose arguments include other such terms, is a finite tree. That tree is called a <b>derivation</b>, and writing one down is how you assert that a particular program does a particular thing.'},

    {t:'code', tag:'illustration', cap:'A two-command program: read address 3 into variable 0, then hand address 3 back. The heap holds <code>7</code> at address 3 and nothing anywhere else.',
     src:'example (σ : Store) :\n    Exec (.load 0 3 ;; .free 3) ⟨σ, Heap.singleton 3 7⟩\n      ⟨Store.set σ 0 7, Heap.erase (Heap.singleton 3 7) 3⟩ :=\n  Exec.seq (Exec.load (singleton_same 3 7)) (Exec.free (singleton_same 3 7))'},

    {t:'p', h:'One line of proof, and every piece of it is doing work. <code>Exec.seq</code> is the root. Its two arguments are the derivations of the two halves, and each of <i>those</i> is a constructor applied to its premise — here the same theorem twice, <code>singleton_same 3 7</code>, which is the Unit 05 lemma saying that a one-cell heap answers at its own address. Draw it and the shape is the shape of the rules.'},

    {t:'svg', cap:'The derivation, with the states named. <code>s₁</code> is the state between the two commands. It appears nowhere in the statement being proved — the statement mentions only <code>s₀</code> and <code>s₂</code> — and the term is what fixes it.',
     src:'\n<svg viewBox="0 0 640 250" role="img" aria-label="A derivation tree for a two-command program">\n  <g class="dg">\n    <text x="46" y="26" class="dg-note">singleton_same 3 7</text>\n    <text x="366" y="26" class="dg-note">singleton_same 3 7</text>\n    <line x1="30" y1="36" x2="250" y2="36" stroke="currentColor" stroke-width="1.2" opacity=".55"/>\n    <line x1="350" y1="36" x2="560" y2="36" stroke="currentColor" stroke-width="1.2" opacity=".55"/>\n    <text x="258" y="40" class="dg-note">load</text>\n    <text x="568" y="40" class="dg-note">free</text>\n    <text x="30" y="58" class="dg-t">Exec (.load 0 3) s₀ s₁</text>\n    <text x="350" y="58" class="dg-t">Exec (.free 3) s₁ s₂</text>\n    <line x1="30" y1="76" x2="560" y2="76" stroke="currentColor" stroke-width="1.2" opacity=".55"/>\n    <text x="568" y="80" class="dg-note">seq</text>\n    <text x="30" y="98" class="dg-t">Exec (.load 0 3 ;; .free 3) s₀ s₂</text>\n\n    <text x="30" y="146" class="dg-lab">the three states</text>\n    <text x="30" y="172" class="dg-t">s₀  =  ⟨σ, Heap.singleton 3 7⟩</text>\n    <text x="30" y="198" class="dg-t">s₁  =  ⟨Store.set σ 0 7, Heap.singleton 3 7⟩</text>\n    <text x="30" y="224" class="dg-t">s₂  =  ⟨Store.set σ 0 7, Heap.erase (Heap.singleton 3 7) 3⟩</text>\n  </g>\n</svg>'},

    {t:'p', h:'The middle state is the point to dwell on. <code>Exec.seq</code>\'s binder list is <code>{s s\' s\'\' c₁ c₂}</code>, and <code>s\'</code> occurs in both premises and in neither the hypothesis you started from nor the conclusion you reached. Lean recovers it by unifying the two premises you supplied. When you go the other way — taking a <code>seq</code> derivation apart instead of building one — that same <code>s\'</code> comes back with no name, and the last exercise on this page is where you meet it.'},

    /* --------------------------------------------------------- a loop\'s tree --- */

    {t:'p', h:'That tree is two storeys because the program is two commands long. A loop\'s tree is shaped by how many times the loop goes round, and that shape is the one worth seeing, because <code>loopTrue</code>\'s recursive premise sits at the same command — the clause <code>runBad</code> choked on. Take a countdown: while variable <code>0</code> is not zero, subtract one from it. Started from a store holding <code>2</code>, it goes round twice.'},

    {t:'code', tag:'illustration', cap:'Each <code>rfl</code> proves a guard premise by computing the guard at the store of the moment: true at <code>2</code>, true at <code>1</code>, false at <code>0</code>. The final store is two nested <code>Store.set</code>s because the <code>assign</code> rule adds one layer per turn and nothing collapses them. The heap <code>h</code> is arbitrary and no rule in the term touches it.',
     src:'example (h : Heap) :\n    Exec (.loop (.not (.equals (.var 0) (.const 0)))\n           (.assign 0 (.minus (.var 0) (.const 1))))\n      ⟨fun _ => 2, h⟩ ⟨Store.set (Store.set (fun _ => 2) 0 1) 0 0, h⟩ :=\n  Exec.loopTrue rfl Exec.assign\n    (Exec.loopTrue rfl Exec.assign\n      (Exec.loopFalse rfl))'},

    {t:'svg', cap:'The tower, with the guard, the body and the three states abbreviated below it. Each <code>loopTrue</code> has three premises — the guard holds, the body runs, and the whole loop runs again — and the third of them is the subtree above and to its right. The top storey is a <code>loopFalse</code>, whose only premise is an equation, and that is where the tree stops.',
     src:'\n<svg viewBox="0 0 660 330" role="img" aria-label="A derivation tree for a loop that goes round twice">\n  <g class="dg">\n    <text x="396" y="26" class="dg-note">hb₂ : b.eval s₂.store = false</text>\n    <line x1="392" y1="36" x2="576" y2="36" stroke="currentColor" stroke-width="1.2" opacity=".55"/>\n    <text x="582" y="40" class="dg-note">loopFalse</text>\n    <text x="392" y="60" class="dg-t">Exec (.loop b c) s₂ s₂</text>\n\n    <text x="206" y="42" class="dg-note">hb₁ : b.eval s₁.store = true</text>\n    <text x="206" y="60" class="dg-t">Exec c s₁ s₂</text>\n    <line x1="202" y1="78" x2="576" y2="78" stroke="currentColor" stroke-width="1.2" opacity=".55"/>\n    <text x="582" y="82" class="dg-note">loopTrue</text>\n    <text x="202" y="104" class="dg-t">Exec (.loop b c) s₁ s₂</text>\n\n    <text x="16" y="86" class="dg-note">hb₀ : b.eval s₀.store = true</text>\n    <text x="16" y="104" class="dg-t">Exec c s₀ s₁</text>\n    <line x1="12" y1="122" x2="576" y2="122" stroke="currentColor" stroke-width="1.2" opacity=".55"/>\n    <text x="582" y="126" class="dg-note">loopTrue</text>\n    <text x="12" y="148" class="dg-t">Exec (.loop b c) s₀ s₂</text>\n\n    <text x="12" y="196" class="dg-lab">the guard, the body, and the three states</text>\n    <text x="12" y="222" class="dg-t">b   =  .not (.equals (.var 0) (.const 0))</text>\n    <text x="12" y="248" class="dg-t">c   =  .assign 0 (.minus (.var 0) (.const 1))</text>\n    <text x="12" y="274" class="dg-t">s₀  =  ⟨fun _ => 2, h⟩</text>\n    <text x="12" y="300" class="dg-t">s₁  =  ⟨Store.set (fun _ => 2) 0 1, h⟩</text>\n    <text x="12" y="326" class="dg-t">s₂  =  ⟨Store.set (Store.set (fun _ => 2) 0 1) 0 0, h⟩</text>\n  </g>\n</svg>'},

    {t:'p', h:'One storey per turn, and the command labelling the recursive premise never got smaller. It did not have to. <code>runBad</code> needed an argument that shrinks at every call because it was computing an answer one step at a time and had to be sure the steps ran out. A derivation computes nothing: it is a term, and the only demand on a term is that it be finite. This one is finite because the guard eventually reads <code>false</code> and <code>loopFalse</code> closes it off. <code>forever</code>\'s guard never does, so nothing can sit at the top of its tower — there is no term, and therefore no derivation.'},

    /* ------------------------------------------------------------- leastness --- */

    {t:'h3', s:'Why "the least relation" is part of the definition'},

    {t:'p', h:'The ten rules say what is <i>in</i> the relation. On their own they do not say what is out of it, and that is not a quibble: plenty of relations satisfy all ten.'},

    {t:'code', tag:'illustration', cap:'The relation that holds of everything satisfies every one of the ten rules, vacuously, because its conclusion is true no matter what its premises say.',
     src:'def Anything : Cmd → State → State → Prop := fun _ _ _ => True\n\nexample : ∀ c s s\', Exec c s s\' → Anything c s s\' := fun _ _ _ _ => trivial'},

    {t:'p', h:'So "closed under the ten rules" does not pin down a relation, and an <code>inductive</code> declaration means something stronger. It means <b>the least</b> relation closed under the rules: <code>Exec c s s\'</code> holds exactly when some finite tree of the ten constructors concludes with it, and for nothing else. That single word carries two consequences, and they run in opposite directions.'},

    {t:'ul', items:[
      'Downwards, it says <code>Exec</code> is contained in every relation closed under the rules — the statement the example above is one instance of. Cashing it in general means arguing about <i>every</i> derivation at once, which is a technique this page does not have.',
      'Upwards, it says nothing is in <code>Exec</code> except by a rule. If no constructor can conclude with the statement in front of you, there is no proof of it. This is the half available today, and the whole of the next section is spending it.'
    ]},

    /* ================================================================ stuck === */

    {t:'sec', s:'Stuck, diverging, and what is not in the relation'},

    {t:'p', h:'Two quite different programs are invisible to <code>Exec</code>, and they are invisible in the same way.'},

    {t:'ul', items:[
      '<b>Stuck.</b> <code>load 0 3</code> in a state whose heap is empty. Every rule that concludes at a <code>load</code> demands a premise <code>s.heap l = some v</code>, and there is no such <code>v</code>. Execution has reached a command it cannot take a step of. This is the memory error, and it is the reason the language exists.',
      '<b>Diverging.</b> <code>forever</code>, in any state at all. Its tower has no top storey, for the reason drawn above. Nothing is wrong with any individual step, and no step is missing a premise; there is no finite tree.'
    ]},

    {t:'p', h:'In both cases the same sentence is true — there is no <code>s\'</code> with <code>Exec c s s\'</code> — and <code>Exec</code> offers no way to say which of the two is happening. That is a genuine loss, it is deliberate, and it is not paid for until Unit 35, where partial and total correctness finally come apart and the difference between "did not finish" and "went wrong" is what separates them. Everything between here and there treats the two alike, because everything between here and there is about programs that are supposed to do both: finish, and not fault.'},

    {t:'note', kind:'key', title:'Existence of a derivation is what "safe" is going to mean',
     h:'A specification in Unit 22 will say: from every state satisfying the precondition, <b>there exists</b> a final state which the command reaches and which satisfies the postcondition. Read that against the two bullets above. A program that faults has no final state, so it fails the existential. A program that diverges has no final state either, so it fails the same existential. One quantifier excludes both, and it does so without the semantics containing any notion of error whatsoever. That is why there is no <code>error</code> constructor in <code>Exec</code>, and why the exercise below — a program with no final state — is a theorem about safety and not a curiosity.'},

    {t:'detail', title:'What an error value would have cost', open:false, blocks:[
      {t:'p', h:'The alternative is a relation whose third position is an <code>Option State</code>, with <code>none</code> meaning "faulted". It can be written, and it does buy something real: it separates faulting from diverging, which <code>Exec</code> cannot. Here is the price, on the two commands where it is smallest.'},
      {t:'code', tag:'illustration',
       src:'inductive ExecF : Cmd → State → Option State → Prop where\n  | load {s x l v} (hl : s.heap l = some v) :\n      ExecF (.load x l) s (some ⟨Store.set s.store x v, s.heap⟩)\n  | loadFault {s x l} (hl : s.heap l = none) :\n      ExecF (.load x l) s none\n  | seq {s s\' r c₁ c₂} (h₁ : ExecF c₁ s (some s\')) (h₂ : ExecF c₂ s\' r) :\n      ExecF (c₁ ;; c₂) s r\n  | seqFault {s c₁ c₂} (h₁ : ExecF c₁ s none) :\n      ExecF (c₁ ;; c₂) s none'},
      {t:'p', h:'Two rules where <code>Exec</code> has one, in both cases, and the pattern continues: every command that can fault needs a fault rule, and every command with a subcommand needs a rule propagating a subcommand\'s fault. Written out for all eight commands it takes fifteen constructors where <code>Exec</code> takes ten. Worse is what happens downstream — every theorem about the relation acquires a <code>none</code> case, and every inversion below would leave two goals instead of one. The gain is a distinction the course does not need until Unit 35 and can make there, on the four lines of a definition, rather than paying for it in every proof from here on.'}
    ]},

    /* ============================================================= inversion === */

    {t:'sec', s:'Taking a derivation apart'},

    {t:'p', h:'Building a derivation is the easy direction. The useful direction is the other one: someone hands you <code>h : Exec c s s\'</code> for a particular <code>c</code>, and you want to know what it must have been. Since the only way to have made it is a constructor, and since the command sits in an index that Lean can compare, the question has an answer — and the tactic that asks it is <code>cases</code>, which Unit 02 used to split a value of an inductive type. Pointed at a proof of an inductive proposition it does the same thing, and the name for it is <b>inversion</b>.'},

    {t:'p', h:'Start where there is nothing to get wrong: the one command with a single rule.'},

    {t:'ex',
     id:'m5-1',
     name:'exec_skip_inv',
     hard:false,
     why:'Your first inversion, and the smallest possible statement of what inversion buys: a hypothesis that looked opaque turns out to determine a variable. Unit 35\'s rule for <code>skip</code> is this proof and nothing else — the same two tactics, in the same order — and the locality proofs from Unit 24 on all open with a move of this shape.',
     setup:'<code>Exec</code> is in scope with all ten constructors. Two tactics are enough, and both are ones you have used before — the second one closes a goal that will already be true when you get there.',
     goal:'theorem exec_skip_inv {s s\' : State} (h : Exec .skip s s\') : s\' = s := by',
     hints:[
       'The goal says that the state you finish in equals the state you started in. You are told nothing about either state; all you have is <code>h</code>, a proof that running <code>skip</code> from <code>s</code> reaches <code>s\'</code>.',
       'There is exactly one rule whose conclusion is about <code>skip</code>, and its conclusion has the <i>same</i> state in both places. So <code>h</code> could only have been built one way, and that way forces <code>s\'</code> and <code>s</code> to be the same state. The argument is: enumerate how <code>h</code> was made; there is one case; in that case the goal is an identity.',
       'The tactic that enumerates how an inductive value was made is <code>cases</code>, applied to the hypothesis. Then look at what is left.',
       'The first line is <code>cases h</code>. It leaves one goal, tagged <code>case skip</code>, in which <code>s\'</code> has disappeared from the context entirely and the goal reads <code>s = s</code>.'
     ],
     sol:'theorem exec_skip_inv {s s\' : State} (h : Exec .skip s s\') : s\' = s := by\n  cases h; rfl',
     solNote:'The semicolon runs the second tactic on what the first left, and is the same one-line device you used in Unit 01. If you climbed all four hints and are still stuck, open this without a second thought — the shape it teaches is worth more than the struggle, and it recurs in most of the proofs left in the course.',
     expl:'<code>cases h</code> asks: which constructor produced <code>h</code>? Lean walks the ten and tries to unify each one\'s conclusion with <code>Exec .skip s s\'</code>. Nine fail on the command index — <code>Cmd.skip</code> is not <code>Cmd.assign x e</code>, and constructors of an inductive type are distinct. The tenth, <code>Exec.skip</code>, unifies, but only by also identifying <code>s\'</code> with <code>s</code>, because that constructor concludes with the same state twice. So the surviving case is not "the <code>skip</code> case with <code>s\'</code> still around": it is the <code>skip</code> case with <code>s\'</code> replaced everywhere by <code>s</code>, which is why the goal that remains is closed by <code>rfl</code>.',
     walk:[
       {tac:'cases h', h:'Ten candidate constructors, nine eliminated by the command index, one surviving. The survivor\'s conclusion forces <code>s\' = s</code>, so Lean substitutes and <code>s\'</code> leaves the context. What is left is tagged <code>case skip</code> and reads <code>s = s</code>.'},
       {tac:'rfl', h:'Both sides are the same term, so the goal closes definitionally. It is not that the equation was proved; it is that after the substitution there was no equation left to prove.'}
     ],
     deep:[
       {t:'trace', title:'exec_skip_inv, two tactics',
        start:'s s\' : State\nh : Exec Cmd.skip s s\'\n⊢ s\' = s',
        steps:[
          {tac:'cases h', state:'case skip\ns : State\n⊢ s = s',
           h:'Three things changed at once: <code>h</code> is gone (it has been consumed), <code>s\'</code> is gone (it has been identified with <code>s</code>), and a case tag appeared naming the constructor that survived. The tag is Lean telling you which rule you are in; with one surviving case it is not yet load-bearing, and with ten it will be.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The elimination of <code>s\'</code> is the part to keep. Inversion does not only give you a case analysis: in each case it also applies whatever equations that constructor\'s conclusion forces. Here it forced one and that one closed the proof.'}
     ],
     pitfall:'Reaching for <code>rfl</code> first. The goal <code>s\' = s</code> looks as if it ought to be an identity, and it is not one until <code>cases</code> has run: before that <code>s</code> and <code>s\'</code> are two unrelated variables, and the only thing tying them together is <code>h</code>, which <code>rfl</code> never looks at. Lean says so in those terms — <code>Tactic `rfl` failed: The left-hand side</code> <code>s\'</code> <code>is not definitionally equal to the right-hand side</code> <code>s</code> — and then reprints the context with <code>h</code> still in it, unconsumed. An unconsumed hypothesis under a failed <code>rfl</code> is the standing signal that the missing move is an inversion.',
     variants:'Reversing the conclusion to <code>s = s\'</code> changes nothing: after <code>cases h</code> the goal is <code>s = s</code> either way. Dropping the hypothesis <code>h</code> makes the statement false, and there is no proof to invert. Replacing <code>.skip</code> by a variable command <code>c</code> makes it false too, and instructively: <code>cases h</code> then leaves ten goals, because with a variable in the index position nothing can be eliminated. Exactly two of them close — <code>case skip</code> and <code>case loopFalse</code>, the two rules whose conclusion carries the same state twice. The first that does not is <code>case assign</code>, and it is where the statement dies: it reads <code>⊢ { store := s.store.set x✝ (Atom.eval s.store e✝), heap := s.heap } = s</code>, which is the claim that assignment changes nothing.'},

    {t:'p', h:'The nine discarded cases should be seen once, because they are what a general inversion looks like and because the next unit is going to leave you with all ten. Run <code>cases h</code> on a hypothesis whose command is a plain variable and every constructor survives.'},

    {t:'code', tag:'illustration', cap:'A goal that every case closes, so the interesting part is the ten goals rather than the proof.',
     src:'example (c : Cmd) (s s\' : State) (h : Exec c s s\') : c = c := by\n  cases h <;> rfl'},

    {t:'detail', title:'The ten goals, in full', open:false, blocks:[
      {t:'p', h:'Obtained by dropping the <code>&lt;;&gt; rfl</code> from the example above and putting <code>trace_state</code> on the line after the <code>cases</code>. Read down the case tags: there is exactly one per constructor, in declaration order, and in each one the command index has been replaced by that constructor\'s own shape.'},
      {t:'state', src:'case skip\ns : State\n⊢ Cmd.skip = Cmd.skip\n\ncase assign\ns : State\nx✝ : Var\ne✝ : Atom\n⊢ Cmd.assign x✝ e✝ = Cmd.assign x✝ e✝\n\ncase load\ns : State\nx✝ : Var\nl✝ : Loc\nv✝ : Val\nhl✝ : s.heap l✝ = some v✝\n⊢ Cmd.load x✝ l✝ = Cmd.load x✝ l✝\n\ncase write\ns : State\nl✝ : Loc\ne✝ : Atom\nold✝ : Val\nhl✝ : s.heap l✝ = some old✝\n⊢ Cmd.write l✝ e✝ = Cmd.write l✝ e✝\n\ncase free\ns : State\nl✝ : Loc\nv✝ : Val\nhl✝ : s.heap l✝ = some v✝\n⊢ Cmd.free l✝ = Cmd.free l✝\n\ncase seq\ns s\' s\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\n⊢ c₁✝ ;; c₂✝ = c₁✝ ;; c₂✝\n\ncase iteTrue\ns s\' : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb✝ : BExpr.eval s.store b✝ = true\nh✝ : Exec c₁✝ s s\'\n⊢ Cmd.ite b✝ c₁✝ c₂✝ = Cmd.ite b✝ c₁✝ c₂✝\n\ncase iteFalse\ns s\' : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb✝ : BExpr.eval s.store b✝ = false\nh✝ : Exec c₂✝ s s\'\n⊢ Cmd.ite b✝ c₁✝ c₂✝ = Cmd.ite b✝ c₁✝ c₂✝\n\ncase loopFalse\ns : State\nb✝ : BExpr\nc✝ : Cmd\nhb✝ : BExpr.eval s.store b✝ = false\n⊢ Cmd.loop b✝ c✝ = Cmd.loop b✝ c✝\n\ncase loopTrue\ns s\' s\'✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb✝ : BExpr.eval s.store b✝ = true\nhbody✝ : Exec c✝ s s\'✝\nhrest✝ : Exec (Cmd.loop b✝ c✝) s\'✝ s\'\n⊢ Cmd.loop b✝ c✝ = Cmd.loop b✝ c✝'},
      {t:'p', h:'Every extra name a constructor introduced arrives daggered, because nothing in the tactic call said what to call it; the undaggered <code>s</code> and <code>s\'</code> are the example\'s own variables, which unification identified with the constructor\'s. Two of the cases have three states in scope where the statement mentions two — <code>seq</code> and <code>loopTrue</code>, whose extra <code>s\'✝</code> is the intermediate state. That dagger is the subject of the last exercise.'}
    ]},

    /* ----------------------------------------------------------- naming them --- */

    {t:'h4', s:'Naming what a case hands you'},

    {t:'p', h:'When only one case survives, and that case has premises you need, you want them under names of your choosing. The syntax is <code>cases h with | ctor a b => …</code>: one branch per surviving case, and after the constructor name, one identifier per <b>explicit</b> argument of that constructor, in order.'},

    {t:'p', h:'Explicit is the operative word, and the error you get for miscounting says which arguments are being counted. Take <code>Exec.write</code>, whose rule is the one place where the premise binds something the conclusion never uses: it binds four things in braces — <code>{s l e old}</code> — and takes one argument in parentheses, the premise <code>hl</code>. So it gets exactly one name.'},

    {t:'code', tag:'sketch', cap:'Two names offered to a constructor with one explicit argument.',
     src:'theorem write_inv_bad {l : Loc} {e : Atom} {s s\' : State} (h : Exec (.write l e) s s\') :\n    s\' = ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩ := by\n  cases h with\n  | write old hl => rfl'},

    {t:'state', cap:'The message counts explicit arguments and says so. <code>old</code> is not refused because it is a bad name; it is refused because that slot does not exist.',
     src:'error: Too many variable names provided at alternative `write`: 2 provided, but 1 expected'},

    {t:'code', tag:'illustration', cap:'One name, and the inversion goes through — the <code>write</code> rule computes its final state, so what is left is an identity.',
     src:'example {l : Loc} {e : Atom} {s s\' : State} (h : Exec (.write l e) s s\') :\n    s\' = ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩ := by\n  cases h with\n  | write hl =>\n    rfl'},

    {t:'state', cap:'The state before the <code>rfl</code>. Four things the constructor bound are in the context and only one of them has the name you gave.',
     src:'case write\nl : Loc\ne : Atom\ns : State\nold✝ : Val\nhl : s.heap l = some old✝\n⊢ { store := s.store, heap := s.heap.write l (Atom.eval s.store e) } =\n    { store := s.store, heap := s.heap.write l (Atom.eval s.store e) }'},

    {t:'p', h:'<code>old✝</code> is the value that was at the address before the write. The rule needed it, in order to state that the address was allocated at all, and the conclusion then discards it — so it is in the context and it is unusable, because <code>✝</code> is output and not an input character. The tactic that repairs this is <code>rename_i</code>: it takes names for the trailing inaccessible entries in the context, rightmost last, and rebinds them. Nothing on this page is going to need it — the two remaining exercises get past their daggers by other means — but Unit 26 has a proof that cannot be written without it, and meeting the tactic where it is optional is cheaper than meeting it where it is not.'},

    {t:'code', tag:'illustration', cap:'The same proof with one line inserted. Nothing about the proof needs it here, which is why it is the right place to watch it work.',
     src:'example {l : Loc} {e : Atom} {s s\' : State} (h : Exec (.write l e) s s\') :\n    s\' = ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩ := by\n  cases h with\n  | write hl =>\n    rename_i old\n    rfl'},

    {t:'state', cap:'After <code>rename_i old</code>. One line of the context changed, and <code>hl</code>\'s type followed it.',
     src:'case write\nl : Loc\ne : Atom\ns : State\nold : Val\nhl : s.heap l = some old\n⊢ { store := s.store, heap := s.heap.write l (Atom.eval s.store e) } =\n    { store := s.store, heap := s.heap.write l (Atom.eval s.store e) }'},

    {t:'p', h:'Now the two inversions the rest of the course is built out of. They differ in what the surviving case has to yield: <code>assign</code> determines the final state outright, so its inversion looks like the <code>write</code> proof above; <code>load</code> determines it only in terms of a value that appears nowhere in the statement, so its inversion has to hand that value back along with the rule\'s premise. The second is the shape you will keep meeting.'},

    {t:'ex',
     id:'x42',
     name:'exec_assign_inv / exec_load_inv',
     hard:false,
     why:'This is the shape of every proof in Module 6. A hypothesis says a command ran; you invert it; and what falls out is either the final state itself, or a premise of the rule — the fact that the address was allocated — which is exactly the fact the precondition of a separation-logic rule will have been holding in reserve. The second theorem is also where you find out that a rule\'s implicit arguments do not disappear when you invert it; they come back with no names.',
     setup:'Two theorems. The first has a one-line proof of the same shape as <code>exec_skip_inv</code>. The second needs the named-branch form of <code>cases</code>, because it has to use the rule\'s premise. The first statement arrives with a <code>sorry</code> under it, so you can attack either one first; the editor checks the whole box at once.',
     goal:'theorem exec_assign_inv {x : Var} {e : Atom} {s s\' : State} (h : Exec (.assign x e) s s\') :\n    s\' = ⟨Store.set s.store x (e.eval s.store), s.heap⟩ :=\n  sorry\n\ntheorem exec_load_inv {x : Var} {l : Loc} {s s\' : State} (h : Exec (.load x l) s s\') :\n    ∃ v, s.heap l = some v ∧ s\' = ⟨Store.set s.store x v, s.heap⟩ := by',
     hints:[
       'The first goal says the final state is the one the <code>assign</code> rule computes: the same heap, and the store with <code>x</code> set to the value of <code>e</code> read in the <i>old</i> store. The second says that if a <code>load</code> ran, then some value was sitting at address <code>l</code>, and the final state is the one the rule computes from it.',
       'Both are the argument you used for <code>skip</code>. Only one rule can have produced each hypothesis; enumerate and see what it forces. For the first, the rule forces the final state completely, so the goal becomes an identity. For the second the rule forces the final state only in terms of the value it found, so you must hand that value over as the witness of the existential — together with the rule\'s own premise, which is the proof that it was there.',
       'The tactic is <code>cases</code> both times. For the first, bare <code>cases</code>, and then <code>rfl</code> on what it leaves. For the second you need the rule\'s premise under a name of your own choosing, so it has to be the branch form — the one that takes a constructor name and then one identifier per <b>explicit</b> argument, of which <code>Exec.load</code> has exactly one. The three-part answer is an anonymous constructor <code>⟨…⟩</code>, and an underscore is allowed in any slot Lean can work out for itself.',
       'The second proof\'s first line is <code>cases h with</code>, its second is <code>| load hl =></code>, and what that leaves is a goal whose existential is over a variable Lean is calling <code>v✝</code>. You do not have to name it: the body <code>exact ⟨_, hl, rfl⟩</code> supplies the witness as an underscore, and the type of <code>hl</code> tells Lean what it must be.'
     ],
     sol:'theorem exec_assign_inv {x : Var} {e : Atom} {s s\' : State} (h : Exec (.assign x e) s s\') :\n    s\' = ⟨Store.set s.store x (e.eval s.store), s.heap⟩ := by\n  cases h; rfl\n\ntheorem exec_load_inv {x : Var} {l : Loc} {s s\' : State} (h : Exec (.load x l) s s\') :\n    ∃ v, s.heap l = some v ∧ s\' = ⟨Store.set s.store x v, s.heap⟩ := by\n  cases h with\n  | load hl => exact ⟨_, hl, rfl⟩',
     solNote:'The underscore is not laziness. The witness is <code>v✝</code>, a name you are not allowed to type; the underscore is the only way to refer to it without first running <code>rename_i</code>.',
     expl:'Both proofs are one inversion. The difference is what the surviving case leaves. <code>Exec.assign</code> has no premises and its conclusion computes the final state from the initial one, so unification rewrites the goal into an identity and <code>rfl</code> finishes. <code>Exec.load</code> has a premise, and the value it mentions is bound implicitly by the rule, so the surviving case carries both a fresh value and a proof about it. The goal asks for a value and a proof about it. They match, and <code>⟨_, hl, rfl⟩</code> is the match written down: witness, premise, and the identity that the final state is what the rule said.',
     walk:[
       {tac:'cases h    (first theorem)', h:'Nine constructors are eliminated on the command index. <code>Exec.assign</code> survives and its conclusion forces <code>s\'</code> to be the record on the right-hand side of the goal, so <code>s\'</code> leaves the context and both sides of the equation become the same term.'},
       {tac:'rfl', h:'Closes the identity that <code>cases</code> left. Nothing about assignment is proved here; the rule already said what assignment does, and inversion is what turns "the rule says" into "the goal is".'},
       {tac:'cases h with    (second theorem)', h:'The same elimination on the command index, and the same substitution of the final state — <code>s\'</code> leaves the context and the goal\'s right-hand equation is now between two records. What is different is that the value the rule found does not leave: it stays, as a new variable, and the goal is an existential over exactly the kind of thing it is. Entering the case by name is what makes the premise about it reachable.'},
       {tac:'| load hl =>', h:'Names the one explicit argument of <code>Exec.load</code>: the premise <code>hl : s.heap l = some v✝</code>. The four implicit ones are bound too, unnamed, and <code>v✝</code> is the one that matters — it is the value the rule found, and it now occurs in the goal in place of <code>s\'</code>.'},
       {tac:'exact ⟨_, hl, rfl⟩', h:'Three slots flattened out of a nested pair, as in Unit 01. The underscore is the existential witness, left to Lean, which reads it off <code>hl</code>\'s type. <code>hl</code> is the first conjunct. <code>rfl</code> is the second, and it works because after the inversion the final state is literally the record the goal names.'}
     ],
     deep:[
       {t:'trace', title:'exec_assign_inv',
        start:'x : Var\ne : Atom\ns s\' : State\nh : Exec (Cmd.assign x e) s s\'\n⊢ s\' = { store := s.store.set x (Atom.eval s.store e), heap := s.heap }',
        steps:[
          {tac:'cases h', state:'case assign\nx : Var\ne : Atom\ns : State\n⊢ { store := s.store.set x (Atom.eval s.store e), heap := s.heap } =\n    { store := s.store.set x (Atom.eval s.store e), heap := s.heap }',
           h:'The left-hand side used to be <code>s\'</code>. Two spellings to keep straight: you wrote <code>Store.set s.store x …</code> and Lean prints <code>s.store.set x …</code>, and you wrote <code>e.eval s.store</code> and Lean prints <code>Atom.eval s.store e</code>. Unit 18 fixed the rule that decides both.'}
        ],
        done:'No goals.'},
       {t:'trace', title:'exec_load_inv',
        start:'x : Var\nl : Loc\ns s\' : State\nh : Exec (Cmd.load x l) s s\'\n⊢ ∃ v, s.heap l = some v ∧ s\' = { store := s.store.set x v, heap := s.heap }',
        steps:[
          {tac:'cases h with | load hl =>', state:'case load\nx : Var\nl : Loc\ns : State\nv✝ : Val\nhl : s.heap l = some v✝\n⊢ ∃ v, s.heap l = some v ∧ { store := s.store.set x v✝, heap := s.heap } = { store := s.store.set x v, heap := s.heap }',
           h:'Two new things in the context, one named and one not. The goal has lost <code>s\'</code> and gained <code>v✝</code> in its place — and its own bound <code>v</code> is still called <code>v</code>, so the two are distinguishable on the page only by the dagger.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Look at the goal in that second state and the choice of witness stops being a guess: put <code>v✝</code> for <code>v</code> and the first conjunct is <code>hl</code> and the second is an identity. The underscore asks Lean to make that substitution by unification instead of by your typing a name you do not have.'}
     ],
     pitfall:'Writing <code>exact ⟨v, hl, rfl⟩</code>, on the reasonable assumption that the value the rule bound is called <code>v</code> because the declaration calls it <code>v</code>. It is called <code>v✝</code>, and Lean answers <code>Unknown identifier `v`</code>. The fixes are the underscore, or <code>rename_i v</code> before the <code>exact</code>. The same error one step earlier catches anyone who writes bare <code>cases h</code> for the second theorem and then reaches for <code>hl</code>: without the branch, the premise is inaccessible too, and the report is <code>Unknown identifier `hl`</code> — pointing at the <code>exact</code>, though the line that needed changing was the <code>cases</code>.',
     variants:'Turn the existential in <code>exec_load_inv</code> into a universal — <code>∀ v, s.heap l = some v ∧ …</code> — and the statement becomes false, since it would claim every value is at <code>l</code>: on the one-cell heap <code>Heap.singleton 3 7</code> it would give <code>Heap.singleton 3 7 3 = some 0</code>. The proof fails at exactly the point that difference lives: the rule found one particular value, so <code>hl</code> has type <code>s.heap l = some v✝</code>, and it is offered where <code>s.heap l = some v</code> is wanted for the <code>v</code> the goal now quantifies over. Lean reports <code>Application type mismatch</code> on <code>And.intro hl</code>. Drop the hypothesis <code>h</code> from <code>exec_assign_inv</code> and it is false because <code>s\'</code> is then an arbitrary state with nothing said about it; drop it from <code>exec_load_inv</code> and it is false because nothing forces the heap to hold anything at <code>l</code> — which is the next exercise, where an empty heap is exactly the witness.'},

    /* --------------------------------------------------------------- stuck --- */

    {t:'p', h:'Now the theorem the design was for. A <code>load</code> from an empty heap is the memory error of Unit 00, and what has to be shown is not that it produces an error value — there is no error value — but that it produces <i>nothing</i>: no final state whatsoever, for any <code>s\'</code> you care to name.'},

    {t:'ex',
     id:'x43',
     name:'exec_load_stuck',
     hard:false,
     why:'A fault is the absence of a derivation, and this is where you prove that rather than being told it. It is also the first negative statement about <code>Exec</code>, and negative statements are where the "least relation" reading earns its keep — the proof works only because nothing is in the relation except by a rule.',
     setup:'The heap is <code>Heap.empty</code>, which Unit 05 defined as <code>fun _ => none</code>. The goal is a negation, so it is a function into <code>False</code>, and the first move is the one Unit 00 made: assume the thing and derive a contradiction.',
     goal:'theorem exec_load_stuck (x : Var) (l : Loc) (σ : Store) (s\' : State) :\n    ¬ Exec (.load x l) ⟨σ, Heap.empty⟩ s\' := by',
     hints:[
       'The goal is <code>¬ Exec (.load x l) ⟨σ, Heap.empty⟩ s\'</code>, which unfolds to a function from a proof that the load ran to a proof of <code>False</code>. Nothing is assumed about <code>s\'</code>: the claim is that <i>no</i> final state works.',
       'Suppose a derivation existed. Only one rule concludes at a <code>load</code>, and it comes with a premise: address <code>l</code> holds some value. But the heap is empty, so it holds nothing. Two contradictory facts about the same lookup, and the proof is over.',
       'Three moves, each of them a tactic you already have. <code>intro</code> to assume the derivation. The branch form of <code>cases</code>, because the premise has to arrive under a name. Then <code>absurd</code>, which takes a fact and a refutation of that fact and hands you anything at all — and the refutation is a one-line <code>simp</code>, which has to be told the definition of <code>Heap.empty</code>.',
       'The first line is <code>intro hex</code>, which turns the goal into <code>False</code> and puts <code>hex : Exec (Cmd.load x l) { store := σ, heap := Heap.empty } s\'</code> in the context. Then <code>cases hex with</code>, <code>| load hl =></code>, and a body of the form <code>exact absurd hl (by simp [Heap.empty])</code>.'
     ],
     sol:'theorem exec_load_stuck (x : Var) (l : Loc) (σ : Store) (s\' : State) :\n    ¬ Exec (.load x l) ⟨σ, Heap.empty⟩ s\' := by\n  intro hex\n  cases hex with\n  | load hl => exact absurd hl (by simp [Heap.empty])',
     solNote:'Nothing in this proof mentions <code>s\'</code>, which is the point: the derivation was refused before any question about the final state arose.',
     expl:'The proof spends the "least relation" reading. If <code>Exec</code> were some arbitrary relation closed under the ten rules, this theorem would be unprovable — <code>Anything</code> is closed under all ten and contains this triple. What makes it provable is that a proof of <code>Exec (.load x l) s s\'</code> can only be a constructor application, so inverting it hands you the constructor\'s premise as a fact, and the fact is false of an empty heap. Inversion converts "no rule concludes this" into a contradiction you can hold in your hand.',
     walk:[
       {tac:'intro hex', h:'The goal <code>¬ P</code> is <code>P → False</code>, so introducing the antecedent gives you <code>hex : Exec …</code> and leaves <code>⊢ False</code>. You are now in the world where the load succeeded, and the job is to show that world is empty.'},
       {tac:'cases hex with', h:'One case survives the command index, as in <code>exec_load_inv</code>. What is different is that the goal, <code>False</code>, does not mention anything the inversion substituted — so nothing about the goal changes and the entire yield of the tactic is the new hypothesis.'},
       {tac:'| load hl =>', h:'Names the premise: <code>hl : { store := σ, heap := Heap.empty }.heap l = some v✝</code>. The projection is displayed unreduced, which is only a display: the term is <code>Heap.empty l = some v✝</code>, and <code>simp</code> sees through the projection without being asked.'},
       {tac:'exact absurd hl (by simp [Heap.empty])', h:'<code>absurd</code> takes a proof of <code>P</code> and a proof of <code>¬ P</code> and gives you anything, <code>False</code> included. The second argument is a proof of <code>¬ ({store := σ, heap := Heap.empty}.heap l = some v✝)</code>, built on the spot: <code>simp</code> is handed <code>Heap.empty</code>\'s definition, reduces the left-hand side to <code>none</code>, and closes the goal because <code>none = some v✝</code> is a disagreement between two constructors.'}
     ],
     deep:[
       {t:'trace', title:'exec_load_stuck, three steps',
        start:'x : Var\nl : Loc\nσ : Store\ns\' : State\n⊢ ¬Exec (Cmd.load x l) { store := σ, heap := Heap.empty } s\'',
        steps:[
          {tac:'intro hex', state:'x : Var\nl : Loc\nσ : Store\ns\' : State\nhex : Exec (Cmd.load x l) { store := σ, heap := Heap.empty } s\'\n⊢ False',
           h:'The negation is gone from the goal and its content is in the context. Standard, and the same first line as Unit 00\'s refutation.'},
          {tac:'cases hex with | load hl =>', state:'case load\nx : Var\nl : Loc\nσ : Store\nv✝ : Val\nhl : { store := σ, heap := Heap.empty }.heap l = some v✝\n⊢ False',
           h:'<code>s\'</code> has left the context — the rule computed it, so it was identified with the record the rule builds and nothing refers to it any more. What arrived is a claim that the empty heap holds a value.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Compare this with what an <code>Option</code>-valued interpreter would have let you state. There, the theorem would read <code>… (.load x l) ⟨σ, Heap.empty⟩ = none</code> — a positive claim about a computed answer, closed by evaluating it, and indistinguishable in form from the same claim about <code>forever</code>. Here the theorem is that a set is empty, and its proof is that no rule can put anything in it.'}
     ],
     pitfall:'Writing <code>by simp</code> without <code>[Heap.empty]</code>. <code>simp</code> gets as far as stripping the projection and then stops, leaving <code>⊢ ¬Heap.empty l = some v✝</code> reported as an unsolved goal — it has no reason to unfold a <code>def</code> nobody named. The second most common is aiming <code>absurd</code> the wrong way round, as <code>absurd (by simp [Heap.empty]) hl</code>: the fact comes first and its refutation second, so this offers <code>hl</code> in the slot wanting a negation, and Lean reports an <code>Application type mismatch</code> in which <code>hl</code> <i>is expected to have type</i> <code>¬?m.87</code>. A second complaint arrives with it, <code>`simp` made no progress</code>, and it is a distraction: the <code>by</code> block was being elaborated against a goal the mismatch had left undetermined. Fix the argument order and both go.',
     variants:'Replace <code>Heap.empty</code> by a heap that does hold something at <code>l</code> and the theorem becomes false, with an explicit witness: <code>Exec.load (singleton_same 3 7)</code> proves <code>Exec (.load x 3) ⟨σ, Heap.singleton 3 7⟩ ⟨Store.set σ x 7, Heap.singleton 3 7⟩</code>. Change the command to <code>.write l e</code> or to <code>.free l</code> and the same four lines work with the branch renamed to <code>| write hl =></code> or <code>| free hl =></code>, because those two rules carry the identical premise — three of the eight commands are stuck on an empty heap and they are stuck for one reason. Change it to <code>.assign x e</code> and the statement is false at the only point it could be: <code>Exec.assign</code> has no premise at all, so <code>Exec.assign</code> on its own proves <code>Exec (.assign x e) ⟨σ, Heap.empty⟩ ⟨Store.set σ x (e.eval σ), Heap.empty⟩</code>. Assignment touches no memory and cannot get stuck.'},

    /* ---------------------------------------------------------------- seq --- */

    {t:'p', h:'One more, and it is the one whose shape recurs. A sequence <code>c₁ ;; c₂</code> was run; you want to say something about <code>c₂</code>. The <code>seq</code> rule has two premises, so inverting once gives you two derivations, and the state between them arrives with no name because nothing in the statement mentions it.'},

    {t:'ex',
     id:'x44',
     name:'exec_skip_seq_inv',
     hard:false,
     why:'Nested inversion — an inversion whose result is itself a derivation to invert — and your first sight of a middle state that Lean names and you cannot. Every later rule about <code>;;</code> that has to take a run apart rather than build one opens with the same <code>cases h with | seq h₁ h₂</code>, and the proofs in Module 6 that fail without <code>rename_i</code> fail on exactly this dagger.',
     setup:'<code>;;</code> is <code>Cmd.seq</code>, so <code>.skip ;; c</code> is a command like any other and inversion applies to it in the usual way. Two inversions are needed and no other tactic.',
     goal:'theorem exec_skip_seq_inv {c : Cmd} {s s\' : State} (h : Exec (.skip ;; c) s s\') : Exec c s s\' := by',
     hints:[
       'You are given that <code>skip</code> followed by <code>c</code> takes <code>s</code> to <code>s\'</code>, and asked to show that <code>c</code> alone takes <code>s</code> to <code>s\'</code>. The two statements differ only in the leading <code>skip</code>, which by <code>exec_skip_inv</code> changes nothing — but the version you need is the one where <code>skip</code> is buried inside a sequence.',
       'A run of a sequence is a run of the first command to some intermediate state, followed by a run of the second from there. Invert to get those two runs. The first is a run of <code>skip</code>, so the intermediate state is the state you started in; substitute that, and the second run is the goal.',
       'Two <code>cases</code>. The first is on <code>h</code>, in the named-branch form, since you need both premises. The second is on the premise that is a run of <code>skip</code>, and it needs no branch names at all.',
       'The proof opens <code>cases h with</code> / <code>| seq h₁ h₂ =></code>, which leaves <code>h₁ : Exec Cmd.skip s s\'✝</code> and <code>h₂ : Exec c s\'✝ s\'</code> with the middle state daggered. Then <code>cases h₁</code> collapses the dagger onto <code>s</code>, and what is left is <code>h₂</code> at the type of the goal.'
     ],
     sol:'theorem exec_skip_seq_inv {c : Cmd} {s s\' : State} (h : Exec (.skip ;; c) s s\') : Exec c s s\' := by\n  cases h with\n  | seq h₁ h₂ => cases h₁; exact h₂',
     solNote:'The whole proof is two inversions and a hypothesis handed back. Nothing computes, nothing rewrites, and there is no lemma.',
     expl:'The first inversion is on the command index and leaves the one <code>seq</code> case, whose two explicit arguments are named <code>h₁</code> and <code>h₂</code>. Its three implicit states are not named; the one that matters is the intermediate state, which appears as <code>s\'✝</code> in both new hypotheses. The second inversion, on <code>h₁ : Exec Cmd.skip s s\'✝</code>, is <code>exec_skip_inv</code> done in place: the <code>skip</code> rule forces its two states to coincide, so <code>s\'✝</code> is identified with <code>s</code> everywhere it occurs — which includes <code>h₂</code>, whose type becomes <code>Exec c s s\'</code>. That is the goal, so <code>exact h₂</code> ends it.',
     walk:[
       {tac:'cases h with', h:'Inversion on the sequence. Nine constructors go; <code>Exec.seq</code> survives, and unification also fixes <code>c₁</code> as <code>Cmd.skip</code> and <code>c₂</code> as <code>c</code>, so neither appears as a loose variable afterwards.'},
       {tac:'| seq h₁ h₂ =>', h:'Names the two explicit arguments — the two sub-derivations. The five implicit binders <code>{s s\' s\'\' c₁ c₂}</code> get no names, and the one that survives visibly is the intermediate state, printed <code>s\'✝</code>. The case tag is <code>case seq</code>.'},
       {tac:'cases h₁', h:'Inversion on the <code>skip</code> derivation. The rule\'s conclusion has the same state twice, so this identifies <code>s\'✝</code> with <code>s</code>. The substitution reaches every hypothesis, and the one it matters for is <code>h₂</code>, which changes type under your feet from <code>Exec c s\'✝ s\'</code> to <code>Exec c s s\'</code>. The case tag becomes <code>case seq.skip</code> — one tag per level of nesting, dot-separated.'},
       {tac:'exact h₂', h:'The context now contains a proof of the goal. This is what inversion is for: nothing was constructed, and the proof was obtained by making a hypothesis more specific until it became the thing wanted.'}
     ],
     deep:[
       {t:'trace', title:'exec_skip_seq_inv, two inversions',
        start:'c : Cmd\ns s\' : State\nh : Exec (Cmd.skip ;; c) s s\'\n⊢ Exec c s s\'',
        steps:[
          {tac:'cases h with | seq h₁ h₂ =>', state:'case seq\nc : Cmd\ns s\' s\'✝ : State\nh₁ : Exec Cmd.skip s s\'✝\nh₂ : Exec c s\'✝ s\'\n⊢ Exec c s s\'',
           h:'Three states where the statement mentioned two. <code>s\'✝</code> is the middle one, and the dagger means Lean invented the name because you did not supply one — the constructor binds it implicitly, so the branch\'s name list never reaches it.'},
          {tac:'cases h₁', state:'case seq.skip\nc : Cmd\ns s\' : State\nh₂ : Exec c s s\'\n⊢ Exec c s s\'',
           h:'The daggered state is gone and <code>h₂</code> has moved onto the goal\'s type. Nothing in the tactic mentioned <code>h₂</code>; the substitution swept the whole context, which is why inversion on one hypothesis can finish a proof about another.'}
        ],
        done:'No goals.'},
       {t:'p', h:'If you wanted to talk about the middle state rather than eliminate it — which is what happens the moment the first command is not <code>skip</code> — one line does it, and every occurrence in <code>h₁</code> and <code>h₂</code> follows.'},
       {t:'code', tag:'illustration', src:'example {c₀ c : Cmd} {s s\' : State} (h : Exec (c₀ ;; c) s s\') : True := by\n  cases h with\n  | seq h₁ h₂ =>\n    rename_i sMid\n    trivial'},
       {t:'state', cap:'The context after <code>rename_i sMid</code>. This is the shape every <code>seq</code> case in Module 6 starts from.', src:'case seq\nc₀ c : Cmd\ns s\' sMid : State\nh₁ : Exec c₀ s sMid\nh₂ : Exec c sMid s\'\n⊢ True'}
     ],
     pitfall:'Reaching for <code>obtain ⟨sMid, h₁, h₂⟩ := h</code>, on the grounds that a <code>seq</code> derivation is a triple of a state and two proofs. It is a constructor application, not a tuple, and the pattern has to line up against five implicit arguments as well as the two explicit ones. It does not, and the failure is quiet: <code>obtain</code> reports nothing, and the context comes back holding <code>s\'✝</code>, <code>h₁✝</code> and <code>h₂✝</code> — every one of the three names you typed went inaccessible, and <code>sMid</code> is not even among them. The complaint arrives on the first line that reaches for one of them, and says only that it does not exist. Continue as the solution does and that line is <code>cases h₁</code>, giving <code>Unknown identifier `h₁`</code> and then a second, worse error underneath it — <code>cases</code> was left holding a metavariable and reports <i>major premise type is not an inductive type</i>. Go straight to <code>exact h₂</code> instead and it is <code>Unknown identifier `h₂`</code>. Either way: when a name you introduced on the previous line is reported unknown, the previous line is where to look, and anything below the first error is noise.',
     variants:'Reverse the sequence to <code>Exec (c ;; .skip) s s\'</code> and the theorem is still true, with the second inversion aimed at <code>h₂</code> instead: <code>cases h with | seq h₁ h₂ => cases h₂; exact h₁</code>. Replace <code>.skip</code> by an arbitrary first command and the statement becomes false, at the one place the <code>skip</code> rule was carrying it: nothing then identifies the middle state with <code>s</code>. The counterexample is two commands long — take the first to be <code>.assign 0 (.const 1)</code> and the second to be <code>.skip</code>, run from the store <code>fun _ => 0</code>. <code>Exec.seq Exec.assign Exec.skip</code> derives the sequence, so the claim would give <code>Exec .skip s s\'</code> with <code>s\'</code> the state whose store sends <code>0</code> to <code>1</code>; <code>exec_skip_inv</code> then forces <code>s\' = s</code>, and <code>storeSet_same</code> reads that off as <code>1 = 0</code>. Drop the second <code>cases</code> and the proof fails on the middle state, in as many words: <code>h₂</code> <i>has type</i> <code>Exec c s\'✝ s\'</code> <i>but is expected to have type</i> <code>Exec c s s\'</code>.'},

    /* ============================================================== closing === */

    {t:'dod', h:'You can say why an <code>Option</code>-valued interpreter is refused on two independent grounds, and which of the two is repairable. You can read <code>inductive Exec : Cmd → State → State → Prop</code> as ten inference rules, say which arguments are indices and what would break if they were parameters, and build a derivation for a concrete two-command program as a term. You can invert a derivation with <code>cases</code>, read the case tag, name a branch\'s explicit arguments and recognise its implicit ones by their daggers, and rename one with <code>rename_i</code>. And you have proved that a program which reads an unallocated address reaches no state at all — which is what this semantics offers in place of an error value.'},

    {t:'p', h:'You can look at the last step of a derivation. The theorem we actually want — that a command has at most one final state — needs us to reason about <i>every</i> derivation at once, and on a derivation that is not the induction you know.'}

  ]
});
