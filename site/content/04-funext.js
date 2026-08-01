registerChapter({
  id: 'funext',
  num: '03',
  phase: 'Phase 0 · Getting started',
  title: 'Functions as values',
  blurb: 'Two functions are equal when they agree everywhere — a principle Lean has to be given rather than compute — and the three-move pattern that turns it into a proof.',

  /* One exhibit quotes real `#check @funext` / `#check @congrFun` output, whose
     types are stated in full generality, so `Sort` appears on the page nine
     units before `14-assertions` books it. The caption on that block tells the
     reader to read `α` and `β` as `Nat` and names the unit that owns the
     machinery; nothing on the page uses it. ERRATA §10's first kind. */
  ledgerAllow: ['Sort'],

  /* `x10`'s `why` says, in as many words, that the same opening appears at the
     top of the `update` proofs in Unit 04. That is a roadmap, not a use: no
     block on this page contains `update`. ERRATA §10's legitimate kind. */
  ledgerForward: ['update'],

  orient: {
    youWill: [
      'Say when reduction settles an equation between two functions, and name the two ways it can fail.',
      'State function extensionality, and say why it is an extra principle rather than a consequence of the rules.',
      'Turn an equation between functions into an equation at a point with <code>funext</code>, and go back with <code>congrFun</code>.',
      'Audit a proof with <code>#print axioms</code> and read what the audit reports.',
      'Split a goal on any proposition with <code>by_cases h : p</code>, work in <code>case pos</code> and <code>case neg</code>, and say what the split costs when the proposition is not one Lean can decide.',
      'Collapse an <code>if</code> by hand with <code>if_pos</code> and <code>if_neg</code>, and say when <code>simp [h]</code> will do it for you.',
      'Run one tactic on every remaining goal with <code>&lt;;&gt;</code>, and recognise the moment its branches stop agreeing.',
      'Tell <code>x ≠ a</code> from <code>a ≠ x</code> as <i>terms</i>, and repair the difference with <code>Ne.symm</code>.'
    ],
    needs: [
      'Unit 02: definitional versus propositional equality, and the rule that a variable in a position being cased on is what blocks reduction. <code>rw</code>, <code>simp</code>, <code>have</code>.',
      'Unit 01: <code>fun</code>, application, <code>∀</code> as a function type, implicit binders, dot notation, <code>constructor</code>, and the focus dot <code>·</code>.',
      'Unit 00: <code>¬ P</code> as <code>P → False</code>, and <code>x ≠ 4</code> as <code>¬ x = 4</code>.'
    ],
    payoff: 'Every equation between heaps in this course is an equation between functions, and every proof of one opens with the same three moves. This unit is where those three moves are installed; from Unit 05 onwards they are assumed.'
  },

  blocks: [

    /* ---------------------------------------- reduction, on functions --- */

    {t:'p', h:'Two heaps are two functions, so the question "are these heaps the same?" is an equation between functions. Unit 02 left that as an obstacle. Before treating it as one, test it: Unit 02\'s rule was that <code>rfl</code> closes an equation when both sides reduce to the same term, and nothing in that rule mentioned what the two sides had to be. So put a function on each side and see how far reduction gets.'},

    {t:'code', tag:'verified', cap:'An operation whose argument is a function and whose result is a function. Applying it to <code>f</code> gives you the function that applies <code>f</code> twice.',
     src:'def twice (f : Nat → Nat) : Nat → Nat := fun n => f (f n)'},

    {t:'code', tag:'illustration', cap:'Adding one to a number twice adds two — an equation between two functions <code>Nat → Nat</code>, neither of which is a number. Accepted, with not a tactic in sight.',
     src:'example : twice (fun n => n + 1) = fun n => n + 2 := rfl'},

    {t:'p', h:'Unfolding <code>twice</code> gives <code>fun n => (fun n => n + 1) ((fun n => n + 1) n)</code>, and substituting an argument into a <code>fun</code> is part of reduction, so that becomes <code>fun n => n + 1 + 1</code>. On the other side, <code>n + 2</code> is <code>n + 1 + 1</code> for the same reason <code>4</code> was <code>2 + 2</code> in Unit 02: <code>+</code> takes its cases on the second argument, and <code>2</code> is a numeral, so the split runs. Both sides arrive at one term. The part to carry forward is that reduction went <i>under the binder</i> — it did not stop at the <code>fun</code> and demand a point to work at. Which means it can be broken with the same lever Unit 02 used: addition splits on its second argument, so <code>0 + n</code> with <code>n</code> a variable is where reduction runs out, lambda or no lambda.'},

    {t:'code', tag:'sketch', cap:'True. Not closable this way.',
     src:'example : (fun n : Nat => 0 + n) = (fun n => n) := by rfl'},

    {t:'state', cap:'The <code>file:line:column</code> prefix is dropped here and everywhere on this page.',
     src:'error: Tactic `rfl` failed: The left-hand side\n  fun n => 0 + n\nis not definitionally equal to the right-hand side\n  fun n => n\n\n⊢ (fun n => 0 + n) = fun n => n'},

    {t:'p', h:'That failure is Unit 02\'s, wearing a lambda. Reduction goes under the binder, reaches <code>0 + n</code>, finds the variable <code>n</code> in the position <code>+</code> wants to split on, and stops — exactly as it stopped on <code>addNat 0 n</code>. The lambda contributed nothing to the failure and nothing to the fix; the missing step is still <code>Nat.zero_add</code>, and it is still a theorem proved by induction. The second way to break it is new, and it is the one this unit exists for. Take two functions about which you know nothing except that they agree at every point.'},

    {t:'code', tag:'sketch', cap:'True on any reading of "function" a mathematician would accept. Not closable this way either.',
     src:'example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by rfl'},

    {t:'state',
     src:'error: Tactic `rfl` failed: The left-hand side\n  f\nis not definitionally equal to the right-hand side\n  g\n\nf g : Nat → Nat\nh : ∀ (x : Nat), f x = g x\n⊢ f = g'},

    {t:'p', h:'Here there is nothing to unfold, nothing to substitute, and no case to take. <code>f</code> and <code>g</code> are variables; reduction has no material to work on and never will, no matter which lemma about <code>Nat</code> you supply. This is not a stuck computation that a theorem could finish. It is a statement that the rules of reduction have no opinion about at all — and which is, nevertheless, true.'},

    /* --------------------------------------------- the extra principle --- */

    {t:'sec', s:'The principle reduction does not have'},

    {t:'defn', term:'Function extensionality',
     h:'Two functions with the same domain and codomain are <b>equal</b> if they take the same value at every point: if <code>f x = g x</code> for all <code>x</code>, then <code>f = g</code>.',
     cap:'On paper this is what "function" means and there is nothing to argue about. Inside Lean it is a statement that has to be supplied, because Lean\'s notion of when two terms are the same is a notion about how they are <i>written</i>.'},

    {t:'p', h:'Be precise about the gap. Definitional equality compares terms after reduction: unfold, substitute, split where you can, and see whether you land on the same text. Two functions can compute the same value at every argument and still be written differently — <code>fun n => 0 + n</code> and <code>fun n => n</code> are the pair you already have — and no rule of reduction turns "agrees everywhere" into "is the same text". The principle above closes that gap, and Lean provides it under the name <code>funext</code>.'},

    {t:'code', tag:'verified', cap:'The principle, stated at the one type this course needs it at, and proved by handing the family of equations to <code>funext</code>.',
     src:'theorem function_extensionality {f g : Nat → Nat}\n    (h : ∀ x, f x = g x) : f = g := funext h'},

    {t:'anat', src:'theorem function_extensionality {f g : Nat → Nat}\n    (h : ∀ x, f x = g x) : f = g := funext h',
     parts:[
       {m:'{f g : Nat → Nat}', h:'Implicit, because both are recoverable from the type of <code>h</code>. Write <code>function_extensionality hpt</code> and Lean reads <code>f</code> and <code>g</code> off <code>hpt</code>.'},
       {m:'(h : ∀ x, f x = g x)', h:'A <i>family</i> of equations, one for each <code>x</code>. Unit 01 established that a <code>∀</code> is a function type, so <code>h</code> is a function taking a point to a proof about that point: <code>h 7</code> is a proof of <code>f 7 = g 7</code>.'},
       {m:'f = g', h:'One equation, between the functions themselves. This is the thing you can hand to <code>rw</code>, chain with <code>Eq.trans</code>, or feed to <code>congrArg</code>. The family is not.'},
       {m:'funext h', h:'Application, in the sense of Unit 01: <code>funext</code> is a name whose type is the implication, and applying it to <code>h</code> produces the proof. No <code>by</code>, no tactic.'}
     ]},

    {t:'p', h:'The last two parts are the whole practical case for the principle, and it is better watched failing than argued. Suppose you were content to state heap laws pointwise — as families of equations rather than equations — on the grounds that they carry the same information. Try to use one.'},

    {t:'code', tag:'sketch', cap:'The pointwise hypothesis is exactly as strong as the equation. It is not as <i>usable</i>.',
     src:'example (f g : Nat → Nat) (h : ∀ x, f x = g x) : twice f = twice g := by\n  rw [h]'},

    {t:'state', cap:'<code>rw</code> looks for the left-hand side of what it is given. What it was given has left-hand side <code>f ?x</code> — <code>f</code> applied to something — and the goal never applies <code>f</code> to anything.',
     src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  f ?x\nin the target expression\n  twice f = twice g\n\nf g : Nat → Nat\nh : ∀ (x : Nat), f x = g x\n⊢ twice f = twice g'},

    {t:'code', tag:'illustration', cap:'Accepted, and the only change is that the hypothesis was converted first.',
     src:'example (f g : Nat → Nat) (h : ∀ x, f x = g x) : twice f = twice g := by\n  rw [function_extensionality h]'},

    {t:'p', h:'Every heap law from Unit 05 onwards is an equation between heaps, and the reason is on those two lines. A family of equations tells you about <code>f</code> at each point; it says nothing you can substitute when <code>f</code> occurs somewhere that is not an application — inside <code>twice</code>, inside another heap operation, inside a larger term. The alternative course, the one where heap laws are all stated with a leading <code>∀ x</code>, is a course in which <code>rw</code> can never be aimed at a heap law, and every proof re-derives the pointwise fact by hand.'},

    /* ------------------------------------------------ tactic, converse --- */

    {t:'sec', s:'funext forwards, congrFun back'},

    {t:'p', h:'Used as a term, <code>funext</code> takes a family and gives an equation. Used as a tactic, it runs the same implication backwards, from the goal: if the goal is an equation between functions, <code>funext x</code> replaces it with the equation at an arbitrary <code>x</code>, and puts <code>x</code> in the context for you to work with. The corpus proof of the add-one-twice equation from the top of this page spells it out.'},

    {t:'code', tag:'verified', src:'theorem twice_succ : twice (fun n => n + 1) = fun n => n + 2 := by\n  funext n\n  rfl'},

    {t:'trace', title:'twice_succ, tactic by tactic',
     start:'⊢ (twice fun n => n + 1) = fun n => n + 2',
     steps:[
       {tac:'funext n',
        state:'n : Nat\n⊢ twice (fun n => n + 1) n = n + 2',
        h:'The equation between two functions became an equation between two <code>Nat</code>s, and <code>n</code> — a name you chose — appeared in the context. Both sides gained an application: the left is now <code>twice (fun n => n + 1)</code> <i>at</i> <code>n</code>.'},
       {tac:'rfl',
        state:'No goals.',
        h:'Reduction from here is the computation on the first page of this unit, one point at a time.'}
     ],
     done:'No goals.'},

    {t:'p', h:'That proof did not need <code>funext</code> — the equation was already closable by <code>rfl</code> alone, as the first exhibit on this page showed — which is precisely why it is a safe place to watch the tactic work: you can see what it changed without also wondering whether the proof depended on it. Choose the name deliberately: <code>funext _</code> is accepted and leaves you a daggered inaccessible name for the point, which you then cannot mention.'},

    {t:'p', h:'The trip back is a separate lemma with a separate name. From <code>f = g</code> you may conclude <code>f n = g n</code>, for any <code>n</code> you like, and the proof is one application.'},

    {t:'code', tag:'verified', src:'theorem apply_eq {f g : Nat → Nat} (h : f = g) (n : Nat) : f n = g n :=\n  congrFun h n'},

    {t:'code', tag:'illustration', src:'#check @funext\n#check @congrFun'},

    {t:'state', cap:'Verbatim, on one line each. Read both with <code>α</code> and <code>β</code> as <code>Nat</code>: the <code>Sort</code> and the subscripted universes say only that the two lemmas hold at every type, and Unit 12 is where that machinery is spelled out and used.',
     src:'@funext : ∀ {α : Sort u_1} {β : α → Sort u_2} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g\n@congrFun : ∀ {α : Sort u_1} {β : α → Sort u_2} {f g : (x : α) → β x}, f = g → ∀ (a : α), f a = g a'},

    {t:'p', h:'Strip the implicit arguments and one says <i>family of equations in, one equation out</i> and the other says <i>one equation in, family of equations out</i>. Set against each other they are the two directions of a single biconditional. They are not, however, of equal standing, and Lean will tell you so if you ask it what a proof rests on.'},

    {t:'code', tag:'illustration', cap:'An audit. Each line names a theorem already in scope and asks what it ultimately depends on.',
     src:'#print axioms two_add_two\n#print axioms double_zero_left\n#print axioms apply_eq\n#print axioms function_extensionality'},

    {t:'state', src:'\'two_add_two\' does not depend on any axioms\n\'double_zero_left\' depends on axioms: [propext]\n\'apply_eq\' does not depend on any axioms\n\'function_extensionality\' depends on axioms: [Quot.sound]'},

    {t:'p', h:'<code>two_add_two</code> was <code>rfl</code>, and computation is free. <code>apply_eq</code> is also free: <code>congrFun</code> is the substitution property of equality applied to a function\'s argument, and substituting equals for equals is a rule Lean already has. <code>function_extensionality</code> is not free. <code>funext</code> is not an axiom in Lean, it is a theorem — but its proof goes through quotient types, a construction this course never has to build, so the audit reports the axiom that quotients rest on, <code>Quot.sound</code>. And <code>double_zero_left</code>, which was a <code>simp</code> call in Unit 02, brings in <code>propext</code>: <code>simp</code> rewrites propositions, and treating two equivalent propositions as interchangeable is itself an extra principle. Nothing here is a warning. It is a measurement, and every theorem in the rest of this course sits somewhere on that scale.'},

    {t:'detail', title:'The type theories that leave it out, and what they keep', open:false, blocks:[
      {t:'p', h:'Some type theories omit function extensionality, and the omission is deliberate. Without it, every proof of an equation is in the end a reduction the kernel can replay, and the theory keeps properties that depend on that — every closed term of type <code>Nat</code> reduces to a numeral, and equality of functions means agreement of their code. Adding the principle gives that up: <code>f = g</code> becomes provable by an appeal the kernel cannot replay. What it buys is the equation you can rewrite with.'}
    ]},

    {t:'ex',
     id:'x10',
     name:'funext_drill',
     hard:false,
     why:'The smallest possible use of the principle, on the smallest possible pair of functions, so that when the same opening appears at the top of the <code>update</code> proofs in Unit 04, and at the top of every heap proof after them, it is already familiar. It also settles by experiment the question this page opened with — which function equalities reduction can close and which it cannot.',
     setup:'Nothing beyond this page is needed. The statement is an equation between two functions <code>Nat → Nat</code>. Two lines: one to reduce it to a point, one to close it.',
     goal:'theorem funext_drill : (fun n : Nat => 0 + n) = (fun n => n) := by',
     hints:[
       'The goal is an equation whose two sides are both functions from <code>Nat</code> to <code>Nat</code>: the one that adds zero on the left of its argument, and the identity. It is not an equation between numbers, so there is no number in it to compute with.',
       'Two functions are equal when they agree at every point. So fix an arbitrary point and prove they agree there. At that point you are left with a fact about <code>Nat</code> — the one Unit 02 showed is <i>not</i> a computation, because addition splits on its second argument.',
       'The two tactics you want are <code>funext</code> and <code>simp</code>. <code>rfl</code> is not one of them: the fact left over at a point is <code>Nat.zero_add</code>, which Unit 02 showed is a theorem proved by induction rather than a computation, and <code>simp</code> carries it in its default stock, so neither tactic needs an argument.',
       'Open with <code>funext n</code>. That leaves <code>n : Nat</code> in the context and the goal <code>0 + n = n</code>, which <code>simp</code> closes using <code>Nat.zero_add</code>.'
     ],
     sol:'theorem funext_drill : (fun n : Nat => 0 + n) = (fun n => n) := by\n  funext n\n  simp',
     solNote:'A single <code>simp</code>, with no <code>funext</code> at all, is also accepted. That is not the lesson, and the reason is in the panel below.',
     expl:'Two failures had to be separated to get here. Reduction cannot close the goal, and the obstruction is the variable under <code>0 +</code>; that is Unit 02\'s failure and <code>simp</code> is its cure. Reduction also cannot see past the lambda to a point at which to apply that cure; that is this unit\'s principle and <code>funext</code> is its cure. Each tactic removes exactly one of the two.',
     walk:[
       {tac:'funext n', h:'Turned the equation between two functions into an equation at an arbitrary point, and put that point in the context under the name <code>n</code>. Goal <code>(fun n => 0 + n) = fun n => n</code> became <code>0 + n = n</code>; the two lambdas were applied to <code>n</code> and reduced away.'},
       {tac:'simp', h:'Rewrote <code>0 + n</code> to <code>n</code> with <code>Nat.zero_add</code>, which is in <code>simp</code>\'s default stock, and closed the resulting <code>n = n</code>. No bracket was needed, because there is no definition of yours in the goal.'}
     ],
     deep:[
       {t:'trace', title:'The two lines, and the state between them',
        start:'⊢ (fun n => 0 + n) = fun n => n',
        steps:[
          {tac:'funext n',
           state:'n : Nat\n⊢ 0 + n = n',
           h:'Everything the lambda was hiding is now on display: one variable, one equation, no functions.'},
          {tac:'simp', state:'No goals.', h:'A theorem about <code>Nat</code>, applied.'}
        ]},
       {t:'p', h:'The second line is not interchangeable with <code>rfl</code>. Once the lambda is gone the goal has the look of a computation, and it is not one:'},
       {t:'code', tag:'sketch', src:'example : (fun n : Nat => 0 + n) = (fun n => n) := by\n  funext n\n  rfl'},
       {t:'state', src:'error: Tactic `rfl` failed: The left-hand side\n  0 + n\nis not definitionally equal to the right-hand side\n  n\n\nn : Nat\n⊢ 0 + n = n'},
       {t:'p', h:'Why a bare <code>simp</code> also works, and why it will stop working. <code>simp</code> rewrites inside a lambda, so it turns the left-hand side <code>fun n => 0 + n</code> into <code>fun n => n</code> directly and the two sides become the same text. That has nothing to do with picking a point; it is the same rewrite done under the binder. The moment the body contains an <code>if</code> whose condition mentions the bound variable, there is no rewrite available under the binder and <code>simp</code> stops dead. That is the goal the next section opens with, and this is what a bare <code>simp</code> does to it:'},
       {t:'code', tag:'sketch', src:'example (f : Nat → Nat) (a : Nat) : (fun x => if x = a then f a else f x) = f := by\n  simp'},
       {t:'state', src:'error: `simp` made no progress'},
       {t:'p', h:'So the two-line proof is the one that generalises and the one-line proof is the accident. The audit agrees: <code>#print axioms funext_drill</code> reports <code>[propext, Quot.sound]</code> whichever proof you give it. The one-line version pays for the principle as well; it does not show you where.'}
     ],
     pitfall:'Writing <code>funext n</code> and then <code>rfl</code>, on the theory that a goal with no lambda left in it must be a computation. The refusal is quoted in full in the fold above: <code>0 + n</code> is not definitionally equal to <code>n</code>, with <code>n : Nat</code> in the context and nothing to split on. It is Unit 02\'s failure word for word, which is the whole content of the mistake — removing the lambda changed the <i>shape</i> of the goal, not which lemmas its body needs. So read a refusal that arrives after <code>funext</code> as a statement about the body, never as a sign that the wrong tactic removed the lambda.',
     variants:'Turn the statement round to <code>(fun n : Nat =&gt; n + 0) = (fun n =&gt; n)</code> and <code>funext</code> becomes unnecessary and so does <code>simp</code>: the whole thing is <code>rfl</code>, because <code>n + 0</code> reduces to <code>n</code> — addition splits on its second argument and that argument is the numeral <code>0</code>. The side the zero sits on is the entire difference. Replace the right-hand side by <code>fun n =&gt; n + 0</code> as well and the two sides are the same text before anything happens, so <code>rfl</code> closes it without reducing at all.'
    },

    /* -------------------------------------------------------- the split --- */

    {t:'sec', s:'After funext: the point you now have to split on'},

    {t:'p', h:'A heap sends one address to a stored value and every other address somewhere else, so the function it <i>is</i> gets written with an <code>if</code> — which is why Unit 02 had to make the address a <code>Nat</code>: an <code>if</code> needs a condition Lean can decide, and equality of naturals is one. So here is the shape, with the heap\'s <code>Option</code> stripped off so nothing but the pattern is left. The claim is that overwriting <code>f</code> at <code>a</code> with the value <code>f</code> already has there changes nothing.'},

    {t:'txt', cap:'The goal, before any tactic, for an arbitrary <code>f : Nat → Nat</code> and an arbitrary <code>a : Nat</code>.',
     src:'(fun x => if x = a then f a else f x)  =  f'},

    {t:'p', h:'<code>funext x</code> is the first move, for the reason the last section gave, and it leaves this.'},

    {t:'state', src:'f : Nat → Nat\na x : Nat\n⊢ (if x = a then f a else f x) = f x'},

    {t:'p', h:'Reduction stops here, and by now the reason is recognisable: <code>if</code> takes cases on its condition, the condition is <code>x = a</code>, and <code>x</code> and <code>a</code> are both variables. There is no case to take. The difference from Unit 02 is that this time you can create one: a proposition either holds or it does not, so you may argue from both. <code>by_cases h : p</code> is the tactic that does it. It replaces the current goal with two copies of itself: the first carries a new hypothesis <code>h : p</code> and is labelled <code>case pos</code>, the second carries <code>h : ¬p</code> and is labelled <code>case neg</code>. Nothing else about the goal changes — in particular the <code>if</code> is still standing in both, because <code>by_cases</code> was aimed at the condition and knows nothing about the conditional around it.'},

    {t:'state', cap:'Both goals after <code>by_cases h : x = a</code>, as Lean prints them: the blank line separates them, and every later tactic sees only the first.',
     src:'case pos\nf : Nat → Nat\na x : Nat\nh : x = a\n⊢ (if x = a then f a else f x) = f x\n\ncase neg\nf : Nat → Nat\na x : Nat\nh : ¬x = a\n⊢ (if x = a then f a else f x) = f x'},

    {t:'detail', title:'Does the condition have to be decidable?', open:false, blocks:[
      {t:'p', h:'The <code>if</code> does: without Unit 02\'s instance the conditional cannot be written down at all. <code>by_cases</code> does not. Aim it at a proposition Lean has no instance for and it still splits — what changes is what the finished proof rests on, and the audit from the last section is the instrument that shows it.'},
      {t:'code', tag:'illustration',
       src:'theorem split_on_nats (n m : Nat) : n = n := by\n  by_cases h : n = m\n  · rfl\n  · rfl\n\ntheorem split_on_anything (p : Prop) (n : Nat) : n = n := by\n  by_cases h : p\n  · rfl\n  · rfl\n\n#print axioms split_on_nats\n#print axioms split_on_anything'},
      {t:'state', src:'\'split_on_nats\' does not depend on any axioms\n\'split_on_anything\' depends on axioms: [propext, Classical.choice, Quot.sound]'},
      {t:'p', h:'Splitting an equation between naturals costs nothing: Lean finds the instance and decides the condition. Splitting an opaque <code>p</code> makes <code>by_cases</code> reach for the excluded middle, and the audit records the axiom that gives it, <code>Classical.choice</code>. Every split in this course is of the first kind, because every condition in it is an equation between addresses.'}
    ]},

    {t:'p', h:'Each branch now holds enough to settle its <code>if</code>, and two library lemmas do the settling. <code>if_pos hc</code> is an equation saying the conditional equals its <i>then</i> branch, and it exists only once you have produced <code>hc</code>, a proof of the condition; <code>if_neg hnc</code> is the same for the <i>else</i> branch and a proof of the negation. The shape is new — a lemma whose statement you cannot write down until you have handed it a proof — and both results are equations, so <code>rw</code> takes them.'},

    /* ------------------------------------------------- Ne and its symm --- */

    {t:'h3', s:'Which way round the condition is written'},

    {t:'p', h:'<code>rw [if_neg hnc]</code> has to find the term <code>if c then t else e</code> in the goal, with the <i>same</i> <code>c</code> that <code>hnc</code> denies. Unit 00 gave you <code>a ≠ b</code> as notation for <code>¬ (a = b)</code>; what matters now is that it is notation for a term, and the term records which of the two is on the left. Lean has a name for it — <code>Ne a b</code> — and the display <code>a ≠ b</code> is that name in disguise. So <code>x ≠ a</code> and <code>a ≠ x</code> are two different terms, and only one of them matches an <code>if</code> testing <code>x = a</code>.'},

    {t:'code', tag:'sketch', cap:'The hypothesis is the right fact, written the wrong way round.',
     src:'example (f : Nat → Nat) (a x : Nat) (hax : a ≠ x) : (if x = a then f a else f x) = f x := by\n  rw [if_neg hax]'},

    {t:'state', cap:'The pattern Lean built from the hypothesis is on the second line; the term it searched is on the fourth. They differ in one place.',
     src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  if a = x then ?m.11 else ?m.12\nin the target expression\n  (if x = a then f a else f x) = f x\n\nf : Nat → Nat\na x : Nat\nhax : a ≠ x\n⊢ (if x = a then f a else f x) = f x'},

    {t:'p', h:'The repair is a lemma, not a rewrite: <code>Ne.symm</code> turns a proof of <code>a ≠ x</code> into a proof of <code>x ≠ a</code>. Dot notation resolves it the way Unit 01 said it does — <code>hax.symm</code> would also work, since the head constant of <code>hax</code>\'s type is <code>Ne</code>.'},

    {t:'code', tag:'illustration', cap:'Accepted. One wrapper, no other change.',
     src:'example (f : Nat → Nat) (a x : Nat) (hax : a ≠ x) : (if x = a then f a else f x) = f x := by\n  rw [if_neg (Ne.symm hax)]'},

    {t:'ex',
     id:'x11',
     name:'if_drill',
     hard:false,
     why:'Collapsing a conditional by hand, in both directions, with the disequality pointing the wrong way in one of them. Unit 04 asks you to drive a three-region case analysis with these two lemmas and to point at the single line where the disequality is consumed; you cannot do that until <code>if_pos</code> and <code>if_neg</code> are muscle memory and the orientation problem is one you have already been bitten by.',
     setup:'A conjunction, so <code>constructor</code> from Unit 01 splits it into two goals and the focus dot <code>·</code> takes them one at a time. You have <code>hab : a ≠ b</code>. Neither branch needs <code>funext</code> — there is no function equality here, only two conditionals. Both branches are one <code>rw</code>.',
     goal:'theorem if_drill (f : Nat → Nat) (a b : Nat) (hab : a ≠ b) :\n    (if a = a then f a else f b) = f a ∧ (if b = a then f a else f b) = f b := by',
     hints:[
       'Two claims joined by <code>∧</code>. The first says a conditional whose test is <code>a = a</code> equals its <i>then</i> branch. The second says a conditional whose test is <code>b = a</code> equals its <i>else</i> branch. You are told <code>a ≠ b</code>.',
       'Prove the two halves separately. For the first, the condition is true, and you need a proof of <code>a = a</code> — the most trivial proof in the course. For the second, the condition is false, and you need a proof that <code>b = a</code> does not hold; what you were handed says <code>a = b</code> does not hold, which is a different statement about the same two numbers.',
       'Four names, all of them from this page or the last: <code>constructor</code>, which splits a conjunction into its two halves; <code>if_pos</code> and <code>if_neg</code>, each of which wants a proof <i>about the condition</i> handed to it before it will give you an equation; and <code>Ne.symm</code>, which turns a disequality round. What <code>if_pos</code> and <code>if_neg</code> produce are equations, so <code>rw</code> is what consumes them.',
       'After <code>constructor</code> the first goal is <code>(if a = a then f a else f b) = f a</code>, and <code>rw [if_pos rfl]</code> closes it: the rewrite leaves <code>f a = f a</code> and <code>rw</code> finishes that on its own. The second goal is <code>(if b = a then f a else f b) = f b</code>, so the condition <code>if_neg</code> must be given a denial of is <code>b = a</code> — and <code>hab</code> denies <code>a = b</code>.'
     ],
     sol:'theorem if_drill (f : Nat → Nat) (a b : Nat) (hab : a ≠ b) :\n    (if a = a then f a else f b) = f a ∧ (if b = a then f a else f b) = f b := by\n  constructor\n  · rw [if_pos rfl]\n  · rw [if_neg (Ne.symm hab)]',
     solNote:'Both branches end without a closing tactic because <code>rw</code> tries <code>rfl</code> when it finishes, which Unit 02 stated and this is the first place it earns its keep.',
     expl:'Each half is one conditional and one lemma. What separates them is where the lemma\'s argument comes from: the <i>then</i> branch needs a proof of a reflexive equation, which costs nothing, and the <i>else</i> branch needs a disequality that you have — pointing the other way.',
     walk:[
       {tac:'constructor', h:'Replaced the goal <code>P ∧ Q</code> by two goals, <code>case left</code> and <code>case right</code>, one per field of the pair. Nothing else moved.'},
       {tac:'· rw [if_pos rfl]', h:'<code>if_pos rfl</code> is the equation <code>(if a = a then f a else f b) = f a</code>, built by feeding <code>if_pos</code> a proof that <code>a = a</code>. Rewriting with it turned the goal into <code>f a = f a</code>, and <code>rw</code>\'s silent trailing <code>rfl</code> closed that.'},
       {tac:'· rw [if_neg (Ne.symm hab)]', h:'<code>Ne.symm hab</code> converted <code>a ≠ b</code> into <code>b ≠ a</code>, which is what the condition <code>b = a</code> needs denied. <code>if_neg</code> then gave the equation collapsing the conditional to <code>f b</code>, leaving <code>f b = f b</code>, closed by the same silent <code>rfl</code>.'}
     ],
     deep:[
       {t:'trace', title:'The two branches',
        start:'f : Nat → Nat\na b : Nat\nhab : a ≠ b\n⊢ (if a = a then f a else f b) = f a ∧ (if b = a then f a else f b) = f b',
        steps:[
          {tac:'constructor',
           state:'case left\nf : Nat → Nat\na b : Nat\nhab : a ≠ b\n⊢ (if a = a then f a else f b) = f a',
           h:'The first of two goals. <code>hab</code> is present and irrelevant here — the first conditional is settled by reflexivity alone.'},
          {tac:'· rw [if_pos rfl]',
           state:'case right\nf : Nat → Nat\na b : Nat\nhab : a ≠ b\n⊢ (if b = a then f a else f b) = f b',
           h:'The first goal is gone and the second is on display. This is the one that needs <code>hab</code>, and needs it turned round first.'},
          {tac:'· rw [if_neg (Ne.symm hab)]', state:'No goals.', h:'The disequality is consumed on this line and nowhere else.'}
        ]},
       {t:'state', cap:'What <code>· rw [if_neg hab]</code> gives, with the <code>Ne.symm</code> left out. <code>case right</code> says the first branch went through and this is the second — which is how you locate a failure inside a split. The pattern built from <code>hab</code> tests <code>a = b</code>; the conditional in the goal tests <code>b = a</code>.',
        src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  if a = b then ?m.28 else ?m.29\nin the target expression\n  (if b = a then f a else f b) = f b\n\ncase right\nf : Nat → Nat\na b : Nat\nhab : a ≠ b\n⊢ (if b = a then f a else f b) = f b'}
     ],
     pitfall:'Writing <code>rw [if_pos]</code> with no argument, expecting Lean to find the proof of <code>a = a</code> itself. It does not. It performs the rewrite and hands the missing argument back as a second goal, so the bullet ends with <code>error: unsolved goals</code> over <code>case left.hc</code> and <code>⊢ a = a</code>. Nothing in that message names <code>if_pos</code>, and the error is reported on the bullet rather than on the rewrite, so it reads as a branch that failed to close rather than a lemma that was fed nothing. The tell is the <code>hc</code> on the end of the case name: it is <code>if_pos</code>\'s own hypothesis slot, come back as an obligation. Supplying <code>rfl</code> in the brackets is the difference between two goals and none.',
     variants:'Drop <code>hab</code> and the statement stays <i>true</i>: if <code>b</code> and <code>a</code> are the same number then <code>f a</code> and <code>f b</code> are the same value, so the second half holds either way. What breaks is this proof. <code>if_neg</code> demands a proof that <code>b = a</code> fails, and with the hypothesis gone nothing supplies one; the second branch has to split on <code>b = a</code> with <code>by_cases</code> and close both halves with <code>simp</code>, which is the next exercise. So <code>hab</code> buys the absence of a case split, not the truth of the theorem — and that is the trade you will be making for the rest of this course. Reverse it to <code>hab : b ≠ a</code> and the second branch becomes <code>rw [if_neg hab]</code> with the statement unchanged: which spelling costs you a wrapper is decided by how the conditional in the goal happens to be written, not by what you know.'
    },

    /* ---------------------------------------------- the three-move proof --- */

    {t:'h3', s:'The three moves, together'},

    {t:'p', h:'<code>funext</code>, then a split, then a lemma in each branch. Written out, with both branches driven by hand, the overwrite claim from the top of this section is five lines.'},

    {t:'anat', tag:'illustration', src:'example (f : Nat → Nat) (a : Nat) : (fun x => if x = a then f a else f x) = f := by\n  funext x\n  by_cases h : x = a\n  · rw [if_pos h, h]\n  · rw [if_neg h]',
     parts:[
       {m:'funext x', h:'Move one. The goal stops being an equation between functions and becomes an equation at <code>x</code>. Everything after this line is about a single point.'},
       {m:'by_cases h : x = a', h:'Move two. Two goals, each carrying a decision about the point: <code>h : x = a</code> in the first, <code>h : ¬x = a</code> in the second.'},
       {m:'·', h:'The focus dot from Unit 01, holding one branch at a time. It is punctuation, not a tactic: it takes no argument and its only effect is that the tactics under it see the first goal and must finish it.'},
       {m:'rw [if_pos h, h]', h:'Move three, in the branch where the condition holds. Two rewrites in one bracket, left to right: <code>if_pos h</code> collapses the conditional to <code>f a</code>, leaving <code>f a = f x</code>; then <code>h</code> itself rewrites <code>x</code> to <code>a</code> on the right, leaving <code>f a = f a</code>. This is the branch readers expect to be free and it is the one that needs the extra step.'},
       {m:'rw [if_neg h]', h:'Move three in the other branch, and here one rewrite is enough: collapsing the conditional to <code>f x</code> leaves <code>f x = f x</code>.'}
     ]},

    {t:'trace', title:'The same proof, with the two-rewrite bracket split so no state is skipped',
     start:'f : Nat → Nat\na : Nat\n⊢ (fun x => if x = a then f a else f x) = f',
     steps:[
       {tac:'funext x',
        state:'f : Nat → Nat\na x : Nat\n⊢ (if x = a then f a else f x) = f x',
        h:'The right-hand side was the bare <code>f</code>; applying it to <code>x</code> makes the two sides comparable term by term.'},
       {tac:'by_cases h : x = a',
        state:'case pos\nf : Nat → Nat\na x : Nat\nh : x = a\n⊢ (if x = a then f a else f x) = f x',
        h:'The first of two goals. The <code>if</code> has not moved — <code>by_cases</code> supplies a hypothesis and nothing else.'},
       {tac:'rw [if_pos h]',
        state:'case pos\nf : Nat → Nat\na x : Nat\nh : x = a\n⊢ f a = f x',
        h:'The conditional is gone and what remains is not <code>rfl</code>: <code>f a</code> and <code>f x</code> are different terms until <code>h</code> is used a second time.'},
       {tac:'rw [h]',
        state:'case neg\nf : Nat → Nat\na x : Nat\nh : ¬x = a\n⊢ (if x = a then f a else f x) = f x',
        h:'Rewriting <code>x</code> to <code>a</code> closed the first goal through <code>rw</code>\'s trailing <code>rfl</code>, and the second goal has come forward. This is the same conditional with the opposite decision attached.'},
       {tac:'rw [if_neg h]', state:'No goals.', h:'One rewrite, and the trailing <code>rfl</code> again.'}
     ],
     done:'No goals.'},

    {t:'p', h:'Both branches ended in a rewrite followed by an implicit reflexivity, which raises the question of whether they had to be written separately at all. They did not. <code>simp [h]</code> collapses a conditional whose condition <code>h</code> decides, in either direction, and it will use <code>h</code> as a rewrite as well — which covers the extra step the positive branch needed. And <code>&lt;;&gt;</code> runs one tactic on <i>every</i> goal the tactic before it produced, so the two branches can be written once.'},

    {t:'cmp',
     left: {t:'Driven by hand', kind:'good', tag:'sketch', h:'Four lines, and the location of each fact\'s use is visible: <code>h</code> is consumed twice in the positive branch and once in the negative.',
            src:'funext x\nby_cases h : x = a\n· rw [if_pos h, h]\n· rw [if_neg h]'},
     right:{t:'Both branches at once', kind:'good', tag:'sketch', h:'Two lines. <code>&lt;;&gt;</code> feeds <code>simp [h]</code> to both goals; <code>h</code> is a different hypothesis in each, and that is the point — the <i>text</i> is the same, the meaning is not.',
            src:'funext x\nby_cases h : x = a <;> simp [h]'}},

    {t:'note', kind:'key', title:'When &lt;;&gt; is available and when it is not',
     h:'<code>t &lt;;&gt; s</code> is one tactic built out of two: run <code>t</code>, then run <code>s</code> on every goal <code>t</code> left behind. It is the move to reach for exactly when the same <i>text</i> closes every branch — which is not the same as the branches being alike. It fails as soon as they diverge, and the failure names one branch only, so the error looks like a lemma being wrong rather than a shape being wrong.'},

    {t:'code', tag:'sketch', cap:'<code>if_pos</code> is correct in one branch out of two.',
     src:'example (f : Nat → Nat) (a : Nat) : (fun x => if x = a then f a else f x) = f := by\n  funext x\n  by_cases h : x = a <;> rw [if_pos h]'},

    {t:'state', cap:'<code>case neg</code> in the report is how you tell this apart from a mistyped lemma name. The positive branch succeeded and is not mentioned.',
     src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  if ¬x = a then ?m.34 else ?m.35\nin the target expression\n  (if x = a then f a else f x) = f x\n\ncase neg\nf : Nat → Nat\na x : Nat\nh : ¬x = a\n⊢ (if x = a then f a else f x) = f x'},

    {t:'p', h:'One more thing <code>simp</code> does, which you will meet far more often than you would like. Given a hypothesis it cannot use — a disequality written the wrong way round, say — it does not stop and complain. It collapses what it can, leaves the rest, and hands back a goal in the form of an obligation you have not discharged. The error you get is about the goal still being open, and arrives at the end.'},

    {t:'code', tag:'sketch', src:'example (f : Nat → Nat) (a x : Nat) (hax : a ≠ x) : (if x = a then f a else f x) = f x := by\n  simp [hax]'},

    {t:'state', cap:'Two messages. The first is the goal <code>simp</code> could not finish; the second names the argument it never used. The linter\'s two trailing lines, a <code>Hint:</code> and a <code>Note:</code> about switching it off, are dropped here.',
     src:'error: unsolved goals\nf : Nat → Nat\na x : Nat\nhax : a ≠ x\n⊢ x = a → f a = f x\n\nwarning: This simp argument is unused:\n  hax'},

    {t:'p', h:'Read the residue as a bill. <code>simp</code> turned the conditional into an implication — <i>if the condition holds, the then-branch had better match</i> — and is asking you to pay it. The fix here is <code>Ne.symm</code>, and once <code>hax</code> points the right way the implication never appears, because <code>simp</code> settles the condition instead of deferring it. The unused-argument warning is the sharper of the two messages: it says which hypothesis was ignored, and a hypothesis is ignored for a reason.'},

    {t:'ex',
     id:'x12',
     name:'by_cases_drill',
     hard:false,
     why:'The first goal on this page whose positive branch is not free. The conditional collapses to <code>f x</code> and the goal wants <code>f y</code>, and the only thing that reconciles them is the branch hypothesis, used a second time on the goal itself. Every heap proof from Unit 04 onwards has a branch shaped like this one, and readers who have not met it look for a missing lemma.',
     setup:'No <code>funext</code>: the statement is already an equation between two values. One split, and then each branch closed. You may drive the branches by hand or run one tactic on both.',
     goal:'theorem by_cases_drill (f : Nat → Nat) (x y : Nat) :\n    (if y = x then f x else f y) = f y := by',
     hints:[
       'The goal says: the conditional that tests <code>y = x</code>, returning <code>f x</code> when it holds and <code>f y</code> when it does not, equals <code>f y</code>. Nothing in the context says whether <code>y = x</code>. Both <code>x</code> and <code>y</code> are arbitrary.',
       'Consider the two cases. If <code>y</code> and <code>x</code> are different, the conditional takes its else branch and the claim is immediate. If they are the same, the conditional takes its then branch and gives you <code>f x</code> — which is not literally <code>f y</code>, and is equal to it only because <code>y</code> and <code>x</code> are the same number. That second observation has to be used, and used on the goal.',
       'The tactic that splits a goal on a proposition nothing in the context settles is <code>by_cases</code>. After it, a branch can be finished either with <code>if_pos</code> / <code>if_neg</code> and a further rewrite, or by handing the branch hypothesis to <code>simp</code>, which does both jobs at once. <code>&lt;;&gt;</code> is what lets one line stand for both branches, and it is the right move exactly when their text agrees.',
       'Open with <code>by_cases h : y = x</code> — the condition spelled exactly as the goal writes it. That leaves two goals, <code>case pos</code> carrying <code>h : y = x</code> and <code>case neg</code> carrying <code>h : ¬y = x</code>, with the conditional untouched in both, and <code>simp [h]</code> closes either one. All that is left to decide is whether to write that under two focus dots or once after <code>&lt;;&gt;</code>.'
     ],
     sol:'theorem by_cases_drill (f : Nat → Nat) (x y : Nat) :\n    (if y = x then f x else f y) = f y := by\n  by_cases h : y = x <;> simp [h]',
     solNote:'The hand-driven version is three lines and equally correct: <code>by_cases h : y = x</code>, then <code>· rw [if_pos h, h]</code> and <code>· rw [if_neg h]</code>. Unit 04 asks you to choose between the two styles for a stated reason, so write both now while the goal is small.',
     expl:'The statement is true for two unrelated reasons and the proof has to give both. In the negative branch the conditional is not taken and there is nothing more to say. In the positive branch it is taken, and what it returns matches the claim only after the branch hypothesis has been used to rewrite the goal. One tactic covers both because <code>simp [h]</code> reads <code>h</code> as a rewrite when it is an equation and as a decision when it is a negation.',
     walk:[
       {tac:'by_cases h : y = x', h:'Replaced the goal with two copies, <code>case pos</code> carrying <code>h : y = x</code> and <code>case neg</code> carrying <code>h : ¬y = x</code>. The conditional is unchanged in both; what changed is that each branch now contains something that decides it.'},
       {tac:'<;> simp [h]', h:'Ran one tactic on both goals. In <code>case pos</code> it rewrote <code>y</code> to <code>x</code> everywhere using <code>h</code>, which turned the condition into <code>x = x</code>, collapsed the conditional to <code>f x</code>, and left <code>f x = f x</code>. In <code>case neg</code> it used <code>h</code> to discharge the condition, collapsed the conditional to <code>f y</code>, and left <code>f y = f y</code>. Same eight characters, two different mechanisms.'}
     ],
     deep:[
       {t:'trace', title:'Both branches, driven one at a time so each one prints',
        start:'f : Nat → Nat\nx y : Nat\n⊢ (if y = x then f x else f y) = f y',
        steps:[
          {tac:'by_cases h : y = x',
           state:'case pos\nf : Nat → Nat\nx y : Nat\nh : y = x\n⊢ (if y = x then f x else f y) = f y',
           h:'The branch where the conditional will take its <i>then</i> arm and return <code>f x</code>, against a goal asking for <code>f y</code>.'},
          {tac:'· simp [h]',
           state:'case neg\nf : Nat → Nat\nx y : Nat\nh : ¬y = x\n⊢ (if y = x then f x else f y) = f y',
           h:'The first goal is closed and the second has come forward. The <code>if</code> is character for character what it was; only the hypothesis differs, and here it takes the <i>else</i> arm and returns <code>f y</code> on the nose.'},
          {tac:'· simp [h]', state:'No goals.', h:'Two bullets carrying the same text is precisely the condition under which <code>&lt;;&gt;</code> replaces them.'}
        ]},
       {t:'p', h:'What happens with no split at all, once, so the residue is recognisable later:'},
       {t:'code', tag:'sketch', src:'example (f : Nat → Nat) (x y : Nat) : (if y = x then f x else f y) = f y := by\n  simp'},
       {t:'state', cap:'<code>simp</code> got as far as it could without a decision and handed back the branch it could not settle.',
        src:'error: unsolved goals\nf : Nat → Nat\nx y : Nat\n⊢ y = x → f x = f y'},
       {t:'p', h:'That residue is the positive branch, written as an implication. It is exactly what <code>by_cases</code> would have produced as <code>case pos</code>, with the hypothesis on the left of an arrow instead of in the context — and it is where the second use of <code>h</code> is needed.'},
       {t:'p', h:'A statement proved in two branches can fail in only one of them, and which one is information. Turn the right-hand side into <code>f x</code> and the negative branch has nothing left to stand on — the identity function, evaluated at two different points, says so:'},
       {t:'code', tag:'illustration', cap:'The witness is <code>f</code> the identity, <code>x = 0</code>, <code>y = 1</code>. <code>h1</code> is then the conditional at <code>1 = 0</code>, which takes its <i>else</i> arm and gives <code>1 = 0</code>; <code>simp</code> decides that, turns <code>h1</code> into a contradiction, and closes the goal with it.',
        src:'example : ¬ ∀ (f : Nat → Nat) (x y : Nat), (if y = x then f x else f y) = f x := by\n  intro hall\n  have h1 := hall (fun n => n) 0 1\n  simp at h1'}
     ],
     pitfall:'Splitting the wrong equation: <code>by_cases h : x = y</code> instead of <code>y = x</code>. Both branches then carry a fact about the right two numbers, written the wrong way round for the conditional in the goal, and half the proof still goes through — <code>simp [h]</code> closes <code>case pos</code>, because rewriting <code>x</code> to <code>y</code> settles the condition as well as the other orientation would. The other half comes back as <code>error: unsolved goals</code> over <code>case neg</code>, <code>h : ¬x = y</code>, <code>⊢ y = x → f x = f y</code> — which is the residue a bare <code>simp</code> leaves, because in that branch <code>h</code> was of no use and <code>simp</code> was in effect run without it. Half a proof working is what makes this one slow to spot: nothing in the failure points at the line that caused it. Split on the condition as the goal writes it, not as you would have written it.',
     variants:'Reverse the conclusion to <code>= f x</code> and the theorem is false; the refutation is compiled in the panel above. It breaks at exactly one point, the negative branch: with <code>y</code> and <code>x</code> different the conditional returns <code>f y</code> while the claim asks for <code>f x</code>, <code>f</code> is free to separate them, and no hypothesis is in scope to save it — the identity at <code>0</code> and <code>1</code> is enough. Replace the then-branch by <code>f y</code> instead, giving <code>(if y = x then f y else f y) = f y</code>, and both branches become reflexivity, so <code>simp</code> alone closes it and the split is unnecessary: the split is needed only because the two arms return different terms.'
    },

    /* -------------------------------------------------------- close --- */

    {t:'dod', h:'You can say which equations between functions reduction settles and which it does not, and name the two different reasons it fails. You can state function extensionality, say why it is an extra principle rather than a consequence of how terms reduce, and show what a course without it would have to pay. You can move between an equation and its pointwise family in both directions, with <code>funext</code> and <code>congrFun</code>, and audit which of the two costs an axiom. You can split a goal on any proposition with <code>by_cases</code> — knowing what that costs when Lean cannot decide it — work in <code>case pos</code> and <code>case neg</code>, and collapse the resulting conditional either by hand with <code>if_pos</code> and <code>if_neg</code> or by handing the branch hypothesis to <code>simp</code>. You can run one tactic across every open goal with <code>&lt;;&gt;</code> and recognise, from a report naming a single branch, that the branches have diverged. And you can tell <code>x ≠ a</code> from <code>a ≠ x</code> as terms, and reach for <code>Ne.symm</code> before the rewrite fails rather than after.'},

    {t:'p', h:'You now have every tactic the next page needs. The theorems there are about updating a function at one point — which is, with one type changed, exactly what writing to memory will be.'}

  ]
});
