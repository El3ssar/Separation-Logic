registerChapter({
  id: 'language',
  num: '18',
  phase: 'Phase 3 · Programs and their semantics',
  title: 'A language that can get memory wrong',
  blurb: 'The smallest syntax that can commit a memory error, written down as an inductive type — and the design decisions built into it that every later proof will live with.',

  orient: {
    youWill: [
      'Declare an inductive type whose constructors take values of that same type, and read its values as the grammar of a language.',
      'Define a function on it by pattern matching, and say why Lean asks for no termination proof.',
      'Write <code>.const 3</code>, say what the leading dot resolves to and how, and predict how Lean will print the term back at you.',
      'Read a <code>structure</code> as a one-constructor inductive, build one with <code>⟨σ, h⟩</code>, project with <code>.store</code> and <code>.heap</code>, and close <code>⟨s.store, s.heap⟩ = s</code> by <code>rfl</code>.',
      'Prove <code>@Store.set = @update</code> and re-derive the store\'s two lookup laws in one line each.',
      'Say why a guard evaluates to <code>Bool</code> while an assertion lives in <code>Prop</code>, and predict the shape a guard hypothesis will have when you meet one.',
      'Say why the store cannot be divided the way the heap can, and what that will cost.'
    ],
    needs: [
      'Unit 00: the abbreviations, in particular <code>Store</code> as <code>Var → Val</code>.',
      'Unit 02: <code>inductive</code>, pattern-matching <code>def</code>, leading-dot constructor names, and the rule that <code>rfl</code> is blocked by a variable in a position being matched on.',
      'Unit 04: <code>update</code>, <code>update_same</code>, <code>update_other</code>.',
      'Unit 05: <code>Heap</code> as <code>Loc → Option Val</code>.',
      'Unit 09: why a <code>match</code> computes only when its scrutinee is a constructor application.',
      'Unit 10: <code>structure … where</code>, and field projection.'
    ],
    payoff: 'Every remaining unit of the course is about the seven declarations on this page. The execution relation of Unit 19 has a rule for every constructor of <code>Cmd</code> and two for the branching ones; the induction of Unit 20 is induction over those rules; the specifications of Unit 22 onwards are triples with a <code>Cmd</code> in the middle. Two decisions taken here are still shaping proofs at the end of the course: expressions cannot fault, which is what keeps every rule in Modules 5 and 6 to one case, and addresses are literals, which is why Unit 33\'s list segments describe memory no program in this language can walk.'
  },

  blocks: [

    /* =============================================== what is forced === */

    {t:'p', h:'A command, then. Which ones is decided by a single requirement: this language has to be able to get memory wrong. Unit 00\'s rule fails because a write lands in a cell some other name is describing; the sharper failure is a program asking for a cell that is not there. A language that only computes can commit neither. Every arithmetic expression has a value, every assignment to a variable succeeds, and nothing in such a language is ever asked for something it does not have. So three operations are forced — read a cell, write a cell, hand a cell back — together with something that puts commands in sequence, because no single command can free a cell and then read it. That is the whole requirement. Everything beyond it is convenience.'},

    {t:'p', h:'Price the extras before buying any. An inductive type is a closed list of ways to build a value, and the list is closed in a strong sense: add a constructor later and every function defined on the type by pattern matching acquires a missing case, every proof that ran through the cases acquires a missing branch, and every relation defined by rules over the type acquires a rule it does not have. In a compiler that is an afternoon. In a proof assistant it is a pass over the whole development. The constructor lists on this page are therefore decided once, and two of the eight commands are there for control flow that no specification in this course reaches until Units 35 and 36.'},

    /* ================================================== expressions === */

    {t:'sec', s:'Expressions, and what they are not allowed to do'},

    {t:'anat', cap:'An expression is a numeral, a program variable, or the sum or difference of two expressions — four cases, of which the last two are what make this a grammar rather than a list. <code>Nat</code> here is the literal number and <code>Var</code> the name of a program variable; both are <code>Nat</code> under Unit 00\'s abbreviations.',
     src:'inductive Atom where\n  | const : Nat → Atom\n  | var   : Var → Atom\n  | plus  : Atom → Atom → Atom\n  | minus : Atom → Atom → Atom\n  deriving Repr',
     parts:[
       {m:'inductive Atom where', h:'A new type, and what follows is the complete list of ways to make one. Unit 02 declared <code>Option</code> this way and printed <code>Nat</code>\'s own declaration; the only thing new is how many of the constructors point back at the type.'},
       {m:'| const : Nat → Atom', h:'Given a number, an expression. <code>Atom.const 7</code> is not the number seven; it is the piece of syntax that evaluates to it.'},
       {m:'| var   : Var → Atom', h:'Given a variable name, an expression. A <code>Var</code> is a <code>Nat</code>, so program variables are numbered rather than named — Unit 02 settled that a name has to have decidable equality, and nothing in the semantics wants more.'},
       {m:'| plus  : Atom → Atom → Atom', h:'The recursive constructor: two values of the type being declared, one more out. This is what makes an <code>Atom</code> a tree of unbounded depth rather than one of four fixed shapes.'},
       {m:'deriving Repr', h:'One word asking Lean to work out how to display a value of this type, so <code>#eval</code> on an <code>Atom</code> prints something. What happens to a type without it is at the foot of this page.'}
     ]},

    {t:'p', h:'A value of type <code>Atom</code> is a finite tree with numbers and variable names at the leaves. That is what <i>abstract syntax</i> means: the tree, with none of the brackets and precedence a concrete program text needs in order to determine it.'},

    {t:'p', h:'What matters most about that list is what is <b>missing</b> from it. There is no constructor that reads memory. An expression cannot dereference a pointer, so evaluating one cannot be handed an address that holds nothing, so evaluation is a total function and an expression has no way to fail. Only a command does. That split is a decision, and it is what keeps the semantics of the next unit to a readable size: were expressions able to fault, every rule about every command would have to say what happens when its expression faults, and the one memory error this course is about would be buried under a copy of itself in every rule.'},

    {t:'code', tag:'illustration', cap:'Building one and printing it. The <code>#eval</code> works because of <code>deriving Repr</code>.',
     src:'#check Atom.plus (.const 1) (.var 0)\n#eval  Atom.plus (.const 1) (.var 0)'},

    {t:'state', cap:'Both lines\' output. Two things in it are predictable rather than surprising.',
     src:'(Atom.const 1).plus (Atom.var 0) : Atom\nAtom.plus (Atom.const 1) (Atom.var 0)'},

    {t:'p', h:'The leading dots went in and did not come out. <code>.const 1</code> sits where an <code>Atom</code> is expected, and the dot means <i>look for this name in the namespace of the type expected here</i>: <code>Atom.plus</code> wants an <code>Atom</code>, so <code>.const</code> resolves to <code>Atom.const</code>. Take the expected type away and there is nothing to resolve against.'},

    {t:'code', tag:'sketch', cap:'No expected type: <code>#check</code> is being asked what this <i>is</i>.',
     src:'#check (.const 3)'},

    {t:'state', cap:'The error, with the position prefix dropped — a convention every quoted message on this page follows. Four constants in scope are called <code>const</code>, and nothing here says which.',
     src:'error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.const` could not be determined\n\nHint: Using one of these would be unambiguous:\n  [apply] `Atom.const`\n  [apply] `Function.const`\n  [apply] `Lean.ParserDescr.const`\n  [apply] `Lean.Omega.LinearCombo.const`'},

    {t:'p', h:'The other thing to predict is the printing. <code>#check</code> answered <code>(Atom.const 1).plus (Atom.var 0)</code> — constructor names in full, and the head of the term moved in front of a dot; <code>#eval</code>, going through <code>Repr</code>, did neither. The display convention is the one Unit 05 met on <code>h.write l v</code>, and its condition is exact: Lean writes <code>f a b c</code> as <code>a.f b c</code> when <code>a</code> is the <b>first explicit argument</b> whose type is the one <code>f</code>\'s namespace is named after. <code>Atom.plus</code> qualifies. The next definition will not.'},

    /* =============================================== evaluating it === */

    {t:'sec', s:'Evaluating an expression'},

    {t:'code', cap:'An expression has a value once you know what the variables hold, and that is what a store is — Unit 00 fixed <code>Store</code> as <code>Var → Val</code>. One clause per constructor. The store is bound <i>before</i> the colon, so it is fixed for the whole definition and is not matched on.',
     src:'def Atom.eval (σ : Store) : Atom → Val\n  | .const v  => v\n  | .var x    => σ x\n  | .plus a b => a.eval σ + b.eval σ\n  | .minus a b => a.eval σ - b.eval σ'},

    {t:'p', h:'Four clauses, four constructors, and the patterns are constructor applications written with the same leading dot — in a pattern the expected type is the type being matched on, so <code>.plus a b</code> is <code>Atom.plus a b</code> with <code>a</code> and <code>b</code> naming its components. Lean checks the cases are exhaustive, and if you delete one it says which value it cannot handle. That is the machinery Unit 02 used on <code>Option</code>, with a recursion added.'},

    {t:'p', h:'The recursion is the interesting part, because nothing here proves that it stops — and nothing has to. The calls in the last two clauses are <code>a.eval σ</code> and <code>b.eval σ</code>, and <code>a</code> and <code>b</code> are <i>components</i> of the value passed in: strictly smaller trees. A recursion whose arguments always shrink into their own constructors cannot run forever, Lean checks that condition syntactically on the shape of the clauses, and the definition is accepted with nothing asked of you. That is <b>structural recursion</b>, and it is the only kind in this course that comes free.'},

    {t:'detail', title:'What the four clauses actually become', open:false, blocks:[
      {t:'p', h:'The clause list is not stored. Lean compiles it into one application of a recursion principle generated along with the type, and keeps the four equations separately. Printing the definition shows the compiled form.'},
      {t:'code', tag:'illustration', src:'#print Atom.eval'},
      {t:'state', src:'def Atom.eval : Store → Atom → Val :=\nfun σ x => Atom.brecOn x (Atom.eval._f σ)'},
      {t:'p', h:'What this buys is one fact used constantly below: the four equations hold <i>definitionally</i>, so a goal whose expression is built from constructors reduces on its own — <code>(Atom.plus a b).eval σ = a.eval σ + b.eval σ</code> is closed by <code>rfl</code> at arbitrary <code>a</code> and <code>b</code> — while a goal about an expression that is still a variable does not reduce at all. Unit 09 gave the general form of that rule for <code>match</code>.'}
    ]},

    {t:'p', h:'The display rule from the previous section now pays off, in the negative direction. <code>Atom.eval</code>\'s first explicit argument is the <i>store</i>, not the atom, so Lean will never print it as <code>a.eval σ</code>: every goal state in this course spells out <code>Atom.eval σ a</code>. You may still write <code>a.eval σ</code>, because on input the dot puts <code>a</code> at the first explicit argument whose type is <code>Atom</code>, wherever in the list that is. What the dot will not do is guess the order — <code>Atom.eval a σ</code> written out in full reports <code>Application type mismatch</code> on the argument <code>a</code>.'},

    {t:'code', tag:'illustration', cap:'Input and display disagree, and the disagreement is provably harmless: both sides are one term.',
     src:'example (σ : Store) (a : Atom) : a.eval σ = Atom.eval σ a := rfl'},

    /* ==================================================== the store === */

    {t:'sec', s:'The store, which you already have'},

    {t:'code', cap:'A command that assigns to a variable changes the store at one point and leaves the rest alone. That is the only operation a store ever undergoes, and this is the whole of its interface.',
     src:'def Store.set (σ : Store) (x : Var) (v : Val) : Store :=\n  fun y => if y = x then v else σ y'},

    {t:'p', h:'<code>Store</code> is <code>Var → Val</code> is <code>Nat → Nat</code>, and Unit 04\'s <code>update</code> was declared at exactly that type with exactly that body. So these are not two functions that behave alike. They are one function under two names, and the first thing to do is prove it, because a proof of that is what lets the store\'s laws be Unit 04\'s laws rather than a fresh set.'},

    {t:'ex',
     id: 'x39',
     name: '@Store.set = @update, and the two store lookup laws',
     why: 'Unit 04\'s five theorems were about a function called <code>update</code> with no memory anywhere near it, and it would have been reasonable to write them off as a warm-up. They were not a warm-up. <code>update</code> <b>is</b> the store, and the first line here is what turns that from a remark into something the checker has agreed to. Every rule about assignment from Unit 22 on ends in the one-line proof you gave <code>update_same</code> in Unit 04, and this is where you find out you have seen it before.',
     setup: 'Three statements. The first is an equation between two functions, with no arguments applied — <code>@</code> in front of a name means <i>take the constant itself</i>. The second and third are the store\'s versions of <code>update_same</code> and <code>update_other</code>, and each has a one-term proof: the corresponding theorem, applied.',
     goal: 'example : @Store.set = @update :=\n  sorry\n\ntheorem storeSet_same (σ : Store) (x : Var) (v : Val) : Store.set σ x v x = v :=\n  sorry\n\ntheorem storeSet_other (σ : Store) (x y : Var) (v : Val) (hne : y ≠ x) :\n    Store.set σ x v y = σ y :=',
     hints: [
       'The first statement has no binders at all: no store, no variable and no value is in scope, and what it claims is that two functions of type <code>(Nat → Nat) → Nat → Nat → Nat → Nat</code> are the same function. The second says that reading the modified store at <code>x</code> gives back the value written there. The third says that reading it anywhere else gives what was there before, given that the address you are reading is not the one you wrote.',
       'Two functions given by the same formula are one function, and that is the whole of the first claim — made about the formulas, not about their values at some point. The other two are then not new propositions. <code>Store.set σ x v</code> and the modified function of Unit 04 are one object, so Unit 04\'s two lookup laws are already statements about it, and a proof of a proposition is a proof of any proposition that is the same proposition.',
       'The first needs <code>rfl</code>, and no <code>funext</code> — the equation is between the constants themselves, not between two functions applied to a point. The second and third are single terms: <code>update_same</code> and <code>update_other</code>. Nothing is proved <code>by</code> anything.',
       'The first line is <code>example : @Store.set = @update := rfl</code>, and it leaves nothing behind: that term closes the goal. For the second, <code>update_same</code> takes three explicit arguments in the order function, address, value, so the entire proof is <code>update_same σ x v</code>. For the third, <code>update_other</code> takes four — function, the address you wrote, the address you are reading, the value — and then the disequality last.'
     ],
     sol: 'example : @Store.set = @update := rfl\n\ntheorem storeSet_same (σ : Store) (x : Var) (v : Val) : Store.set σ x v x = v := update_same σ x v\ntheorem storeSet_other (σ : Store) (x y : Var) (v : Val) (hne : y ≠ x) :\n    Store.set σ x v y = σ y := update_other σ x y v hne',
     solNote: 'The <code>@</code> in the first line is documentation rather than necessity: neither <code>Store.set</code> nor <code>update</code> has an implicit argument, so <code>example : Store.set = update := rfl</code> is accepted too. Writing the <code>@</code> says out loud that the claim is about the two constants and not about anything they were applied to.',
     expl: 'Two definitions with the same body elaborate to the same term, and <code>rfl</code> is exactly the assertion that the checker can reduce both sides to one thing. Once that is on record, the two lookup laws need no proof of their own: the statement <code>Store.set σ x v x = v</code> and the statement <code>update σ x v x = v</code> are the same proposition, so a term of the second type is a term of the first, and <code>update_same σ x v</code> is that term.',
     walk: [
       {tac:'example : @Store.set = @update := rfl', h:'Unfolding both names gives the same term — <code>fun σ x v y => if y = x then v else σ y</code> — and nothing more has to happen. Contrast Unit 02, where the obstacle to <code>rfl</code> was a <i>variable in a position being matched on</i>: here nothing is being matched on, because neither side has been applied to anything.'},
       {tac:'… := update_same σ x v', h:'This does not transform the goal, it closes it. The term has type <code>update σ x v x = v</code>; the goal is <code>Store.set σ x v x = v</code>; the two are accepted as one because checking a term against a type is allowed to unfold <code>Store.set</code> and find <code>update</code> underneath. That unfolding is exactly what the line above put on record, and it is why nothing here needs a rewrite.'},
       {tac:'… := update_other σ x y v hne', h:'The same move with two more arguments, and the second of them carries all the content: <code>hne</code> is what stops the conditional inside the body from going the other way. The order matters, because <code>update_other</code> is stated <code>(f : Nat → Nat) (x y value : Nat) (hne : y ≠ x)</code> — the address you wrote, then the address you are reading, then the value, and the disequality last.'}
     ],
     deep: [
       {t:'trace', title:'What each of the two lookup goals looks like before its one term',
        start:'⊢ Store.set = update',
        steps:[
          {tac:'(first goal)  trace_state',
           state:'⊢ Store.set = update',
           h:'No context and no binders, and the <code>@</code>s are gone: the display drops them because neither constant has an implicit argument for them to have been suppressing. The whole content of the goal is that the two bodies reduce to one term.'},
          {tac:'(second goal) trace_state',
           state:'σ : Store\nx : Var\nv : Val\n⊢ σ.set x v x = v',
           h:'Lean prints <code>σ.set x v x</code>, not <code>Store.set σ x v x</code>: <code>Store.set</code>\'s first explicit argument <i>is</i> a <code>Store</code>, so it meets the display condition that <code>Atom.eval</code> failed. This is the goal <code>update_same σ x v</code> closes.'},
          {tac:'(third goal)  trace_state',
           state:'σ : Store\nx y : Var\nv : Val\nhne : y ≠ x\n⊢ σ.set x v y = σ y',
           h:'<code>hne</code> is <code>y ≠ x</code> — <i>the address I am reading is not the address I wrote</i>. Reverse it and the proof stops typechecking; the <code>variants</code> field below has the message.'}
        ]}
     ],
     pitfall: 'Trying <code>rfl</code> on the second statement. It is refused, and the refusal is the one Unit 02 taught you to read:<br><br><code>Not a definitional equality: the left-hand side<br>&nbsp;&nbsp;σ.set x v x<br>is not definitionally equal to the right-hand side<br>&nbsp;&nbsp;v</code><br><br>There is no <code>Note:</code> line under it, and that absence is the diagnosis. The keyword is not the problem — unfolding <code>Store.set</code> is allowed and would not help. The problem is the <i>term</i>: the body is <code>if y = x then v else σ y</code> with <code>y</code> instantiated to <code>x</code>, and <code>x = x</code> with <code>x</code> a variable is a conditional nothing reduces. That is why <code>update_same</code> exists at all, and why it was proved with <code>simp</code> rather than by reduction. A second message follows, reporting that <code>rfl</code> has type <code>?m.3 = ?m.3</code>: with the two sides refusing to meet, Lean never settles what <code>rfl</code> was to be a proof <i>of</i>, and says so separately. §<i>errors</i> catalogues the pair.',
     variants: 'Reverse the disequality in the third statement to <code>hne : x ≠ y</code> and the same term is rejected, naming the argument:<br><br><code>Application type mismatch: The argument<br>&nbsp;&nbsp;hne<br>has type<br>&nbsp;&nbsp;x ≠ y<br>but is expected to have type<br>&nbsp;&nbsp;y ≠ x<br>in the application<br>&nbsp;&nbsp;update_other σ x y v hne</code><br><br>The repair is <code>hne.symm</code>, and the reason the orientation is the way it is comes from <code>update_other</code>, where the conditional being decided is <code>y = x</code>.<br><br>Drop the disequality instead of reversing it and the third statement is worse than unprovable: it is <b>false</b>, and false at exactly one point: <code>y = x</code>, where the left-hand side is the value you wrote and the right-hand side is the value that was there before. The everywhere-zero store with <code>x = y = 0</code> and <code>v = 1</code> is a witness, and the refutation is four lines:<br><br><code>example : ¬ (∀ (σ : Store) (x y : Var) (v : Val), Store.set σ x v y = σ y) := by<br>&nbsp;&nbsp;intro h<br>&nbsp;&nbsp;have h₀ := h (fun _ => 0) 0 0 1<br>&nbsp;&nbsp;simp [Store.set] at h₀</code><br><br>Instantiating gives <code>h₀ : Store.set (fun x => 0) 0 1 0 = 0</code>, whose left-hand side computes to <code>1</code>; <code>simp</code> reduces it to <code>1 = 0</code>, sees that two numerals differ, and closes the goal from the contradiction. That single point is the whole reason <code>update_other</code> asks for a hypothesis at all.<br><br>Prove the two laws with <code>simp [Store.set]</code> and <code>simp [Store.set, hne]</code> instead and both go through — the definitions are the same, so the same two <code>simp</code> calls that worked in Unit 04 work here. That route re-proves rather than reuses, and it makes the identification invisible: nothing in either proof records that this function has been studied before. The whole point of the exercise is the first line, and the first line is what makes the other two free.'
    },

    {t:'p', h:'The two named laws do not go where you would guess. Nothing later in this course cites <code>storeSet_same</code> or <code>storeSet_other</code> by name; what the proofs from Unit 22 on do instead is restate the goal with <code>show</code> and close it with <code>simp [Store.set]</code> — <code>update_same</code>\'s proof from Unit 04, with one name changed, written out at the point of use. So the exercise buys recognition rather than a citation: when that line appears in a specification of assignment, you have already proved it and can read past it.'},

    /* ============================================ truncated arithmetic === */

    {t:'p', h:'<code>Val</code> is <code>Nat</code>, and subtraction on <code>Nat</code> is <b>truncated</b>: when the second argument is the larger, the answer is <code>0</code>, not a negative number. That is not a quirk of this course — it is what <code>-</code> means at the type <code>Nat</code>, and it means <code>Atom.minus</code> is total for the same reason everything else here is.'},

    {t:'code', tag:'illustration', cap:'Both lines print <code>0</code>.',
     src:'#eval (3 : Nat) - 5\n#eval (Atom.minus (.const 3) (.const 5)).eval (fun _ => 0)'},

    {t:'p', h:'The alternative was <code>Val := Int</code>, and it is refused twice. At the model: a heap is <code>Loc → Option Val</code> and a location is a <code>Nat</code>, so a value read out of a cell could no longer be used as an address without a conversion and a proof that it is not negative. And in the arithmetic: every proof about a program that subtracts would carry a side condition ruling out the negative case, which is exactly the bookkeeping truncation removes by giving the bad case an answer. The cost is real — a program computing <code>x - y</code> is not computing what a mathematician means by it — and Unit 37 is where it is paid, on a loop counter running down to zero.'},

    {t:'ex',
     id: 'x40',
     name: 'Evaluating a compound expression',
     why: 'Concreteness, and one surprise met deliberately rather than at the worst moment. Everything from Unit 19 on is stated about arbitrary commands and arbitrary expressions, and it is easy to go a long way without ever having watched <code>Atom.eval</code> produce a number. The second half puts truncated subtraction in front of you now, nineteen units before the loop in Unit 37 where a subtraction that stops at zero is what makes the proof work.',
     setup: 'Two statements, both closed by <code>rfl</code> alone. In the first, the store is <code>Store.set (fun _ => 0) 1 9</code> — the everywhere-zero store with variable <code>1</code> set to <code>9</code>. In the second the store is arbitrary, and the claim holds anyway.',
     goal: 'example : (Atom.plus (.var 0) (.minus (.var 1) (.const 2))).eval (Store.set (fun _ => 0) 1 9) = 7 :=\n  sorry\n\nexample (σ : Store) : (Atom.minus (.const 3) (.const 5)).eval σ = 0 :=',
     hints: [
       'The first tree is <code>plus</code> of two things: the variable <code>0</code>, and <code>minus</code> of the variable <code>1</code> and the constant <code>2</code>. Under that store the variable <code>0</code> holds <code>0</code> and the variable <code>1</code> holds <code>9</code>. The second tree is <code>minus</code> of two constants and mentions no variable at all, which is why the store can be anything.',
       'Both statements are closed arithmetic once evaluation has run: <code>0 + (9 - 2)</code> and <code>3 - 5</code>. Everything in sight is built from constructors, so nothing blocks the computation — there is no theorem to find and no hypothesis to spend.',
       'The word is <code>rfl</code>, twice, in term position — the same word that closed <code>2 + 2 = 4</code> in Unit 01. Nothing is proved <code>by</code> anything, no lemma about <code>Atom.eval</code> is needed, and in the second statement the store is never mentioned.',
       'Put <code>:= rfl</code> at the end of each statement, so that the first reads <code>example : (Atom.plus (.var 0) (.minus (.var 1) (.const 2))).eval (Store.set (fun _ => 0) 1 9) = 7 := rfl</code> and the second is the same move. If the second one surprises you, evaluate <code>3 - 5</code> at the type <code>Nat</code> and read the answer before deciding the exercise is wrong.'
     ],
     sol: 'example : (Atom.plus (.var 0) (.minus (.var 1) (.const 2))).eval (Store.set (fun _ => 0) 1 9) = 7 := rfl\n\nexample (σ : Store) : (Atom.minus (.const 3) (.const 5)).eval σ = 0 := rfl',
     solNote: 'The second statement holds for <b>every</b> store, and the proof does not case on the store or mention it. That is the whole difference between an expression and a command: an expression that contains no variable has one value, and an expression that contains variables has one value per store. Neither has a way to fail.',
     expl: 'Both proofs are reduction and nothing else. The first tree\'s evaluation walks down to <code>σ 0</code> and <code>σ 1</code>, where <code>σ</code> is a concrete function built by <code>Store.set</code> out of a lambda, so both lookups compute; then <code>0 + (9 - 2)</code> computes to <code>7</code>. The second tree contains no variable, so its evaluation reaches <code>3 - 5</code> without ever consulting the store, and at the type <code>Nat</code> that is <code>0</code>.',
     walk: [
       {tac:'(first)  rfl', h:'Reduction unfolds <code>Atom.eval</code> once per node of the tree, five times in all, and <code>Store.set</code> once for each of the two variable lookups. Both of its conditionals are between numerals, so both decide. What is left is <code>0 + (9 - 2) = 7</code>, and that decides too.'},
       {tac:'(second) rfl', h:'Three unfoldings of <code>Atom.eval</code> and no store lookup, leaving <code>3 - 5 = 0</code>. The store variable <code>σ</code> is never touched, which is why it can be a variable without blocking anything: it sits in the argument position of a definition that is being unfolded, not in a position being matched on.'}
     ],
     deep: [
       {t:'trace', title:'The first statement, with the evaluation forced into the open',
        start:'⊢ Atom.eval (Store.set (fun x => 0) 1 9) ((Atom.var 0).plus ((Atom.var 1).minus (Atom.const 2))) = 7',
        steps:[
          {tac:'show 0 + (9 - 2) = 7',
           state:'⊢ 0 + (9 - 2) = 7',
           h:'<code>show</code> restates the goal as something definitionally equal to it, so it succeeds exactly when reduction gets from one to the other — which makes it a way of asking Lean to confirm what the evaluation produced. This line is not in the solution; it is here so that the arithmetic <code>rfl</code> settles is visible.'},
          {tac:'rfl',
           state:'No goals.',
           h:'Closed arithmetic between numerals.'}
        ]},
       {t:'p', h:'Two details in that opening state recur throughout the course. The store prints as <code>fun x => 0</code> although <code>fun _ => 0</code> was written — Lean invents a name for a binder you left anonymous. And the atom prints in dot form, <code>(Atom.var 0).plus …</code>, while the evaluation around it prints in full, <code>Atom.eval σ a</code>: the same rule, applied to two functions whose first explicit argument has different types.'},
       {t:'code', tag:'illustration', cap:'With a variable store, evaluation still runs; it stops at the one point where a lookup cannot be decided, and <code>σ 0</code> is what is left standing.',
        src:'example (σ : Store) : (Atom.plus (.var 0) (.const 2)).eval σ = σ 0 + 2 := rfl'}
     ],
     pitfall: 'Writing the second statement with the answer a mathematician would give. <code>-2</code> cannot even be stated, and the message is about the minus sign rather than about the proof:<br><br><code>error(lean.synthInstanceFailed): failed to synthesize instance of type class<br>&nbsp;&nbsp;Neg Val</code><br><br>There is no negation at <code>Val</code>, so <code>-2</code> is not a term of that type and the statement never gets as far as being false.',
     variants: 'Replace the concrete store in the first statement by a variable <code>σ</code> and the equation becomes <code>σ 0 + (σ 1 - 2) = 7</code>, which is not provable — it is a claim about a store nobody has constrained. Reduction still does everything it can — <code>show σ 0 + (σ 1 - 2) = 7</code> is accepted on that goal — and then two lookups stand where nothing can decide them. The illustration above is the same effect on a smaller tree, where one lookup is left. It is not refutable either, and the reason is that it is true for some stores and false for others: change the <code>9</code> to an <code>8</code> and the same tree evaluates to <code>6</code>, which <code>rfl</code> proves as readily as it proved <code>7</code>.<br><br><code>example : (Atom.plus (.var 0) (.minus (.var 1) (.const 2))).eval (Store.set (fun _ => 0) 1 8) = 6 := rfl</code><br><br>Push the constant the other way and truncation appears inside a compound tree rather than beside one. With <code>.const 20</code> in place of <code>.const 2</code>, the inner <code>minus</code> is <code>9 - 20</code>, which is <code>0</code>, and the whole tree evaluates to <code>0</code> rather than to anything negative:<br><br><code>example : (Atom.plus (.var 0) (.minus (.var 1) (.const 20))).eval (Store.set (fun _ => 0) 1 9) = 0 := rfl</code><br><br>Ask instead for <code>(Atom.var 0).eval σ = 0</code> with <code>σ</code> arbitrary and <code>rfl</code> reports <code>?m.7 = ?m.7</code> against <code>Atom.eval σ (Atom.var 0) = 0</code> — the twin of the failed <code>rfl</code> that §<i>errors</i> catalogues. The left side reduces to <code>σ 0</code> and there it stops, because <code>σ</code> is a variable.'
    },

    /* ======================================== the store is not a resource === */

    {t:'sec', s:'Why the store is not a resource'},

    {t:'txt', cap:'The whole of Module 2 was built on one property of the heap and the store does not have it. Put the two declarations side by side and the property is the <code>Option</code>: both are total functions, and only one has a way of saying <i>nothing here</i>.',
     src:'  Heap  := Loc → Option Val        h l = none   —  I do not hold this cell\n  Store := Var → Val                 σ x = ???    —  there is no such value'},

    {t:'p', h:'Every definition in Module 2 goes through <code>none</code>: disjointness is <i>at every address, one of the two holds nothing</i>, the empty heap holds nothing anywhere, and <code>emp</code> is the assertion that you are looking at it. A store has no <code>none</code>. Every variable has a value, always, so no store owns nothing and two stores cannot divide the variables between them. Writing the definition down is not hard; it does not typecheck.'},

    {t:'code', tag:'sketch', cap:'<code>Heap.disjoint</code>\'s definition with <code>Store</code> for <code>Heap</code>. It is the same text and it is not a proposition.',
     src:'def Store.disjoint (σ₁ σ₂ : Store) : Prop :=\n  ∀ x, σ₁ x = none ∨ σ₂ x = none'},

    {t:'state', cap:'One report per occurrence. <code>Val</code> is <code>Nat</code>, and <code>none</code> is not a number.',
     src:'error: Type mismatch\n  none\nhas type\n  Option ?m.2\nbut is expected to have type\n  Val\n\nerror: Type mismatch\n  none\nhas type\n  Option ?m.3\nbut is expected to have type\n  Val'},

    {t:'note', kind:'key', title:'The consequence, stated now and collected at Unit 24', h:'A command that assigns to a variable changes that variable for <b>everything</b>, including whatever assertion is standing beside it describing memory the command never touches. The heap algebra cannot prevent that, because the store was never divided — there is nothing for the frame to own. So the frame rule cannot be justified by separation alone. It needs a second side condition, about program variables rather than about cells, which is not spatial and gets no help from <code>∗</code>. Unit 24 finds two gaps in the textbook statement of the rule — one read off a goal that will not close, one from a counterexample about a program variable — and this is the second of them.'},

    /* ====================================================== the state === */

    {t:'sec', s:'A state is a store and a heap'},

    {t:'p', h:'The next unit has to say what running a command does, and what it does is relate a <i>before</i> to an <i>after</i>. Two things change, and they change together: an assignment moves the store, a write moves the heap, and a sequence of two commands has to hand the whole result of the first to the second. So the before and after want to be single objects.'},

    {t:'code', cap:'A record with two fields.',
     src:'structure State where\n  store : Store\n  heap  : Heap'},

    {t:'p', h:'A <code>structure</code> is an <code>inductive</code> with exactly one constructor, and the fields are that constructor\'s arguments. Unit 10 built <code>PCM</code> this way; the difference here is that the fields carry data rather than proofs, so a <code>State</code> is something you construct rather than something you discharge obligations to construct. The constructor is <code>State.mk</code>, and because there is only one, the anonymous bracket <code>⟨σ, h⟩</code> means it with nothing to resolve. In the other direction the projections <code>s.store</code> and <code>s.heap</code> take a state apart.'},

    {t:'code', tag:'illustration', cap:'Building, projecting, and putting back together. The last line is the one to look at.',
     src:'#check @State.mk\nexample (σ : Store) (h : Heap) : (State.mk σ h).store = σ := rfl\nexample (s : State) : ⟨s.store, s.heap⟩ = s := rfl'},

    {t:'state', src:'State.mk : Store → Heap → State'},

    {t:'p', h:'The last line holds with no case split, no induction and no hypothesis that <code>s</code> was built by <code>mk</code>: taking a one-constructor value apart and reassembling it gives the value back <i>by reduction</i>, not by a theorem. That is <b>structure eta</b>, and it looks like a curiosity and is not. From Unit 26 on, proofs about a command routinely produce a state written <code>⟨σ, h⟩</code> on one side of an equation and as a variable <code>s</code> on the other; every one of those closes on eta, and without it each would need a case split on <code>s</code> first.'},

    {t:'p', h:'The alternative was to leave the store and the heap as two separate arguments everywhere, which is what assertions do: <code>Assertion</code> is <code>Store → Heap → Prop</code>, and Module 3 never needed a pair. That works for a predicate and fails for a relation. The execution relation has to <i>name</i> the state a command ends in — quantify over it, compare two of them, hand one to the next command — and "the pair of things it ends with" is not a term you can bind unless it is one object. The price is a mismatch at every boundary between the two conventions: an assertion applied to a state is written <code>Q s.store s.heap</code>, and those two projections are visible in most of the definitions from Unit 22 on.'},

    /* ==================================================== conditions === */

    {t:'sec', s:'Conditions the machine can decide'},

    {t:'code', cap:'A guard is not an assertion. An assertion is a proposition: something you prove, possibly at length, possibly not at all. A guard is something the machine looks at and immediately goes one way or the other. Lean has different types for the two — <code>Prop</code> and <code>Bool</code> — so guards get their own inductive type, with an evaluator landing in the second.',
     src:'inductive BExpr where\n  | equals : Atom → Atom → BExpr\n  | not    : BExpr → BExpr\n\ndef BExpr.eval (σ : Store) : BExpr → Bool\n  | .equals a b => a.eval σ == b.eval σ\n  | .not b      => !(b.eval σ)'},

    {t:'p', h:'<code>==</code> takes two numbers and returns <code>true</code> or <code>false</code>, where <code>=</code> would have taken two numbers and returned a proposition; <code>!</code> is boolean negation where <code>¬</code> is the proposition-forming one. Both compute, so <code>#eval</code> on a <code>BExpr.eval</code> prints an answer rather than a proof or a failure.'},

    {t:'cmp',
     left: {t:'What you would write on paper', h:'A conditional whose guard is a proposition — <code>x = 3</code>, or something with a quantifier in it. Perfectly meaningful mathematics, and a perfectly good specification.', src:'inductive PExpr where\n  | holds : (Store → Prop) → PExpr\n\ndef PExpr.eval (σ : Store) : PExpr → Bool\n  | .holds φ => φ σ', tag:'sketch'},
     right:{t:'What a machine needs', h:'The evaluator has to return an answer, and a proposition is not an answer. Lean reports the gap at the one line that tries to cross it:<br><br><code>error: Type mismatch<br>&nbsp;&nbsp;φ σ<br>has type<br>&nbsp;&nbsp;Prop<br>but is expected to have type<br>&nbsp;&nbsp;Bool</code><br><br>Nothing here is a limitation of Lean. A guard the machine cannot settle is a guard the program cannot branch on.'}},

    {t:'p', h:'There is a bridge, and it goes one way only. <code>decide</code> takes a proposition <i>together with evidence that it is decidable</i> — the typeclass argument in square brackets, found by Lean rather than supplied by you, exactly as in Unit 02 — and returns the <code>Bool</code> saying which way it went. A tactic of the same name exists and is used nowhere in this course.'},

    {t:'code', tag:'illustration', src:'#check @decide'},

    {t:'state', cap:'Only <i>some</i> propositions can become guards, and the square brackets are where the restriction lives. That is why <code>BExpr</code> is an inductive type with two constructors rather than a wrapper around <code>Store → Prop</code>; conjunction and comparison would each cost one more constructor, at the price set on the first page of this unit.',
     src:'decide : (p : Prop) → [h : Decidable p] → Bool'},

    {t:'p', h:'One shape can be predicted now, and it appears in every rule about a conditional from Unit 19 onwards. When a proof needs to know that a guard came out true, it will not carry <code>b.eval σ</code> as a hypothesis — it will carry <code>hb : b.eval σ = true</code>, an <i>equation</i> between a <code>Bool</code> and a <code>Bool</code>. If you write the shorter thing, Lean inserts the rest.'},

    {t:'code', tag:'illustration', cap:'Written with the <code>Bool</code> standing where a <code>Prop</code> is wanted, and displayed as Lean recorded it.',
     src:'example (σ : Store) (b : BExpr) (hb : b.eval σ) : b.eval σ = true := by\n  trace_state\n  exact hb'},

    {t:'state', cap:'The hypothesis you wrote as <code>b.eval σ</code> arrives in the context as an equation. The display is <code>BExpr.eval σ b</code> and not <code>b.eval σ</code>, by the same argument-order rule as <code>Atom.eval</code>.',
     src:'σ : Store\nb : BExpr\nhb : BExpr.eval σ b = true\n⊢ BExpr.eval σ b = true'},

    /* ===================================================== commands === */

    {t:'sec', s:'Commands'},

    {t:'anat', cap:'Eight constructors. Three of them touch memory, and all three can be handed an address that holds nothing — which is the reason this course exists.',
     src:'inductive Cmd where\n  | skip\n  | assign : Var → Atom → Cmd\n  | load   : Var → Loc → Cmd\n  | write  : Loc → Atom → Cmd\n  | free   : Loc → Cmd\n  | seq    : Cmd → Cmd → Cmd\n  | ite    : BExpr → Cmd → Cmd → Cmd\n  | loop   : BExpr → Cmd → Cmd',
     parts:[
       {m:'| skip', h:'No arguments: the command that does nothing. It is here because every other construct needs something to put in a branch it does not want, and because the simplest possible rule about commands has to be about some command.'},
       {m:'| assign : Var → Atom → Cmd', h:'Store the value of an expression in a variable. This one cannot fail: the expression always has a value and the variable always exists.'},
       {m:'| load   : Var → Loc → Cmd', h:'Read the cell at an address into a variable. This one <b>can</b> fail — the address may hold nothing — and that possibility is the reason for the rest of the course.'},
       {m:'| write  : Loc → Atom → Cmd', h:'Put the value of an expression into the cell at an address. It fails on the same condition <code>load</code> does: there has to be a cell there already, because this language has no way to make one.'},
       {m:'| free   : Loc → Cmd', h:'Give a cell back. It is what makes failure reachable: no program reads an unallocated cell unless something first unallocated it.'},
       {m:'| seq    : Cmd → Cmd → Cmd', h:'The recursive constructor that every later page uses. <code>ite</code> and <code>loop</code> are recursive too, and no specification reaches either until Units 35 and 36.'},
       {m:'| loop   : BExpr → Cmd → Cmd', h:'While the guard evaluates to <code>true</code>, run the body. Declared here, given execution rules in the next unit, used in a proof about arbitrary commands at Unit 26, and given a rule you could specify a program with at Unit 36.'}
     ]},

    {t:'txt', cap:'Constructors, and the program text each stands for. The right-hand column is not notation this course defines — it is here so the constructor names have something to mean. Only <code>;;</code> exists in Lean.',
     src:'  Cmd.skip                skip\n  Cmd.assign x e          x := e\n  Cmd.load x l            x := [l]            ← read the cell at address l\n  Cmd.write l e           [l] := e            ← write the cell at address l\n  Cmd.free l              free(l)\n  c₁ ;; c₂                c₁ ; c₂\n  Cmd.ite b c₁ c₂         if b then c₁ else c₂\n  Cmd.loop b c            while b do c'},

    {t:'p', h:'Now the decision the rest of the course lives with. <code>load</code>, <code>write</code> and <code>free</code> take a <code>Loc</code> — a literal address, written into the program text — and not an <code>Atom</code>. A program in this language can read address <code>3</code>; it cannot read the address currently held in variable <code>x</code>. What that buys is the tractability of Units 22 to 27. A rule about <code>write l e</code> can say <i>the precondition owns the cell at <code>l</code></i>, with <code>l</code> the same syntactic object in the rule and in the program. Let the address be an expression and the rule has to say <i>the cell at whatever <code>e</code> evaluates to in the current store</i>: every specification acquires a store-dependent address, every use of the frame rule has to prove two such addresses differ, and the non-aliasing Unit 17 got free from disjointness has to be re-derived underneath an evaluation.'},

    {t:'p', h:'What it costs is stated here so that no later unit has to apologise for it. A program that cannot compute an address cannot follow a pointer, and one that cannot follow a pointer cannot walk a linked list. Unit 32 defines an assertion describing a list in memory and Unit 33 one describing a segment of it; both are correct and both are used, and they describe structures that no program written in this <code>Cmd</code> can traverse. What is proved about them is proved about the assertions and about fixed-length fragments of code, never about a loop chasing pointers. Unit 38 states the limitation again beside the one-line syntax change that removes it, and shows that every theorem in the course survives that change, because not one of them inspects how an address was obtained.'},

    {t:'p', h:'The second decision is the two constructors nothing uses yet. <code>ite</code> and <code>loop</code> are in the list from the start and the next unit gives each of them execution rules alongside the other six, but neither gets a rule you could specify a program with until Units 35 and 36. Adding them later would cost the pass over the whole development priced at the top of this page. Declaring them now costs two unused branches in a handful of proofs. The trade is not close.'},

    {t:'code', cap:'One piece of notation, for the one constructor used on every page from here.',
     src:'infixr:60 " ;; " => Cmd.seq'},

    {t:'p', h:'<code>infixr</code> rather than <code>infix</code> means <code>c₁ ;; c₂ ;; c₃</code> parses as <code>c₁ ;; (c₂ ;; c₃)</code>, and the choice is not arbitrary: proofs about a sequence peel one command off the front, so the shape the parser hands them should be <i>first command, then the rest</i>. The precedence <code>60</code> is the number <code>↦</code> was given and five above <code>∗</code>, and it decides nothing here, because no expression in this course contains both a command connective and an assertion connective.'},

    {t:'code', tag:'illustration', cap:'The associativity, proved rather than asserted. Both sides are the same term.',
     src:'example (a b c : Cmd) : a ;; b ;; c = a ;; (b ;; c) := rfl'},

    {t:'p', h:'What does bite is that <b>application binds tighter than any infix notation</b>. Hand a sequence to a three-argument predicate as <code>Triple P c₁ ;; c₂ Q</code> and the parser reads it as <code>Cmd.seq (Triple P c₁) (c₂ Q)</code>, reporting <code>Application type mismatch: The argument Triple P c₁ has type Assertion → Prop but is expected to have type Cmd</code>. That is why every specification from Unit 22 on carries an extra pair of brackets around its command, and the brackets are not decoration.'},

    {t:'note', kind:'warn', title:'A constructor name you cannot have', h:'Declaring an inductive type silently declares several other constants in its namespace — the recursor <code>T.rec</code> among them — and a constructor whose name collides with one of those is refused only when the finished declaration reaches the kernel, so the message carries a <code>(kernel)</code> prefix and is about a declaration you never wrote: <code>(kernel) constant has already been declared \'Cmd8.rec\'</code>. Compiled from <code>inductive Cmd8 where | rec : Cmd8</code>. Nothing else in the constructor lists on this page is at risk, and the keywords that look dangerous are not: <code>| if</code>, <code>| while</code> and <code>| do</code> are all accepted as constructor names, because after <code>|</code> Lean is reading an identifier and not a term.'},

    {t:'note', kind:'warn', title:'Do not <code>open Cmd</code>', h:'<code>Cmd.ite</code> shares its short name with the function that <code>if _ then _ else _</code> abbreviates, which §<i>errors</i> met inside a <code>motive is not type correct</code> message. Inside the namespace the constructor wins: after <code>open Cmd</code>, <code>#check ite</code> answers <code>Cmd.ite : BExpr → Cmd → Cmd → Cmd</code> and the function is no longer reachable by that name. Nothing in this course opens the namespace, and every occurrence is written <code>Cmd.ite</code> or, where the expected type supplies it, <code>.ite</code>.'},

    {t:'p', h:'<code>Atom</code> carries <code>deriving Repr</code> and <code>Cmd</code> does not, so a command cannot be printed — and the repair is not one word, because deriving is structural: to display a <code>Cmd</code> you must be able to display everything it contains, and it contains a <code>BExpr</code>.'},

    {t:'code', tag:'sketch', src:'#eval Cmd.skip'},

    {t:'state', cap:'The first message is that line. The second is what putting <code>deriving Repr</code> on a copy of <code>Cmd</code> reports, and it names where the missing word would have to go first. Nothing in this course prints a command, so it never went there: after this page the syntax is only ever read in goal states.',
     src:'error: could not synthesize a `Repr` or `ToString` instance for type\n  Cmd\n\nerror(lean.synthInstanceFailed): failed to synthesize instance of type class\n  Repr BExpr\n\nHint: Adding the command `deriving instance Repr for BExpr` may allow Lean to derive the missing instance.'},

    /* ================================================== exercise x41 === */

    {t:'p', h:'The last thing to practise is the one genuinely new technique on this page: defining a function by recursion on a type you declared yourself. <code>Atom.eval</code> was handed to you; write one.'},

    {t:'ex',
     id: 'x41',
     name: 'Atom.size',
     why: 'Structural recursion, on your own, before it is load-bearing. Unit 20 is built on induction over a derivation, and induction is structural recursion with propositions in place of numbers — the same shrinking-argument condition, checked the same way. And it puts in front of you what a recursion looks like when Lean accepts it without comment, which is what Unit 19 needs you to have seen: it opens on one Lean refuses.',
     setup: 'Four clauses, one per constructor of <code>Atom</code>, and then one equation about a concrete tree. Count nodes: a leaf is one node, and a node with two subtrees is one more than its two subtrees together. The clause heads are given; the bodies are the exercise.',
     goal: 'def Atom.size : Atom → Nat\n  | .const _ => sorry\n  | .var _ => sorry\n  | .plus a b => sorry\n  | .minus a b => sorry\n\nexample : (Atom.plus (.const 1) (.var 0)).size = 3 :=',
     hints: [
       'The definition has to give a number for every <code>Atom</code>. Two of the four constructors have no <code>Atom</code> inside them, so their clauses are numbers with nothing to compute. The other two have exactly two <code>Atom</code>s inside them, named <code>a</code> and <code>b</code> by the pattern.',
       'The size of a tree is one for the node you are looking at, plus the sizes of whatever hangs below it. For a leaf nothing hangs below, so the answer is <code>1</code>. The equation to be proved says the two-leaf tree <code>plus (const 1) (var 0)</code> has size <code>3</code>, which fixes the convention: both leaves count, and the <code>plus</code> node counts.',
       'The recursive clauses call <code>Atom.size</code> on <code>a</code> and on <code>b</code>. Dot notation reaches it as <code>a.size</code> even while the definition is still being made, because the receiver is the only argument. The equation at the end is closed by <code>rfl</code>, in term position, with no tactic block at all.',
       'The first two clauses are <code>=> 1</code>. The third is <code>| .plus a b => a.size + b.size + 1</code>, and the fourth is the same with <code>minus</code> for <code>plus</code>. Lean accepts the recursion without asking anything, because <code>a</code> and <code>b</code> are components of the argument. Then <code>rfl</code>.'
     ],
     sol: 'def Atom.size : Atom → Nat\n  | .const _ => 1\n  | .var _ => 1\n  | .plus a b => a.size + b.size + 1\n  | .minus a b => a.size + b.size + 1\n\nexample : (Atom.plus (.const 1) (.var 0)).size = 3 := rfl',
     solNote: 'The underscores in the first two clauses are patterns that match anything and bind no name: the size of a constant does not depend on which constant it is. Writing <code>| .const n => 1</code> instead compiles, and earns the warning Unit 05 met on an unused binder — <code>Variable name `n` is not explicitly referenced.</code> — with the repair spelled out under it: remove the binding, or call it <code>_</code>.',
     expl: 'Every clause is determined by one question — <i>what does this constructor contain?</i> — and the two recursive constructors contain two <code>Atom</code>s each, so their clauses call the function being defined on both. Nothing about termination has to be argued: the calls are on <code>a</code> and <code>b</code>, which the pattern obtained by taking the argument apart, so each call is on a strictly smaller tree and Lean\'s structural check passes silently. The final equation is then closed by reduction, because the tree in it is built entirely from constructors.',
     walk: [
       {tac:'| .const _ => 1', h:'A base case. The pattern <code>.const _</code> matches every atom whose head constructor is <code>const</code>, and the underscore discards the number it carries. No recursive call, so nothing about this clause can fail to terminate.'},
       {tac:'| .var _ => 1', h:'The second base case, identical in shape. Two of the four constructors have no <code>Atom</code> among their arguments, and those are exactly the clauses that end the recursion.'},
       {tac:'| .plus a b => a.size + b.size + 1', h:'The pattern binds the two subtrees; the body calls the function on each of them and adds one for the node itself. This is the line the termination check looks at, and what it checks is that <code>a</code> and <code>b</code> came out of the pattern rather than being built by the body.'},
       {tac:'| .minus a b => a.size + b.size + 1', h:'Character for character the third clause with a different head constructor, and that is a fact about the function rather than a copy-paste: counting nodes does not look at what a node <i>means</i>, so <code>plus</code> and <code>minus</code> cannot be told apart by it. <code>Atom.eval</code>, which does look, has different bodies in the same two clauses.'},
       {tac:'example … := rfl', h:'Nothing to arrange: the tree is <code>plus (const 1) (var 0)</code>, three nodes and every one of them a constructor application, so the third clause fires at the root and the first two at the leaves. The goal reduces to <code>1 + 1 + 1 = 3</code>, which is closed arithmetic between numerals, and <code>rfl</code> is the assertion that both sides reduce to the same numeral.'}
     ],
     deep: [
       {t:'trace', title:'The equation, with the recursion forced into the open',
        start:'⊢ ((Atom.const 1).plus (Atom.var 0)).size = 3',
        steps:[
          {tac:'show 1 + 1 + 1 = 3',
           state:'⊢ 1 + 1 + 1 = 3',
           h:'<code>show</code> succeeds exactly when the two statements are definitionally equal, so it is a way of asking Lean to confirm what the three unfoldings of <code>Atom.size</code> produced. One <code>1</code> for each leaf and one for the <code>plus</code> node. This line is not part of the solution.'},
          {tac:'rfl',
           state:'No goals.',
           h:'Closed arithmetic. <code>simp only [Atom.size]</code> would also close the whole goal in one call, without the <code>show</code>, by using the four defining equations as rewrite rules.'}
        ]},
       {t:'p', h:'The definition also computes on trees that are only partly known, for the same reason <code>Atom.eval</code> did: the third clause fires as soon as the scrutinee is headed by <code>plus</code>, whatever its subtrees are.'},
       {t:'code', tag:'illustration', cap:'The defining equation for one constructor, at arbitrary subtrees.',
        src:'example (a b : Atom) : (Atom.plus a b).size = a.size + b.size + 1 := rfl'}
     ],
     pitfall: 'Getting the convention wrong by one and discovering it at the equation rather than at the definition. Counting only the leaves — <code>| .plus a b => a.size + b.size</code> — is a perfectly good function, and the given equation then fails, with <code>rfl</code> reporting the twin metavariables §<i>errors</i> catalogues:<br><br><code>Type mismatch<br>&nbsp;&nbsp;rfl<br>has type<br>&nbsp;&nbsp;?m.9 = ?m.9<br>but is expected to have type<br>&nbsp;&nbsp;((Atom.const 1).plus (Atom.var 0)).leafCount = 3</code><br><br>(The exhibit is named <code>leafCount</code> because the real <code>Atom.size</code> is already in scope alongside it; with your own name in place the last line reads <code>.size = 3</code>.) Nothing in the definition is wrong. The equation is what fixes which of the two functions was wanted, which is why the exercise supplies it.',
     variants: 'Drop the base cases and there is no definition. Lean names the shapes nothing in the clause list covers, by their short constructor names:<br><br><code>Missing cases:<br>(const _)<br>(var _)</code><br><br>Drop only the recursion — <code>| .plus _ _ => 1</code> — and the definition is accepted, terminates trivially, and computes the wrong thing, which is a reminder that the structural check is about termination and not about correctness.<br><br>The equation the exercise supplies constrains two of the four clauses and no more, because the tree in it contains no <code>minus</code>. Write <code>| .minus a b => a.size + b.size</code>, leaving the other three as in the solution, and the definition is wrong and the equation still passes. Pinning all four clauses needs a tree that mentions all four constructors, or four separate equations — one per clause, at arbitrary subtrees, in the shape of the illustration above.<br><br>Try to make the recursive call on something the pattern did not produce — <code>| .plus a b => (Atom.plus a b).size + 1</code>, say — and the shrinking condition fails, because the argument is the same tree the clause was given. That is the failure Unit 19 opens on, in the one place in this course where a natural definition genuinely does not satisfy it.'
    },

    /* ======================================================== close === */

    {t:'dod', h:'You can declare an inductive type whose constructors take values of that type and read its values as trees; define a function on it by pattern matching; say why Lean accepts the recursion with nothing asked of you; and predict when the defining equations reduce and when they do not. You can write <code>.const 3</code>, say what the dot resolves against, and predict which of two functions prints with dot notation. You can read a <code>structure</code> as a one-constructor inductive, build one with <code>⟨σ, h⟩</code>, project out of one, and close <code>⟨s.store, s.heap⟩ = s</code> by reduction. You know that the store is <code>update</code>, that it cannot be divided the way the heap can, and that this will cost the frame rule a second side condition. And you know why a guard is a <code>Bool</code>, what shape a hypothesis about one has, and why three of the eight commands take a literal address.'},

    {t:'p', h:'We have syntax and no meaning. Nothing on this page says what <code>Cmd.write 3 (.const 7)</code> <i>does</i>, and nothing can, because "the command writes to memory" is not yet mathematics. Making it mathematics means choosing what kind of object the semantics is — a function from states to states, or a relation between them — and that choice is not a matter of taste. It decides what "the program crashed" will mean.'}

  ]
});
