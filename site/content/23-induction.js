registerChapter({
  id: 'induction',
  num: '20',
  phase: 'Phase 3 · Programs and their semantics',
  title: 'Structural induction, up to derivations',
  blurb: 'One tactic, met three times on objects of rising difficulty — a number, a list, a derivation — and then the one adjustment that makes it strong enough to prove that a command has at most one final state.',

  orient: {
    youWill: [
      'Prove a statement about every <code>Nat</code> with <code>induction n with | zero | succ n ih</code>, and say what <code>ih</code> is a proof of.',
      'Say what <code>induction n</code> gives you that <code>cases n</code> does not, by reading the goal <code>cases</code> leaves standing.',
      'Run the same tactic on a <code>List</code>, and on a derivation of <code>Exec c s s\'</code> — ten cases, one per rule, each with one induction hypothesis per recursive premise.',
      'Recognise an induction hypothesis that is too weak, from an <code>Application type mismatch</code> that names it, and repair it with <code>generalizing</code>.',
      'Say exactly what <code>generalizing s₂</code> does to the statement being proved.',
      'Move a hypothesis along an equation with <code>▸</code>, and do the same step by hand with <code>have</code> and <code>subst</code>.',
      'Prove <code>exec_deterministic</code>: a command has at most one final state.'
    ],
    needs: [
      'Unit 19: <code>Exec</code> and its ten constructors, derivations as finite trees, and <code>cases h</code> as inversion.',
      'Unit 18: <code>Cmd</code>, <code>State</code>, <code>Store.set</code>, <code>BExpr.eval</code>, <code>;;</code>, and structural recursion.',
      'Unit 02: <code>inductive</code>, constructors, and <code>cases</code> on an equation between constructors.',
      'Ordinary mathematical induction on the natural numbers. That much is assumed; what is new here is everything else.'
    ],
    payoff: '<code>exec_deterministic</code> is the theorem Unit 35 uses to get partial correctness out of total correctness. The <i>technique</i> is worth more than the theorem: the two hardest proofs left in the course — that locality survives a loop, in Unit 26, and the invariant rule, in Unit 36 — are both inductions over a derivation whose hypothesis had to be strengthened before the induction started, and a reader who has not met that failure once will not recognise it there.'
  },

  blocks: [

    /* ================================================== what cases leaves === */

    {t:'p', h:'Reasoning about every derivation at once means this theorem: if <code>c</code> runs from <code>s</code> to <code>s₁</code>, and <code>c</code> also runs from <code>s</code> to <code>s₂</code>, then <code>s₁ = s₂</code>. There is one tool available. <code>cases h₁</code> splits on the last rule of the first derivation — ten branches, of the kind Unit 19 took apart one at a time. Take the branch for a rule that was built out of smaller runs.'},

    {t:'code', tag:'sketch', cap:'The command is fixed as a sequence so that <code>cases</code> has one branch instead of ten. There is no proof under the branch, so Lean reports <code>unsolved goals</code> and prints the goal a second time; the display below is what <code>trace_state</code> printed.',
     src:'example {c₁ c₂ : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec (c₁ ;; c₂) s s₁) (h₂ : Exec (c₁ ;; c₂) s s₂) : s₁ = s₂ := by\n  cases h₁ with\n  | seq hA hB => trace_state'},

    {t:'state', cap:'The position prefix on every quoted message in this unit is dropped, and mid-proof states come from <code>trace_state</code>. Both conventions are stated once, here.',
     src:'case seq\nc₁ c₂ : Cmd\ns s₁ s₂ : State\nh₂ : Exec (c₁ ;; c₂) s s₂\ns\'✝ : State\nhA : Exec c₁ s s\'✝\nhB : Exec c₂ s\'✝ s₁\n⊢ s₁ = s₂'},

    {t:'p', h:'Everything needed is nearly there. <code>h₂</code> is still whole, and inverting it would give a second intermediate state and two more sub-derivations. What would finish the argument is the theorem itself, applied to <code>hA</code> and to <code>hB</code> — smaller derivations than the one you started with. And that is precisely what the context does not contain. <code>cases</code> tells you which rule came last and hands you its premises as raw hypotheses. It does not hand you the theorem about them.'},

    {t:'p', h:'A derivation is a finite tree. Every branch of it terminates in a rule with no derivations among its premises, because that is what building a term of an <code>inductive</code> type means. So a statement about every derivation can be proved the way a statement about every natural number is proved: assume it for the pieces, prove it for the whole. The hypothesis you are allowed to assume is the <b>induction hypothesis</b>, and getting Lean to hand it to you is what the rest of this unit is about.'},

    {t:'p', h:'Lean has one tactic for this, <code>induction</code>, and it works the same way on a number, on a list and on a derivation, because <code>Nat</code>, <code>List</code> and <code>Exec</code> are all declared the same way — a type with a finite list of constructors, some of which take arguments of the type being declared. Meeting the tactic on <code>Exec</code> first would mean meeting new syntax and a ten-case proof together. So: a number, then a list, then a derivation.'},

    /* ======================================================== on a number === */

    {t:'sec', s:'A number'},

    {t:'p', h:'There has to be something to prove about. This function builds a list of <code>n</code> zeros, by recursion on <code>n</code>: nothing at all when <code>n</code> is <code>0</code>, and one more zero on the front of the previous answer otherwise.'},

    {t:'code', src:'def allZeros : Nat → List Nat\n  | 0 => []\n  | n + 1 => 0 :: allZeros n'},

    {t:'p', h:'<code>List Nat</code> is the type of finite lists of naturals, <code>[]</code> is the empty one, and <code>x :: xs</code> is the list with <code>x</code> on the front of <code>xs</code>. Like <code>Nat</code> and like <code>Cmd</code>, <code>List</code> is an <code>inductive</code> with two constructors, one of them recursive; the clauses above are the two of them, in the same pattern-matching style as <code>Atom.eval</code>. <code>xs.length</code> counts the entries.'},

    {t:'p', h:'The claim is that <code>allZeros n</code> has length <code>n</code>. Nobody doubts it. The reason to prove it here is that the proof is four lines and every one of them is new.'},

    {t:'code', src:'theorem allZeros_length (n : Nat) : (allZeros n).length = n := by\n  induction n with\n  | zero => rfl\n  | succ n ih => simp [allZeros, ih]'},

    {t:'anat', src:'  induction n with\n  | zero => rfl\n  | succ n ih => simp [allZeros, ih]',
     parts:[
       {m:'induction n', h:'Names the variable being taken apart. It has to be a variable sitting in the context, not a compound expression; anything else in the context whose type mentions it is carried into the branches with it.'},
       {m:'with', h:'Announces a list of branches, exactly as it does after <code>cases</code>. One branch per constructor of <code>Nat</code>, and Lean checks you supplied all of them: leave one out and it answers <code>Alternative `succ` has not been provided</code>.'},
       {m:'| zero =>', h:'The branch for <code>Nat.zero</code>. It takes no arguments, so there are no names to supply. The goal has <code>0</code> wherever it had <code>n</code>.'},
       {m:'| succ n ih =>', h:'The branch for <code>Nat.succ</code>. It takes one argument — the predecessor — and that argument is recursive, so this branch gets <b>two</b> names: one for the predecessor, one for the induction hypothesis about it. Reusing the letter <code>n</code> for the predecessor is a convention, not a requirement; the original <code>n</code> is gone by now and nothing is being shadowed.'},
       {m:'simp [allZeros, ih]', h:'<code>ih</code> is handed to <code>simp</code> as an equation it may rewrite with, in exactly the way <code>allZeros</code> is handed over as a definition it may unfold. A hypothesis in the context is not used by <code>simp</code> unless it is named.'}
     ]},

    {t:'p', h:'The two branches face these two goals.'},

    {t:'state', cap:'The <code>zero</code> branch. <code>allZeros 0</code> is <code>[]</code> by the first clause of the definition, and <code>[].length</code> is <code>0</code>, so both sides reduce to the same term and <code>rfl</code> closes it.',
     src:'case zero\n⊢ (allZeros 0).length = 0'},

    {t:'state', cap:'The <code>succ</code> branch. <code>ih</code> is the statement of the theorem at <code>n</code>, and the goal is the statement at <code>n + 1</code>.',
     src:'case succ\nn : Nat\nih : (allZeros n).length = n\n⊢ (allZeros (n + 1)).length = n + 1'},

    {t:'p', h:'One <code>simp</code> closes the second branch, which hides where the hypothesis is spent. Split it and the two jobs come apart: unfolding the definition, and then using what was assumed.'},

    {t:'code', tag:'illustration', src:'example (n : Nat) : (allZeros n).length = n := by\n  induction n with\n  | zero => rfl\n  | succ n ih =>\n      simp [allZeros]\n      exact ih'},

    {t:'state', cap:'The goal between the two tactics. <code>allZeros (n + 1)</code> unfolds to <code>0 :: allZeros n</code>, whose length is one more than the length of <code>allZeros n</code>; both sides then carry a <code>+ 1</code> and <code>simp</code> cancels it. What is left is the induction hypothesis, character for character — which is why the one-line version works, <code>ih</code> in the bracket letting <code>simp</code> do this last rewrite itself.',
     src:'case succ\nn : Nat\nih : (allZeros n).length = n\n⊢ (allZeros n).length = n'},

    {t:'p', h:'That residue is the whole point of the tactic, and the fastest way to see it is to ask for less. <code>cases n</code> also splits into <code>zero</code> and <code>succ</code>, and also lets you unfold the definition. It gives you no hypothesis.'},

    {t:'code', tag:'sketch', cap:'Legal, and it does not close.',
     src:'example (n : Nat) : (allZeros n).length = n := by\n  cases n with\n  | zero => rfl\n  | succ n => simp [allZeros]'},

    {t:'state', cap:'The goal Lean is left holding is the induction hypothesis that <code>cases</code> did not supply.',
     src:'error: unsolved goals\ncase succ\nn : Nat\n⊢ (allZeros n).length = n'},

    {t:'note', kind:'key', title:'The difference, in one line',
     h:'<code>cases x</code> gives you one branch per constructor. <code>induction x</code> gives you one branch per constructor <b>and</b>, in each branch, the statement being proved, assumed for every argument of that constructor whose type is the type you are inducting on. Everything else about the two tactics is the same, including the branch syntax and the fact that Lean checks the list of branches is complete.'},

    /* ========================================================== on a list === */

    {t:'sec', s:'A list'},

    {t:'p', h:'Nothing changes at another type except the names of the constructors. A list is built either as <code>[]</code> or as <code>x :: xs</code>, so <code>induction xs with | nil | cons x xs ih</code> is the same tactic with the same two shapes: a base case with no assumptions, and a step case that gets the head, the tail, and the statement about the tail. <code>xs ++ ys</code> is concatenation, and the theorem is that appending nothing changes nothing.'},

    {t:'code', src:'theorem append_nil (xs : List Nat) : xs ++ [] = xs := by\n  induction xs with\n  | nil => rfl\n  | cons x xs ih => simp'},

    {t:'state', cap:'The <code>cons</code> branch. <code>::</code> binds tighter than <code>++</code>, so the left-hand side is <code>(x :: xs) ++ []</code>.',
     src:'case cons\nx : Nat\nxs : List Nat\nih : xs ++ [] = xs\n⊢ x :: xs ++ [] = x :: xs'},

    {t:'p', h:'That <code>simp</code> deserves a second look before you trust any proof of this shape, because it never consults <code>ih</code>. Lean\'s own library contains this equation already, and <code>simp</code> uses it. In fact the induction is not doing any work at all, and one line proves the whole theorem.'},

    {t:'code', tag:'illustration', cap:'No induction, no cases, no hypothesis.',
     src:'example (xs : List Nat) : xs ++ [] = xs := by simp'},

    {t:'p', h:'So <code>append_nil</code> is here for its branch structure and for the warning that comes with it: a proof that closes is not evidence that the argument you had in mind is the argument that ran. When you want to know where a hypothesis was spent, take the automation apart the way the <code>succ</code> branch was taken apart above.'},

    /* ------------------------------------------------------------ x45 ------ */

    {t:'ex',
     id:'x45',
     name:'allZeros_length / append_nil',
     hard:false,
     why:'Two inductions on objects you already understand, so that when the tactic is pointed at a derivation the only new thing is the object. The second one is also the course\'s standing warning about <code>simp</code>: it closes the goal, and it closes it without your hypothesis.',
     setup:'<code>allZeros</code> is given. Both theorems are in the box; the first arrives with a <code>sorry</code> under it so you can start with either, and the editor checks both at once. Each proof is <code>induction</code> with two branches, and no branch is longer than one tactic.',
     goal:'theorem allZeros_length (n : Nat) : (allZeros n).length = n :=\n  sorry\n\ntheorem append_nil (xs : List Nat) : xs ++ [] = xs := by',
     hints:[
       'The first goal says: <code>allZeros n</code> is a list of <code>n</code> copies of <code>0</code>, and <code>.length</code> of it is <code>n</code>. The second says: gluing the empty list onto the right-hand end of <code>xs</code> gives back <code>xs</code>. Neither is a claim about one particular <code>n</code> or one particular <code>xs</code> — each has to hold for all of them at once, and that is the only reason either needs a proof at all.',
       'Induction. In the base case the object is the empty one, both sides reduce to the same thing, and there is nothing to assume. In the step case you have the object one size smaller together with the statement about it, and the goal one size larger; unfold whatever the definition says about the larger object, and what remains should be what you assumed.',
       'The tactic is <code>induction</code>, in the branch form. <code>Nat</code>\'s branches are called <code>zero</code> and <code>succ</code>; <code>List</code>\'s are called <code>nil</code> and <code>cons</code>. The step branch needs one more name than it has constructor arguments — the last name is the induction hypothesis. Closing tactics: <code>rfl</code> in both base cases, <code>simp</code> in both step cases, with the definition and the hypothesis named in the first.',
       'The first proof is <code>induction n with</code> / <code>| zero => rfl</code> / <code>| succ n ih => simp [allZeros, ih]</code>. The second has the same four lines with <code>xs</code>, <code>nil</code> and <code>cons x xs ih</code>, and its step branch needs nothing in the bracket at all.'
     ],
     sol:'theorem allZeros_length (n : Nat) : (allZeros n).length = n := by\n  induction n with\n  | zero => rfl\n  | succ n ih => simp [allZeros, ih]\n\ntheorem append_nil (xs : List Nat) : xs ++ [] = xs := by\n  induction xs with\n  | nil => rfl\n  | cons x xs ih => simp',
     solNote:'The second proof\'s <code>ih</code> is never used, and the branch would compile with the name left out. It is written in because the shape is what you are learning.',
     expl:'Both proofs are the same four lines against different constructor names. What differs is where the work goes: in <code>allZeros_length</code> the <code>simp</code> unfolds one clause of the definition and then rewrites with the hypothesis, and without the hypothesis in the bracket it stops one step short. In <code>append_nil</code> the <code>simp</code> matches a library equation and finishes on its own.',
     walk:[
       {tac:'induction n with', h:'Splits the goal in two, one per constructor of <code>Nat</code>, and generalises nothing else because nothing else in the context mentions <code>n</code>.'},
       {tac:'| zero => rfl', h:'The goal is <code>(allZeros 0).length = 0</code>. <code>allZeros 0</code> reduces to <code>[]</code> by the first clause and <code>[].length</code> reduces to <code>0</code>, so the two sides are the same term and <code>rfl</code> accepts it with no definition named — the reduction is one Lean performs on its own.'},
       {tac:'| succ n ih => simp [allZeros, ih]', h:'The goal is <code>(allZeros (n + 1)).length = n + 1</code> and <code>ih</code> is the same statement at <code>n</code>. <code>allZeros</code> in the bracket lets <code>simp</code> rewrite <code>allZeros (n + 1)</code> to <code>0 :: allZeros n</code>; the length of that is one more than the length of the tail, and cancelling the <code>+ 1</code> on both sides leaves exactly <code>ih</code>, which is in the bracket too.'},
       {tac:'induction xs with', h:'The same split at another type. <code>List Nat</code> has constructors <code>nil</code> and <code>cons</code>, and <code>cons</code> takes two arguments of which the second is a list, so its branch takes three names.'},
       {tac:'| nil => rfl', h:'<code>[] ++ []</code> reduces to <code>[]</code> because concatenation is defined by recursion on its left argument and the first clause returns the right one unchanged.'},
       {tac:'| cons x xs ih => simp', h:'The goal is <code>x :: xs ++ [] = x :: xs</code>. <code>simp</code> pushes the concatenation under the <code>::</code> and then finds the equation <code>xs ++ [] = xs</code> in its own library. <code>ih</code> is in the context and is not consulted.'}
     ],
     deep:[
       {t:'trace', title:'The step branch of allZeros_length, split in two',
        start:'case succ\nn : Nat\nih : (allZeros n).length = n\n⊢ (allZeros (n + 1)).length = n + 1',
        steps:[
          {tac:'simp [allZeros]', state:'case succ\nn : Nat\nih : (allZeros n).length = n\n⊢ (allZeros n).length = n',
           h:'Everything the definition can contribute has been contributed. The goal and the hypothesis are now the same proposition.'},
          {tac:'exact ih', state:'No goals.', h:'The one tactic that had to know what was assumed. Everything before it was unfolding.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The comparison that makes the point about <code>append_nil</code> is the pair of proofs below. Only the first is an induction, and both are accepted.'},
       {t:'cmp',
        left:{t:'What you write', tag:'illustration', h:'Four lines, two branches, one unused hypothesis. The branch structure is real; the work in the step branch is not.', src:'example (xs : List Nat) : xs ++ [] = xs := by\n  induction xs with\n  | nil => rfl\n  | cons x xs ih => simp'},
        right:{t:'What suffices', tag:'illustration', h:'A closed goal is a fact about the goal, not about your proof. Ask where a hypothesis went whenever it matters.', src:'example (xs : List Nat) : xs ++ [] = xs := by simp'}}
     ],
     pitfall:'Leaving the induction hypothesis out of the branch\'s name list — writing <code>| succ n =></code> instead of <code>| succ n ih =></code>. This is not an error. Lean supplies the missing name itself and makes it inaccessible, so the hypothesis is there, is visible in the goal display as <code>a✝</code>, and cannot be typed. The complaint arrives later and elsewhere: <code>simp [allZeros, ih]</code> then fails with <code>Unknown identifier `ih`</code>, or, if you also dropped <code>ih</code> from the bracket, the branch does not close and you are looking at <code>unsolved goals</code> with <code>a✝ : (allZeros n).length = n</code> sitting in plain sight. A branch that leaves a daggered hypothesis behind is a branch whose name list is one short.',
     variants:'Replace <code>induction</code> by <code>cases</code> in the first proof and the base case still closes while the step case leaves <code>⊢ (allZeros n).length = n</code> standing — the induction hypothesis, in the position of an unsolved goal. Drop <code>ih</code> from the bracket, keeping the name, and the same goal is left, this time with <code>ih</code> in the context unused: <code>simp</code> does not read hypotheses it was not given. Drop <code>allZeros</code> from the bracket instead, leaving <code>simp [ih]</code>, and the answer is <code>`simp` made no progress</code>: without the definition there is nothing in the goal for either equation to match. In the second theorem <code>| nil => simp</code> also works, so the choice of <code>rfl</code> there is a statement that the base case needs no rewriting rather than a necessity. And <code>append_nil</code> survives a harder cut: replace its <code>induction xs</code> by <code>cases xs</code>, so that no hypothesis is offered at all, and the proof still compiles unchanged. That is the one-line <code>simp</code> again, seen from inside the branch structure. The reason lies in the mirror statement: <code>[] ++ xs = xs</code> is <code>rfl</code>, with no tactic block and no branches, because <code>++</code> recurses on its <i>left</i> argument and an empty list there is the clause that reduces. An empty list on the right is not, which is the whole of why the two directions cost different amounts. Last, make the first theorem false — claim <code>(allZeros n).length = n + 1</code> — and watch which branch objects: the <code>succ</code> branch still closes, because the step is a valid implication whatever the base case says, and the only complaint is <code>Tactic `rfl` failed</code> under <code>case zero ⊢ (allZeros 0).length = 0 + 1</code>. A step case that compiles is not evidence of anything on its own.'},

    /* ==================================================== on a derivation === */

    {t:'sec', s:'A derivation'},

    {t:'p', h:'<code>Exec</code> was declared with <code>inductive</code>, so it is the same kind of object as <code>Nat</code> and <code>List</code>: ten constructors, and some of them take arguments that are themselves proofs of <code>Exec</code>. Those arguments are what a sub-derivation is. So <code>induction h</code> where <code>h : Exec c s s\'</code> produces ten branches, one per rule, and in each branch you may assume the statement being proved for each premise of that rule that is a derivation.'},

    {t:'tbl', cap:'The premises of each rule, and how many of them are derivations. The last column is the number of induction hypotheses that rule\'s branch receives, which is also how many names the branch takes beyond the ones for its ordinary premises.',
     head:['rule', 'premises', 'induction hypotheses'],
     rows:[
       ['<code>skip</code>', 'none', '0'],
       ['<code>assign</code>', 'none', '0'],
       ['<code>load</code>', '<code>hl</code>, an equation about the heap', '0'],
       ['<code>write</code>', '<code>hl</code>', '0'],
       ['<code>free</code>', '<code>hl</code>', '0'],
       ['<code>seq</code>', 'two derivations', '2'],
       ['<code>iteTrue</code>', 'a guard, one derivation', '1'],
       ['<code>iteFalse</code>', 'a guard, one derivation', '1'],
       ['<code>loopFalse</code>', 'a guard', '0'],
       ['<code>loopTrue</code>', 'a guard, two derivations', '2']
     ]},

    {t:'p', h:'The cheapest way to see all ten at once is to prove something that needs none of them. <code>Exec c s s\' → Exec c s s\'</code> is proved by <code>exact h</code> and there is no reason ever to prove it any other way. Prove it by induction anyway: each branch then has to rebuild its own rule out of the hypotheses that branch was handed, so what appears on the screen is the branch structure with nothing else in it.'},

    {t:'code', src:'theorem exec_id {c : Cmd} {s s\' : State} (h : Exec c s s\') : Exec c s s\' := by\n  induction h with\n  | skip => exact .skip\n  | assign => exact .assign\n  | load hl => exact .load hl\n  | write hl => exact .write hl\n  | free hl => exact .free hl\n  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂\n  | iteTrue hb _ ih => exact .iteTrue hb ih\n  | iteFalse hb _ ih => exact .iteFalse hb ih\n  | loopFalse hb => exact .loopFalse hb\n  | loopTrue hb _ _ ihb ihr => exact .loopTrue hb ihb ihr'},

    {t:'p', h:'The underscores are the derivations themselves, which this proof does not need — only the hypotheses about them. Look at what three of the branches contain.'},

    {t:'state', cap:'<code>seq</code>. Two premises, two hypotheses, and they say the same thing as the premises.',
     src:'case seq\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nih₁ : Exec c₁✝ s✝ s\'✝\nih₂ : Exec c₂✝ s\'✝ s\'\'✝\n⊢ Exec (c₁✝ ;; c₂✝) s✝ s\'\'✝'},

    {t:'state', cap:'<code>iteTrue</code>. One derivation among the premises, so one hypothesis — and it has the same type as the premise, which is why Lean prints the two names on one line.',
     src:'case iteTrue\nc : Cmd\ns s\' s✝ s\'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ ih : Exec c₁✝ s✝ s\'✝\n⊢ Exec (Cmd.ite b✝ c₁✝ c₂✝) s✝ s\'✝'},

    {t:'state', cap:'<code>loopFalse</code>. A guard and nothing else, so no hypothesis at all: this rule has no derivation among its premises, and a branch cannot assume something about a sub-derivation that does not exist.',
     src:'case loopFalse\nc : Cmd\ns s\' s✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = false\n⊢ Exec (Cmd.loop b✝ c✝) s✝ s✝'},

    {t:'p', h:'Two things in those displays need a word. First, <code>c</code>, <code>s</code> and <code>s\'</code> — the variables the theorem was stated with — are still in the context and appear nowhere in the goal. <code>induction h</code> takes apart a proof whose type mentions all three, so all three are replaced by fresh variables in every branch, and the originals are left behind with nothing depending on them. Second, those fresh variables are daggered. They come from the constructor\'s own implicit binders, which the branch name list does not reach, so Lean names them and marks the names as not yours to type.'},

    {t:'p', h:'The proof itself proves nothing, and that is deliberate. Its value is the ten goal states. Four of them carry hypotheses, and each such hypothesis says the same thing in different letters: <i>you may assume the theorem for the pieces.</i> The other six carry none, because their rule has no pieces. Read the hypotheses, not the tactics.'},

    /* ------------------------------------------------------------ x46 ------ */

    {t:'ex',
     id:'x46',
     name:'exec_id',
     hard:false,
     why:'This is the only place in the course where you get to look at all ten branches of an induction on a derivation with nothing else in the goal to distract you. The next proof has ten branches too, and each of them is doing something; if the branch structure is unfamiliar when you get there, both will be new at once.',
     setup:'Prove <code>Exec c s s\' → Exec c s s\'</code> — by <code>induction h with</code>, not by <code>exact h</code>. The point is the goals, not the proof. Each branch rebuilds its own rule from what that branch was handed: the guard and the heap equations come through as premises, the sub-derivations come through as induction hypotheses. Use <code>_</code> for the sub-derivations you do not need, and remember that <code>.skip</code> is short for <code>Exec.skip</code> when the expected type says which namespace to look in.',
     goal:'theorem exec_id {c : Cmd} {s s\' : State} (h : Exec c s s\') : Exec c s s\' := by',
     hints:[
       'The goal in each branch is the conclusion of one rule, at the variables that rule binds. What you are given is that rule\'s premises, plus — for each premise that is itself a derivation — a proof of the goal for that premise.',
       'Ten cases, one per rule. In each, apply the same rule again. Non-derivation premises (the heap equation in <code>load</code>, <code>write</code> and <code>free</code>; the guard in the four conditional rules) are passed straight through. Derivation premises are supplied from the induction hypotheses rather than from the premises themselves, which is what makes this an induction instead of a copy.',
       'The tactic is <code>induction h with</code>, then one <code>| ctor ... => exact ...</code> line per constructor. The constructor names are the ten from Unit 19. Each branch names one identifier per <b>explicit</b> argument of its rule; write <code>_</code> for any you do not use, and add one further name per sub-derivation for the hypothesis about it.',
       'The first three branches are <code>| skip => exact .skip</code>, <code>| assign => exact .assign</code> and <code>| load hl => exact .load hl</code>. <code>seq</code> has two explicit arguments and two hypotheses, so it is <code>| seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂</code>. Leave out a branch and Lean tells you which one: <code>Alternative `write` has not been provided</code>.'
     ],
     sol:'theorem exec_id {c : Cmd} {s s\' : State} (h : Exec c s s\') : Exec c s s\' := by\n  induction h with\n  | skip => exact .skip\n  | assign => exact .assign\n  | load hl => exact .load hl\n  | write hl => exact .write hl\n  | free hl => exact .free hl\n  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂\n  | iteTrue hb _ ih => exact .iteTrue hb ih\n  | iteFalse hb _ ih => exact .iteFalse hb ih\n  | loopFalse hb => exact .loopFalse hb\n  | loopTrue hb _ _ ihb ihr => exact .loopTrue hb ihb ihr',
     solNote:'Name the premises instead of discarding them — <code>| seq h₁ h₂ ih₁ ih₂ => exact .seq h₁ h₂</code> — and the proof still compiles, because for this statement the premises and the hypotheses have the same type. That is true here and nowhere else in the course. In the next exercise they differ, and only the hypotheses will do.',
     expl:'Nothing is proved and nothing is meant to be. What the branches display is the anatomy of an induction on a derivation: the number of names each takes, which of them are premises and which are hypotheses, and the fact that a rule with no sub-derivation gets no hypothesis. The rules divide by that count into six with no hypothesis, two with one, and two with two. The next proof divides them differently — by what a rule\'s conclusion determines rather than by how the rule was built — and the two divisions cross. <code>load</code> and <code>loopFalse</code> have no induction hypothesis at all, which is what makes them among the cheapest branches here. In <code>exec_deterministic</code> neither is cheap: <code>load</code> has two heap lookups to reconcile, <code>loopFalse</code> has a rival rule to refute, and having nothing to assume is no help with either.',
     walk:[
       {tac:'induction h with', h:'Ten goals. Every index of <code>h</code> — the command and both states — is replaced in each branch by the variables that branch\'s constructor binds, which is why the goal in each branch mentions daggered names and not <code>c</code>, <code>s</code>, <code>s\'</code>.'},
       {tac:'| skip => exact .skip', h:'The branch has nothing in it: <code>Exec.skip</code> takes no explicit argument and its conclusion has the same state twice, so the goal is <code>Exec Cmd.skip s✝ s✝</code> and the constructor is already a proof of it.'},
       {tac:'| assign => exact .assign', h:'No name either, and this time the goal has a compound final state: <code>Exec (Cmd.assign x✝ e✝) s✝ { store := s✝.store.set x✝ (Atom.eval s✝.store e✝), heap := s✝.heap }</code>. Nothing has to be matched up by hand, because that state is written exactly as <code>Exec.assign</code>\'s conclusion writes it.'},
       {tac:'| load hl => exact .load hl', h:'One explicit argument, the heap equation, so one name. Its type is <code>s✝.heap l✝ = some v✝</code>, and handing it back to <code>Exec.load</code> rebuilds the rule at the same three implicit arguments Lean already fixed.'},
       {tac:'| write hl => exact .write hl', h:'One name again, but for a premise that does a different job. <code>hl : s✝.heap l✝ = some old✝</code> certifies only that the address is allocated; <code>old✝</code> appears nowhere in the goal, which stores the value of an expression instead. The branch is still a hand-back, and <code>free</code> is the same once more — its premise names a value and its conclusion erases the address without keeping one.'},
       {tac:'| seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂', h:'Four names for two explicit arguments: the two premises, discarded, and then the two induction hypotheses. The order is fixed: all of the constructor\'s own arguments first, then the hypotheses, in the same order as the arguments they belong to.'},
       {tac:'| iteTrue hb _ ih => exact .iteTrue hb ih', h:'The guard is kept because <code>Exec.iteTrue</code> needs it; the sub-derivation is discarded and the hypothesis about it is used in its place.'},
       {tac:'| iteFalse hb _ ih => exact .iteFalse hb ih', h:'The mirror, at the second command. Two rules conclude a run of an <code>ite</code>, and <code>induction</code> gives each of them a branch of its own, so the guard equation here reads <code>= false</code> and the hypothesis is about <code>c₂✝</code> rather than <code>c₁✝</code>.'},
       {tac:'| loopFalse hb => exact .loopFalse hb', h:'One name and no hypothesis. The goal is <code>Exec (Cmd.loop b✝ c✝) s✝ s✝</code> — a run of the loop that ends where it started — and the rule handed the guard concludes exactly that, which is how a branch with nothing assumed still closes.'},
       {tac:'| loopTrue hb _ _ ihb ihr => exact .loopTrue hb ihb ihr', h:'The widest branch: one guard, two sub-derivations, two hypotheses. <code>ihr</code> is the hypothesis about the rest of the loop, which is a derivation of the very same command <code>loop b c</code> — smaller as a derivation, identical as a command. That is why induction on the derivation works where induction on the command could not.'}
     ],
     deep:[
       {t:'trace', title:'The seq branch',
        start:'case seq\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nih₁ : Exec c₁✝ s✝ s\'✝\nih₂ : Exec c₂✝ s\'✝ s\'\'✝\n⊢ Exec (c₁✝ ;; c₂✝) s✝ s\'\'✝',
        steps:[
          {tac:'exact .seq ih₁ ih₂', state:'No goals.',
           h:'<code>h₁✝</code> and <code>ih₁</code> have the same type, and so do <code>h₂✝</code> and <code>ih₂</code>, because the statement being proved is the identity. The moment the statement is anything else the two columns come apart, and only the hypotheses are usable.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Two of the ten branches receive two hypotheses. Here is the other one.'},
       {t:'state', cap:'Five names, of which two are hypotheses. <code>ihr</code> is an assumption about a derivation of <code>Cmd.loop b✝ c✝</code> — the same command the goal is about. Nothing got smaller except the derivation, and that is enough.',
        src:'case loopTrue\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nhbody✝ : Exec c✝ s✝ s\'✝\nhrest✝ : Exec (Cmd.loop b✝ c✝) s\'✝ s\'\'✝\nihb : Exec c✝ s✝ s\'✝\nihr : Exec (Cmd.loop b✝ c✝) s\'✝ s\'\'✝\n⊢ Exec (Cmd.loop b✝ c✝) s✝ s\'\'✝'},
       {t:'p', h:'Leaving a branch out is the mistake this proof makes easiest, and Lean reports it once per missing rule.'},
       {t:'state', cap:'What <code>induction h with</code> answers when only the <code>skip</code> branch is supplied.',
        src:'error: Alternative `assign` has not been provided\nerror: Alternative `load` has not been provided\nerror: Alternative `write` has not been provided\nerror: Alternative `free` has not been provided\nerror: Alternative `seq` has not been provided\nerror: Alternative `iteTrue` has not been provided\nerror: Alternative `iteFalse` has not been provided\nerror: Alternative `loopFalse` has not been provided\nerror: Alternative `loopTrue` has not been provided'}
     ],
     pitfall:'Counting the names wrong on <code>seq</code> and <code>loopTrue</code>. The rule for the list is: one name per <b>explicit</b> constructor argument, in order, and then one name per argument that was a derivation, in the same order. <code>Exec.seq</code> has two explicit arguments, both derivations, so the list is four long; <code>Exec.loopTrue</code> has three explicit arguments of which two are derivations, so its list is five long. Supply too many and Lean says <code>Too many variable names provided at alternative `seq`</code> with both counts. Supply too few and it says nothing: the names you did not write are created inaccessible, and you discover it when <code>ih₂</code> is reported unknown.',
     variants:'Replace the whole proof by <code>exact h</code> and it compiles, which is the honest way to prove this statement. Replace <code>induction h</code> by <code>cases h</code> and it also compiles, with the same ten branch names and two fewer names in each of <code>seq</code> and <code>loopTrue</code>: the premises are still there, the hypotheses are gone. Run both and put the two <code>seq</code> goals side by side. They differ in two ways. <code>cases</code> leaves the theorem\'s own <code>s</code> and <code>s\'</code> standing in the goal, where <code>induction</code> replaced every index by a fresh daggered variable and left <code>c</code>, <code>s</code> and <code>s\'</code> behind unused. And <code>cases</code> has no <code>ih₁</code> and no <code>ih₂</code>: two lines of context, and they are the entire subject of this unit. Supply one name too many, <code>| seq _ _ ih₁ ih₂ ih₃ =></code>, and Lean counts for you: <code>Too many variable names provided at alternative `seq`: 5 provided, but 4 expected</code>.'},

    /* ==================================================== the real theorem === */

    {t:'sec', s:'Determinism'},

    {t:'p', h:'Back to the theorem this unit opened with, now with a tactic that hands over the hypothesis the opening was missing. Two derivations, both from <code>c</code> and <code>s</code>; induct on the first; in each branch, invert the second and show the two end states agree. The branch structure is <code>exec_id</code>\'s, and the ten branches fall into three shapes.'},

    {t:'steps', title:'The three shapes of a branch',
     items:[
       {k:'The rule fixes its own answer', h:'<code>skip</code>, <code>assign</code>, <code>write</code>, <code>free</code>. The conclusion of each of these rules determines the final state from the initial state and the command alone. Inverting <code>h₂</code> leaves one branch, whose end state is written the same way, so the goal becomes an identity: <code>cases h₂; rfl</code>.'},
       {k:'The rule carries a value out of the heap', h:'<code>load</code>. The final state mentions <code>v</code>, and <code>v</code> came from the premise <code>hl : s.heap l = some v</code>. Inverting <code>h₂</code> produces a second value <code>v\'</code> with its own premise at the same address. Two equations with the same left-hand side give <code>some v = some v\'</code>, and constructor injectivity finishes it.'},
       {k:'The rule is compositional, or has a rival', h:'<code>seq</code>, <code>iteTrue</code>, <code>iteFalse</code>, <code>loopFalse</code>, <code>loopTrue</code>. Two things happen in this group, sometimes both at once. Where the rule was built from smaller runs, the induction hypotheses are what identify the states those runs passed through. And where two rules conclude runs of the same command — which is the case for <code>ite</code> and for <code>loop</code> — inverting <code>h₂</code> leaves more than one branch, and the branch in which the two derivations disagree about the guard is impossible. Killing it is a separate small move.'}
     ]},

    {t:'p', h:'Write it the direct way first, with no adjustment to the tactic. The proof below is the finished one with two words missing.'},

    {t:'code', tag:'sketch', cap:'Eight of the ten branches close. Two do not, and they are the two whose rule has a sub-run through an intermediate state the rule itself invents.',
     src:'example {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by\n  induction h₁ with\n  | skip => cases h₂; rfl\n  | assign => cases h₂; rfl\n  | load hl => cases h₂ with | load hl\' => rw [hl] at hl\'; cases hl\'; rfl\n  | write hl => cases h₂ with | write hl\' => rfl\n  | free hl => cases h₂ with | free hl\' => rfl\n  | seq _ _ ih₁ ih₂ =>\n      cases h₂ with\n      | seq h₁\' h₂\' => exact ih₂ (ih₁ h₁\' ▸ h₂\')\n  | iteTrue hb _ ih =>\n      cases h₂ with\n      | iteTrue hb\' h\' => exact ih h\'\n      | iteFalse hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | iteFalse hb _ ih =>\n      cases h₂ with\n      | iteTrue hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | iteFalse hb\' h\' => exact ih h\'\n  | loopFalse hb =>\n      cases h₂ with\n      | loopFalse hb\' => rfl\n      | loopTrue hb\' _ _ => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | loopTrue hb _ _ ihb ihr =>\n      cases h₂ with\n      | loopFalse hb\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | loopTrue hb\' hbody\' hrest\' => exact ihr (ihb hbody\' ▸ hrest\')'},

    {t:'state', cap:'The first of four. The second is the knock-on complaint about <code>h₂\'</code> in the same branch; <code>loopTrue</code> reports the same pair in different letters, about <code>ihb</code> and <code>hrest\'</code>.',
     src:'error: Application type mismatch: The argument\n  h₁\'\nhas type\n  Exec c₁✝ s✝ s\'✝\nbut is expected to have type\n  Exec c₁✝ s✝ s₂\nin the application\n  ih₁ h₁\''},

    {t:'p', h:'The argument named is an induction hypothesis, and that is the diagnosis. <code>ih₁</code> wants a derivation ending in <code>s₂</code> — the one particular final state named in the theorem\'s statement — and what is available is a derivation ending in the intermediate state that inverting <code>h₂</code> produced. There is no repair inside the branch. The hypothesis is the wrong statement, and it was made the wrong statement before the branch existed.'},

    {t:'p', h:'Everything in the context when <code>induction</code> runs that the tactic does not move is held fixed while it runs. <code>s₂</code> was introduced by the theorem\'s binders, is not an index of <code>h₁</code>, and so stays where it is; each induction hypothesis is therefore a claim about that <code>s₂</code> and no other. In the <code>seq</code> branch the state you have to identify is not that one. Eight branches never needed a second state and never noticed.'},

    {t:'p', h:'<code>generalizing</code> is the repair. Naming <code>s₂</code> after the derivation moves <code>s₂</code> — and <code>h₂</code>, which mentions it — out of the context and back into the statement being proved, so the induction runs on a <code>∀ s₂</code> claim; each branch then re-introduces them locally, and each induction hypothesis begins with <code>∀ {s₂ : State}</code> and can be used at whatever state the branch turns out to need.'},

    {t:'code', tag:'sketch', cap:'The only change to the proof above.',
     src:'  induction h₁ generalizing s₂ with'},

    {t:'cmp',
     left:{t:'Without <code>generalizing s₂</code>', kind:'bad',
       h:[{t:'p', h:'<code>ih₁</code> speaks about the <code>s₂</code> fixed by the statement. Inverting <code>h₂</code> produces a different intermediate state, and there is nothing to apply <code>ih₁</code> to.'},
          {t:'state', src:'ih₁ : Exec c₁✝ s✝ s₂ → s\'✝¹ = s₂\nih₂ : Exec c₂✝ s\'✝¹ s₂ → s\'\'✝ = s₂'}]},
     right:{t:'With <code>generalizing s₂</code>', kind:'good',
       h:[{t:'p', h:'Each hypothesis takes the final state as an argument. <code>ih₁</code> can now be applied at the intermediate state, which is what the branch needs.'},
          {t:'state', src:'ih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝¹ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s\'✝¹ s₂ → s\'\'✝ = s₂'}]}},

    {t:'detail', title:'Both <code>seq</code> contexts in full', open:false, blocks:[
      {t:'p', h:'The two lines in each column of the comparison above are extracted from these. Both are the state after <code>cases h₂ with | seq h₁\' h₂\' =></code>, and they differ in nothing else.'},
      {t:'state', cap:'Without <code>generalizing</code>. <code>s₂</code> sits among the theorem\'s own variables at the top, where it was introduced, and has been there since before the induction.',
       src:'case seq.seq\nc : Cmd\ns s₁ s₂ s✝ s\'✝¹ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝¹\nh₂✝ : Exec c₂✝ s\'✝¹ s\'\'✝\nih₁ : Exec c₁✝ s✝ s₂ → s\'✝¹ = s₂\nih₂ : Exec c₂✝ s\'✝¹ s₂ → s\'\'✝ = s₂\ns\'✝ : State\nh₁\' : Exec c₁✝ s✝ s\'✝\nh₂\' : Exec c₂✝ s\'✝ s₂\n⊢ s\'\'✝ = s₂'},
      {t:'state', cap:'With <code>generalizing</code>. <code>s₂</code> has moved down: it is now introduced inside the branch, after the hypotheses, alongside the fresh state that inverting <code>h₂</code> produced. That change of position is the whole of what the word did.',
       src:'case seq.seq\nc : Cmd\ns s₁ s✝ s\'✝¹ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝¹\nh₂✝ : Exec c₂✝ s\'✝¹ s\'\'✝\nih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝¹ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s\'✝¹ s₂ → s\'\'✝ = s₂\ns₂ s\'✝ : State\nh₁\' : Exec c₁✝ s✝ s\'✝\nh₂\' : Exec c₂✝ s\'✝ s₂\n⊢ s\'\'✝ = s₂'},
      {t:'p', h:'There are two intermediate states in both displays — <code>s\'✝¹</code> from the derivation being inducted on, and <code>s\'✝</code> from the one inverted a line earlier — and nothing yet says they are equal. Proving they are equal is what <code>ih₁</code> is for, and it is the only step in the branch that needs the generalisation.'}
    ]},

    {t:'note', kind:'key', title:'What <code>generalizing x</code> does',
     h:'It puts <code>x</code>, and every hypothesis whose type mentions <code>x</code>, back into the goal before the induction starts, and re-introduces them at the top of every branch. The effect on each induction hypothesis is to prefix it with a binder for <code>x</code> — implicit here, printing as <code>∀ {s₂ : State}</code>, because <code>s₂</code> was declared as an implicit argument of the theorem. Reach for it when the hypothesis has to be used at a value of something other than the thing you are inducting on. You cannot name an index of the derivation itself: <code>generalizing s</code> here answers <code>Variable `s` cannot be generalized because the induction target depends on it</code>, and it is unnecessary anyway, since <code>induction</code> already generalises the indices.'},

    {t:'p', h:'The tactic is a convenience, not the only route. Anything still in the goal when <code>induction</code> runs is in every induction hypothesis already, so a statement written with the quantifier in it and never introduced needs no <code>generalizing</code> at all. That is the form the two loop proofs later in the course take, and it is worth seeing once, because it is the reason the word to reach for is <i>strengthen the statement</i> rather than <i>add a keyword</i>.'},

    {t:'detail', title:'The same proof with the quantifier in the statement', open:false, blocks:[
      {t:'p', h:'Move <code>s₂</code> and <code>h₂</code> out of the binders and into the goal, and induct on <code>h₁</code> with neither of them introduced. The ten branches are the ones above; each opens with the <code>intro</code> that <code>generalizing</code> was performing for you.'},
      {t:'code', tag:'illustration',
       src:'example {c : Cmd} {s s₁ : State} (h₁ : Exec c s s₁) :\n    ∀ {s₂ : State}, Exec c s s₂ → s₁ = s₂ := by\n  induction h₁ with\n  | skip => intro s₂ h₂; cases h₂; rfl\n  | assign => intro s₂ h₂; cases h₂; rfl\n  | load hl => intro s₂ h₂; cases h₂ with | load hl\' => rw [hl] at hl\'; cases hl\'; rfl\n  | write hl => intro s₂ h₂; cases h₂ with | write hl\' => rfl\n  | free hl => intro s₂ h₂; cases h₂ with | free hl\' => rfl\n  | seq _ _ ih₁ ih₂ =>\n      intro s₂ h₂\n      cases h₂ with\n      | seq h₁\' h₂\' => exact ih₂ (ih₁ h₁\' ▸ h₂\')\n  | iteTrue hb _ ih =>\n      intro s₂ h₂\n      cases h₂ with\n      | iteTrue hb\' h\' => exact ih h\'\n      | iteFalse hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | iteFalse hb _ ih =>\n      intro s₂ h₂\n      cases h₂ with\n      | iteTrue hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | iteFalse hb\' h\' => exact ih h\'\n  | loopFalse hb =>\n      intro s₂ h₂\n      cases h₂ with\n      | loopFalse hb\' => rfl\n      | loopTrue hb\' _ _ => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | loopTrue hb _ _ ihb ihr =>\n      intro s₂ h₂\n      cases h₂ with\n      | loopFalse hb\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | loopTrue hb\' hbody\' hrest\' => exact ihr (ihb hbody\' ▸ hrest\')'},
      {t:'p', h:'Ten <code>intro</code>s bought nothing here, which is why the corpus proof uses the tactic. The trade turns the other way as soon as what has to stay in the goal is not a variable you could have named — an equation, say, that each branch is supposed to refute. Then there is nothing for <code>generalizing</code> to take, and the statement has to carry it.'}
    ]},

    {t:'p', h:'One line in the finished proof is still unexplained. In the <code>seq</code> branch, <code>ih₁ h₁\'</code> proves that the two intermediate states are equal, and <code>h₂\'</code> is a derivation starting from one of them while <code>ih₂</code> expects one starting from the other. <code>▸</code> is what carries a term across an equation: <code>e ▸ t</code> is <code>t</code> with the equation <code>e</code> applied to its type, in whichever direction makes the result fit where it is being put. Delete it and Lean says exactly what is wrong: <code>h₂\'</code> <i>has type</i> <code>Exec c₂✝ s\'✝ s₂</code> <i>but is expected to have type</i> <code>Exec c₂✝ s\'✝¹ s₂</code>.'},

    {t:'p', h:'The same step written out takes two lines and no new notation. Name the equation, then substitute it away.'},

    {t:'code', tag:'sketch', cap:'One branch, lifted out; on its own it is not a proof of anything. Put it in place of the old <code>seq</code> branch and the proof compiles unchanged.',
     src:'      | seq h₁\' h₂\' =>\n          have hmid := ih₁ h₁\'\n          subst hmid\n          exact ih₂ h₂\''},

    {t:'p', h:'<code>subst hmid</code> eliminates one of the two intermediate states everywhere at once, including inside <code>h₂\'</code>, which is why <code>ih₂ h₂\'</code> then typechecks unaided. Use this form when the equation is needed in more than one place, or when <code>▸</code> guesses the direction you did not want — it has to choose one, and the only information it has is the type it is being asked to produce.'},

    /* ------------------------------------------------------------ m5-2 ----- */

    {t:'ex',
     id:'m5-2',
     name:'exec_deterministic',
     hard:true,
     why:'A command has at most one final state. The theorem is used in Unit 35, where it is what lets partial correctness be derived from total correctness rather than proved separately. The proof is the first induction on a derivation that does something, and the obstacle it runs into decides the two hardest proofs left in the course — that locality survives a loop, in Unit 26, and the invariant rule, in Unit 36. Both of those are inductions over a derivation in which the hypothesis has to be used at something the statement did not fix, and both strengthen it before the induction starts. They do it by a different device, for the reason you are about to meet here.',
     setup:'Ten branches. Five of them are one line. The other five open a nested <code>cases</code> and run to three or four — four wherever two rules could have concluded a run of the same command, so that the inversion leaves two alternatives instead of one. Two branches of the ten need an induction hypothesis applied at a state the goal does not mention. Write it without <code>generalizing</code> first if you want to see the failure, then add it — the rest of the proof does not change. Everything else here you have: <code>cases</code> in the branch form, <code>rw ... at</code>, <code>absurd</code>, and <code>cases</code> on an equation between two <code>some</code>s.',
     goal:'theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by',
     hints:[
       'You are given two derivations of the same command from the same starting state, ending in <code>s₁</code> and <code>s₂</code>, and asked to prove those two states equal. Neither derivation is distinguished by the statement; you get to choose which one to take apart.',
       'Induct on one derivation and invert the other in every branch. In each branch the two derivations end with rules that conclude runs of the same command, so either the rules agree — and then you compare what they produce — or they are the <code>true</code> and <code>false</code> versions of the same guard, and the branch is refuted by the guard. Where a rule was built from a smaller run, the induction hypothesis about that run is what identifies the states it passed through.',
       'The outer tactic is <code>induction h₁ generalizing s₂ with</code>; the inner one, in every branch, is <code>cases h₂</code>, plain where one rule survives and in the <code>with | ctor ... =></code> form where you need a name out of it. A guard clash is closed by rewriting one guard equation into the other and then <code>absurd</code>. Two <code>some</code>s with the same left-hand side are reconciled by <code>rw ... at</code> and then <code>cases</code>.',
       'The proof opens <code>induction h₁ generalizing s₂ with</code>, and the first branch is <code>| skip => cases h₂; rfl</code>. That is the whole pattern for <code>assign</code> too, and <code>write</code> and <code>free</code> differ only in naming the surviving branch. The <code>seq</code> branch ends <code>exact ih₂ (ih₁ h₁\' ▸ h₂\')</code>, and <code>loopTrue</code> ends with the same line in different letters.'
     ],
     sol:'theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by\n  induction h₁ generalizing s₂ with\n  | skip => cases h₂; rfl\n  | assign => cases h₂; rfl\n  | load hl => cases h₂ with | load hl\' => rw [hl] at hl\'; cases hl\'; rfl\n  | write hl => cases h₂ with | write hl\' => rfl\n  | free hl => cases h₂ with | free hl\' => rfl\n  | seq _ _ ih₁ ih₂ =>\n      cases h₂ with\n      | seq h₁\' h₂\' => exact ih₂ (ih₁ h₁\' ▸ h₂\')\n  | iteTrue hb _ ih =>\n      cases h₂ with\n      | iteTrue hb\' h\' => exact ih h\'\n      | iteFalse hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | iteFalse hb _ ih =>\n      cases h₂ with\n      | iteTrue hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | iteFalse hb\' h\' => exact ih h\'\n  | loopFalse hb =>\n      cases h₂ with\n      | loopFalse hb\' => rfl\n      | loopTrue hb\' _ _ => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | loopTrue hb _ _ ihb ihr =>\n      cases h₂ with\n      | loopFalse hb\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | loopTrue hb\' hbody\' hrest\' => exact ihr (ihb hbody\' ▸ hrest\')',
     solNote:'Twenty-seven lines, and only two of them — the <code>seq</code> and <code>loopTrue</code> endings — depend on <code>generalizing</code>. If you have climbed all four hints and the <code>seq</code> branch is still not going in, open this and read those two lines against the goal state in the trace below; that is where the whole proof is.',
     expl:'The induction supplies, in each branch, the theorem for every sub-run of the rule that concluded <code>h₁</code>. Inverting <code>h₂</code> in that branch enumerates the rules that could have concluded a run of the same command. Where the two rules agree the states are compared, using the hypotheses where the rule had sub-runs; where they disagree they disagree about a guard, and the guard is a <code>Bool</code>, so <code>true = false</code> ends it. The one subtlety is the intermediate state, which each derivation chooses for itself, and which the hypotheses identify.',
     walk:[
       {tac:'induction h₁ generalizing s₂ with', h:'Ten goals, and in each of them <code>s₂</code> and <code>h₂</code> have been re-introduced after the induction hypotheses instead of before them. Every hypothesis now reads <code>∀ {s₂}, Exec … s₂ → … = s₂</code>.'},
       {tac:'| skip =>', h:'The first of the four branches whose rule fixes its own answer. The goal is <code>s✝ = s₂</code> and the only other thing in scope is <code>h₂ : Exec Cmd.skip s✝ s₂</code>.'},
       {tac:'cases h₂; rfl', h:'Only <code>Exec.skip</code> concludes a run of <code>skip</code>, and its conclusion has the same state twice, so the inversion replaces <code>s₂</code> by the initial state everywhere and the goal becomes an identity.'},
       {tac:'| assign => cases h₂; rfl', h:'The same sentence with a longer final state. <code>Exec.assign</code> computes its answer from the store and the expression alone, so once the inversion has fixed <code>s₂</code> the two sides are the same term.'},
       {tac:'| load hl =>', h:'The value-carrying branch. <code>hl : s✝.heap l✝ = some v✝¹</code> came in with the rule, and the goal\'s two sides differ in which value was written into the store.'},
       {tac:'cases h₂ with | load hl\' =>', h:'One surviving rule again, but this time its premise is wanted, so the branch is named. It brings a second value and a second equation at the same address: <code>hl\' : s✝.heap l✝ = some v✝</code>.'},
       {tac:'rw [hl] at hl\'', h:'Rewrites the left-hand side of <code>hl\'</code> using <code>hl</code>. Both equations had the same left-hand side, so <code>hl\'</code> becomes <code>some v✝¹ = some v✝</code> — an equation between two applications of one constructor.'},
       {tac:'cases hl\'', h:'Constructor injectivity, the same move Unit 02 made on <code>Option</code>: from <code>some v = some v\'</code> the two values are identified and one of them disappears from context and goal alike. The case tag gains <code>.refl</code>, which is <code>Eq</code>\'s only constructor.'},
       {tac:'rfl', h:'The two states are now written identically.'},
       {tac:'| write hl => cases h₂ with | write hl\' => rfl', h:'<code>write</code> also carries a value out of the heap, and does not put it in the final state — it stores the value of an expression — so the two premises never have to be reconciled and no injectivity step is needed. <code>free</code> is the same again, storing nothing.'},
       {tac:'| seq _ _ ih₁ ih₂ =>', h:'The compositional shape. The two premises are discarded and the two hypotheses kept; both are now <code>∀</code>-quantified over their own final state.'},
       {tac:'cases h₂ with | seq h₁\' h₂\' =>', h:'Two intermediate states now exist — the one belonging to the derivation being inducted on, and the one that inverting <code>h₂</code> produced — and the goal mentions neither.'},
       {tac:'exact ih₂ (ih₁ h₁\' ▸ h₂\')', h:'<code>ih₁ h₁\'</code> is the first hypothesis applied at the <i>other</i> derivation\'s intermediate state, which is legal only because of <code>generalizing</code>; it proves the two intermediate states equal. <code>▸</code> retypes <code>h₂\'</code> along that equation so that it starts where <code>ih₂</code> expects, and <code>ih₂</code> then delivers the goal.'},
       {tac:'| iteTrue hb _ ih => cases h₂ with', h:'Inverting under <code>ite</code> leaves <b>two</b> branches, because two rules conclude a run of an <code>ite</code>. This is the first branch in the proof where the inner <code>cases</code> does not collapse to one alternative.'},
       {tac:'| iteTrue hb\' h\' => exact ih h\'', h:'The rules agree. Both took the first command, so the single hypothesis applied to the other derivation of that command is the whole argument.'},
       {tac:'| iteFalse hb\' h\' => rw [hb] at hb\'', h:'The rules disagree, about the same expression evaluated in the same store: <code>hb</code> says the guard was <code>true</code>, <code>hb\'</code> says it was <code>false</code>. Rewriting the first into the second turns <code>hb\'</code> into <code>true = false</code>.'},
       {tac:'exact absurd hb\' (by simp)', h:'<code>absurd</code> takes a proposition and a refutation of it and produces anything at all, so the goal is never looked at. The refutation of <code>true = false</code> is one word, because <code>true</code> and <code>false</code> are distinct constructors.'},
       {tac:'| iteFalse hb _ ih => …', h:'The mirror image: the guard clash is now in the <code>iteTrue</code> alternative and the hypothesis closes the <code>iteFalse</code> one. Nothing else changes.'},
       {tac:'| loopFalse hb => cases h₂ with', h:'A loop that stopped. Against <code>loopFalse</code> the goal is an identity; against <code>loopTrue</code> it is a guard clash, and the two sub-derivations of that rule are discarded with underscores because the contradiction does not need them.'},
       {tac:'| loopTrue hb _ _ ihb ihr => …', h:'The widest branch, and the one that justifies inducting on the derivation rather than on the command. <code>ihr</code> is a hypothesis about a derivation of <code>loop b c</code> — the same command as the goal — which is smaller only as a derivation. Its ending, <code>exact ihr (ihb hbody\' ▸ hrest\')</code>, is <code>seq</code>\'s ending in different letters.'}
     ],
     deep:[
       {t:'trace', title:'The load branch, where a value has to be reconciled',
        start:'case load.load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝¹ : Val\nhl : s✝.heap l✝ = some v✝¹\nv✝ : Val\nhl\' : s✝.heap l✝ = some v✝\n⊢ { store := s✝.store.set x✝ v✝¹, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }',
        steps:[
          {tac:'rw [hl] at hl\'',
           state:'case load.load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝¹ : Val\nhl : s✝.heap l✝ = some v✝¹\nv✝ : Val\nhl\' : some v✝¹ = some v✝\n⊢ { store := s✝.store.set x✝ v✝¹, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }',
           h:'The heap lookup has gone out of <code>hl\'</code> and been replaced by what <code>hl</code> says it equals. Both values are still in the goal.'},
          {tac:'cases hl\'',
           state:'case load.load.refl\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝ : Val\nhl : s✝.heap l✝ = some v✝\n⊢ { store := s✝.store.set x✝ v✝, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }',
           h:'One of the two values is gone from the context and from both sides of the goal. This is the same use of <code>cases</code> on a constructor equation as in Unit 02, at a bigger type.'},
          {tac:'rfl', state:'No goals.', h:'Both sides are now the same term.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Attempting <code>cases hl\'</code> before the rewrite is the natural shortcut and it is refused, because <code>hl\'</code> is not yet an equation between two constructor applications — its left-hand side is a heap lookup.'},
       {t:'state', cap:'The <code>rw</code> is what makes the injectivity step legal. <code>s✝.2</code> in the message is the heap field of the state, printed by position rather than by name.',
        src:'error: Dependent elimination failed: Failed to solve equation\n  some v✝ = s✝.2 l✝'},
       {t:'trace', title:'A guard clash',
        start:'case iteTrue.iteFalse\nc : Cmd\ns s₁ s✝ s\'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ : Exec c₁✝ s✝ s\'✝\nih : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝ = s₂\ns₂ : State\nhb\' : BExpr.eval s✝.store b✝ = false\nh\' : Exec c₂✝ s✝ s₂\n⊢ s\'✝ = s₂',
        steps:[
          {tac:'rw [hb] at hb\'',
           state:'case iteTrue.iteFalse\nc : Cmd\ns s₁ s✝ s\'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ : Exec c₁✝ s✝ s\'✝\nih : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝ = s₂\ns₂ : State\nhb\' : true = false\nh\' : Exec c₂✝ s✝ s₂\n⊢ s\'✝ = s₂',
           h:'The context is now contradictory and the goal has stopped mattering. Both guard equations were about the same expression in the same store, which is what makes the rewrite apply.'},
          {tac:'exact absurd hb\' (by simp)', state:'No goals.',
           h:'<code>absurd</code> turns a proposition and its refutation into anything at all. The refutation of <code>true = false</code> is a one-word tactic proof.'}
        ],
        done:'No goals.'},
       {t:'detail', title:'The <code>seq</code> branch of the failed attempt, in full', open:false, blocks:[
         {t:'p', h:'This is what the branch looks like when <code>generalizing s₂</code> was left out. Compare the two <code>ih</code> lines against the ones in the finished proof; everything else is identical.'},
         {t:'state', src:'case seq.seq\nc : Cmd\ns s₁ s₂ s✝ s\'✝¹ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝¹\nh₂✝ : Exec c₂✝ s\'✝¹ s\'\'✝\nih₁ : Exec c₁✝ s✝ s₂ → s\'✝¹ = s₂\nih₂ : Exec c₂✝ s\'✝¹ s₂ → s\'\'✝ = s₂\ns\'✝ : State\nh₁\' : Exec c₁✝ s✝ s\'✝\nh₂\' : Exec c₂✝ s\'✝ s₂\n⊢ s\'\'✝ = s₂'},
         {t:'p', h:'<code>ih₁</code> would prove <code>s\'✝¹ = s₂</code> if you could feed it a derivation from <code>s✝</code> to <code>s₂</code>. The derivation available goes to <code>s\'✝</code>. Nothing in the branch can bridge that, and the failure is reported as a mismatch on the argument of <code>ih₁</code> rather than as anything about induction.'}
       ]}
     ],
     pitfall:'Omitting <code>generalizing s₂</code> and then trying to fix the <code>seq</code> branch where it broke. It cannot be fixed there. What Lean prints is <code>Application type mismatch</code> naming <code>ih₁ h₁\'</code>, which reads like an argument-order problem and is not one: the hypothesis is a true statement about the wrong state, and no rewriting turns a claim about one <code>s₂</code> into a claim about every state. When a type mismatch names an induction hypothesis, suspect the induction, not the line. The second frequent error is writing <code>| load hl hl\' =></code> as though the induction branch and the inner <code>cases</code> shared one name list. They do not — the outer list names only this rule\'s own arguments — and Lean answers <code>Too many variable names provided at alternative `load`: 2 provided, but 1 expected</code>, followed by <code>Unknown identifier `hl\'`</code> on the line that tries to use it. The third is writing bare <code>cases h₂</code> in the <code>seq</code> branch, where the pieces are wanted. It is legal, it leaves exactly the right goal, and the two new derivations arrive as <code>h₁✝</code> and <code>h₂✝</code>, inaccessible, while the branch\'s own premises — which held those two names — are pushed up to <code>h₁✝¹</code> and <code>h₂✝¹</code>. Four derivations in the context and not one of them typeable. Bare <code>cases</code> is for branches you mean to close without looking inside, which is why it appears on <code>skip</code> and <code>assign</code> and nowhere else in this proof.',
     variants:'Drop <code>▸</code> from the <code>seq</code> branch and the mismatch moves to <code>h₂\'</code>: <i>has type</i> <code>Exec c₂✝ s\'✝ s₂</code> <i>but is expected to have type</i> <code>Exec c₂✝ s\'✝¹ s₂</code>. Replace it with <code>have hmid := ih₁ h₁\'</code> followed by <code>subst hmid</code> and <code>exact ih₂ h₂\'</code>, and the proof is the same length and needs no notation. Write <code>generalizing s</code> instead of <code>generalizing s₂</code> and the tactic refuses outright — <code>Variable `s` cannot be generalized because the induction target depends on it</code> — because <code>s</code> is an index of <code>h₁</code> and is generalised already. Reverse the guard rewrite — <code>rw [hb\'] at hb</code> in place of <code>rw [hb] at hb\'</code>, closing on <code>exact absurd hb (by simp)</code> — and the branch is equally dead: the contradiction is <code>false = true</code> instead of <code>true = false</code>, and neither is harder to refute than the other. The direction decides only which of the two hypotheses survives, and nothing after it reads either. Replace <code>cases h₂ with | write hl\' => rfl</code> by <code>cases h₂; rfl</code> and it still compiles: naming the surviving branch there is documentation, not necessity, and it earns its place by recording which of the ten rules the inversion left. Finally, drop the second derivation and try to prove <code>Exec c s s₁ → ∃ s₂, Exec c s s₂ ∧ s₁ = s₂</code>: that is a different and much weaker statement, provable with no induction at all, and the difference is exactly what determinism claims.'},

    /* ============================================================== close === */

    {t:'p', h:'What the theorem buys is a right that has been assumed silently up to now: the right to speak of <i>the</i> final state of a command. A specification of the form "if <code>c</code> runs from a state satisfying <code>P</code>, the state it reaches satisfies <code>Q</code>" is a claim about a set of possible end states, and determinism is what makes that set have at most one element. Unit 35 spends it, deriving partial correctness from total correctness rather than proving them separately.'},

    {t:'dod', h:'You can prove a statement about every <code>Nat</code>, every <code>List</code> and every derivation with one tactic, and say in each case what the induction hypothesis is a proof of. You can tell an induction from a case split by the goal each leaves. You can read an <code>Application type mismatch</code> that names a hypothesis as a report about the induction rather than about the line, repair it with <code>generalizing</code>, and say what that word does to the statement being proved. You can classify the ten branches of a proof over <code>Exec</code> into the ones whose rule fixes its own answer, the one that carries a value out of the heap, and the ones built from smaller runs — and kill an impossible branch by rewriting one guard into another. And you have proved that a command has at most one final state.'},

    {t:'p', h:'The relation proves things and computes nothing. You cannot ask it what a program does — only offer an answer and ask whether it agrees. Whether that matters is the subject of the next unit, and the fact that the next unit is <i>optional</i> is itself informative about what a relational semantics is for.'}

  ]
});
