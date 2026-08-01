registerChapter({
  id: 'compute',
  num: '02',
  phase: 'Phase 0 · Getting started',
  title: 'Equality, computation, and the limits of rfl',
  blurb: 'Why some equations close by computing and others do not, what a type is made of, and the two facts about Option that every heap proof in this course uses.',

  /* x09's `deep` shows the same proof with the saved equation deleted, in order
     to print the two errors that causes. Without the `hl :` the line reads
     `cases h l with | none => …`, which is token-identical to the inversion form
     booked at `22-exec` (ERRATA §7's first collision). It is a deliberate
     failure exhibit and the page says so in the sentence above it; the
     saved-equation form, which is this unit's own row, is what the solution
     uses. */

  /* x07 is the unit's own defect, repaired. `def double … ; theorem … := rfl`
     compiles in local Lean 4.32.2 and is REJECTED by the Lean that runs in the
     reader's browser, which does not expose a plain `def`'s body to a `theorem`.
     The exercise now carries both keywords — `def double` and `abbrev double'`,
     identical bodies — and every `rfl` on this page is either on the `abbrev` or
     inside an `example`. Every error quoted in and around x07 is output from the
     browser's kernel, obtained with `site/tools/e2/wasm-check.cjs`; it is not
     local `check.sh` output, and for these lines the two disagree. See ERRATA
     §28 before you write `:= rfl` after a `def` anywhere. */

  /* x08's `why` names the Unit 13 theorem its two facts are spent on, and marks
     it as a forward reference in the same clause. */
  ledgerForward: ['pointsTo_value_unique'],

  orient: {
    youWill: [
      'Read an <code>inductive</code> declaration, name its constructors, and say what does <i>not</i> inhabit the type.',
      'Write a <code>def</code> by cases and predict, before running Lean, which of its equations <code>rfl</code> will close.',
      'State the rule that decides when <code>rfl</code> works, and name the <i>two</i> different things that block it — a variable where a definition wants to take cases, and the keyword the definition was declared with.',
      'Say why every name in this course\'s model is an <code>abbrev</code> and not a <code>def</code>, and what you write instead when a <code>def</code> is what you have.',
      'Use an equation you cannot compute with: <code>rw [h]</code>, <code>rw [← h]</code>, <code>rw … at h</code>, and a <code>calc</code> chain.',
      'Restate a goal with <code>show</code>, unfold a definition by name, establish an intermediate fact with <code>have</code>, and tell <code>simp</code> from <code>simp only</code>.',
      'Use the two facts about <code>Option</code> — its constructors are distinct, and <code>some</code> is injective.',
      'Say why <code>Loc</code> is <code>Nat</code> and not something else, and what an <code>if</code> demands of the thing it tests.',
      'Split a proof on the <i>value</i> of a heap lookup, keeping the equation that says which case you are in.'
    ],
    needs: [
      'Unit 01: a proof is a term; <code>fun</code>, application, <code>⟨…⟩</code>, <code>obtain</code>, <code>exact</code>.',
      'Unit 00: <code>def</code> and <code>abbrev</code>, <code>simp [f]</code> and <code>simp [f] at h</code>, <code>intro</code>, <code>¬ P</code> as <code>P → False</code>, and the five abbreviations that name the model.'
    ],
    payoff: 'Every equation in the rest of this course is one of two kinds, and which tactic closes it depends on which kind it is. Getting that distinction now is what stops the heap lemmas from Unit 05 onwards feeling arbitrary.'
  },

  blocks: [

    /* ------------------------------------------------- why rfl worked --- */

    {t:'p', h:'Unit 01 closed an equation between numbers with a three-letter proof and left the question of why that was allowed.'},

    {t:'code', tag:'verified', cap:'From Unit 01. The proof is a term, and the term is <code>rfl</code>.',
     src:'theorem two_add_two : 2 + 2 = 4 := rfl'},

    {t:'p', h:'<code>rfl</code> is the proof of reflexivity: for any <code>a</code> it proves <code>a = a</code>, and it proves nothing else. So Lean accepted that line only because, in its notion of what a term <i>is</i>, <code>2 + 2</code> and <code>4</code> are not two things. They are one thing written twice. Which pairs of terms have that property is the question this unit answers — because a heap is a function, two heaps are two functions, and "are these the same?" is very nearly the only question the next six units ask. To see why <code>2 + 2</code> and <code>4</code> are one term you have to know what <code>Nat</code> is, and Lean will tell you.'},

    {t:'code', tag:'illustration',
     cap:'<code>#print</code> answers a different question from <code>#check</code>: not what type this thing has, but how it was declared.',
     src:'#print Nat'},

    {t:'state', cap:'The reply. The <code>file:line:column</code> prefix is dropped here and everywhere on this page.',
     src:'inductive Nat : Type\nnumber of parameters: 0\nconstructors:\nNat.zero : Nat\nNat.succ : Nat → Nat'},

    {t:'p', h:'That is a complete definition of the natural numbers: a name, and two ways of building a value. <code>inductive</code> introduces a type by listing exactly those ways — there is <code>Nat.zero</code>, and there is <code>Nat.succ</code>, which turns a <code>Nat</code> into another one. What the word <i>inductive</i> adds is everything the list leaves out. Nothing else builds a <code>Nat</code>; two values built by different constructors are different; and two values built by the same constructor from different arguments are different.'},

    {t:'p', h:'The numeral <code>4</code> is notation for <code>Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))</code>, and <code>2 + 2</code> has to become that, or <code>rfl</code> would not have been accepted. It becomes that by <i>computing</i>, and computing is possible because the constructor list is exhaustive: a function out of <code>Nat</code> can be given by saying what it does to <code>zero</code> and what it does to a <code>succ</code>. That is a <code>def</code> by cases, and the cases are written as a list.'},

    {t:'code', tag:'illustration',
     cap:'Addition, written out. Each line is one case: <code>|</code> begins a case, the patterns are to the left of <code>=&gt;</code> and the result is to the right. The patterns are the two constructors under their everyday spellings — <code>0</code> is <code>Nat.zero</code> and <code>m + 1</code> is <code>Nat.succ m</code>. The definition may call itself provided the call is on a strictly smaller argument, which is why the recursive call is at <code>m</code> and not at <code>m + 1</code>.',
     src:'def addNat : Nat → Nat → Nat\n  | n, 0     => n\n  | n, m + 1 => addNat n m + 1'},

    {t:'p', h:'Read the second line as the recursion it is: to add <code>m + 1</code> to <code>n</code>, add <code>m</code> and take the successor. Now look at which argument the cases are taken on. The first is <code>n</code> in both lines and is never inspected. The <i>second</i> is the one that has to be a <code>0</code> or a <code>succ</code> before either line can apply. That choice is invisible in the type <code>Nat → Nat → Nat</code>, and it decides everything that follows. Both equations of the definition hold by computation, so both are closed by <code>rfl</code> — no induction, no lemma, nothing but Lean unfolding what you wrote.'},

    {t:'code', tag:'illustration',
     src:'example (n : Nat)   : addNat n 0 = n := rfl\nexample (n m : Nat) : addNat n (m + 1) = addNat n m + 1 := rfl'},

    /* ---------------------------------------- definitional equality --- */

    {t:'sec', s:'Definitional equality, and where it stops'},

    {t:'defn', term:'Definitional and propositional equality',
     h:'Two terms are <b>definitionally equal</b> when they reduce to the same thing: unfold every definition you are permitted to unfold — which is not the same as every definition you can see, and the rest of this section makes that exact — substitute every argument, take every case split whose scrutinee is known, and see whether you arrive at the same term. That is a mechanical test run by Lean\'s kernel — the small trusted core that checks every finished term — and not a proof step you write. <b>Propositional equality</b> is the statement <code>a = b</code>, a proposition like any other, provable by any means at all — induction, a previous theorem, a case analysis. <code>rfl</code> proves <code>a = b</code> exactly when the two sides are definitionally equal, and Lean says so in those words when it refuses.',
     cap:'Every definitional equality is propositional. The converse is where the interesting half of this course lives.'},

    {t:'p', h:'The test has a failure mode that the rest of this course turns on, and it is the one to meet on purpose. Reduction of <code>addNat n m</code> proceeds by asking which case <code>m</code> falls into. If <code>m</code> is a numeral it falls into one. If <code>m</code> is a <i>variable</i> it falls into neither, and reduction stops there with nothing further it can do. So <code>addNat n 0</code> reduced above — the second argument was <code>0</code> — and its mirror image does not.'},

    {t:'code', tag:'sketch', cap:'True, and not closable this way.',
     src:'example (n : Nat) : addNat 0 n = n := by rfl'},

    {t:'state', cap:'Lean naming the concept itself. The last two lines are the goal it gave up on.',
     src:'error: Tactic `rfl` failed: The left-hand side\n  addNat 0 n\nis not definitionally equal to the right-hand side\n  n\n\nn : Nat\n⊢ addNat 0 n = n'},

    {t:'p', h:'<code>addNat 0 n = n</code> is true, and it is proved by induction on <code>n</code> — a proof, with a base case and a step, and therefore not something the kernel performs silently while checking a term. The asymmetry between the two sides is not a fact about arithmetic. It is a fact about which argument <code>addNat</code> takes its cases on, and had the definition recursed on the first argument instead, the failing example and the succeeding one would swap places. Lean\'s own <code>+</code> on <code>Nat</code> recurses on the second argument, exactly as <code>addNat</code> does, which is why <code>n + 0 = n</code> is <code>rfl</code> and <code>0 + n = n</code> is not.'},

    {t:'p', h:'That is one way to be stopped, and everything about it is a fact about the <i>term</i>: reduction ran out of road at a particular subexpression, and you can point at it. There is a second way, and it has nothing to do with the term. It is a fact about the word the definition was declared with. Here is one function under both words, so that the keyword is the only difference between them.'},

    {t:'code', tag:'verified',
     cap:'Two names for one function. Unit 00 said that <code>abbrev</code> names a type <i>transparently</i> and <code>def</code> does not; the same word does the same job for a function, and this is where the difference becomes visible. Both definitions join the course\'s vocabulary and stay in scope for the rest of this page.',
     src:'def double (n : Nat) : Nat := n + n\n\nabbrev double\' (n : Nat) : Nat := n + n'},

    {t:'p', h:'<code>double\' n = n + n</code> is closed by <code>rfl</code>. <code>double n = n + n</code> is not. Those are the same equation about the same function; what differs is one word in a declaration you did not have to look at in order to write either statement down.'},

    {t:'code', tag:'sketch', cap:'True, and not closable this way either.',
     src:'theorem double_unfold (n : Nat) : double n = n + n := rfl'},

    {t:'state', cap:'The refusal, and the note underneath it that says why. Keep reading to the note: it is the whole diagnosis, and it is the only part of the message that is about your declaration rather than about your goal.',
     src:'error: Not a definitional equality: the left-hand side\n  double n\nis not definitionally equal to the right-hand side\n  n + n\n\nNote: This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.'},

    {t:'p', h:'A <code>theorem</code> is <b>exported</b>: it is part of what this file offers to everything written after it, and Lean holds it to a rule that goes with that. Its statement travels; the bodies of the plain <code>def</code>s underneath it do not. So <code>rfl</code>, asked to check <code>double n</code> against <code>n + n</code>, is not permitted to look inside <code>double</code>, and there is nothing else it could have done. An <code>abbrev</code> is a <code>def</code> marked <b>reducible</b>, and a reducible definition\'s body <i>is</i> part of what its name means — so it travels with the name, and <code>rfl</code> may unfold it. That is the entire difference between the two lines above.'},

    {t:'p', h:'It is also why the two <code>addNat</code> equations further up are <code>example</code>s. An <code>example</code> has no name and exports nothing, so nothing is hidden from it and the same <code>rfl</code> that is refused here is accepted there; write either of them as a <code>theorem</code> and it is refused too, with the same note. And it says what to do when a <code>def</code> is what you have: <b>ask by name</b>. <code>simp [double]</code> adds <code>double</code>\'s defining equation to what <code>simp</code> may rewrite with, and <code>unfold double</code> replaces the name by its body outright. Naming the definition is exactly the thing <code>rfl</code> cannot do. When instead you want a name that <code>rfl</code> sees straight through, you declare it <code>abbrev</code> — which is the reason the five names that make up this course\'s model are <code>abbrev</code>s, a line Unit 00 showed you and could not yet explain.'},

    {t:'note', kind:'key', title:'The rule',
     h:'<code>rfl</code> succeeds when both sides reduce to the same term, and two different things stop it. <b>The term</b> stops it when a variable sits in a position that is being cased on: reduction reaches it and has no case to take. <b>The keyword</b> stops it when the definition it would have to unfold is a plain <code>def</code> and the declaration being proved is a <code>theorem</code>. The message tells you which — Lean adds the <code>Note:</code> about exposing definitions when, and only when, exposing one would have fixed the goal. With the note, the repair is to name the definition (<code>simp [f]</code>, <code>unfold f</code>) or to declare it <code>abbrev</code>. Without it, no amount of unfolding will help: look for the variable, ask which definition was waiting to split on it, and go and find a theorem.'},

    {t:'ex',
     id:'x07',
     name:'double',
     hard:false,
     why:'Four equations about two definitions that differ by a single keyword. Two of them close by computing; two do not, and for two <i>different</i> reasons. Telling them apart by eye is the skill; from Unit 05 onwards every heap lemma you meet is one of these, and reaching for the wrong tactic costs you the goal state you would have learned from. It is also the first place you see <code>simp</code> doing something <code>rfl</code> cannot, which is not a matter of <code>simp</code> being stronger — it is a matter of <code>simp</code> being handed a name, and then knowing a theorem.',
     setup:'<code>def double (n : Nat) : Nat := n + n</code> and <code>abbrev double\' (n : Nat) : Nat := n + n</code> are both in scope — one function, two keywords. Four separate theorems, and the editor opens with all four statements and a <code>sorry</code> under each; replace the four <code>sorry</code>s. The first two want a term, the last two want one tactic under the <code>by</code> that is already there. Nothing beyond <code>rfl</code> and <code>simp</code> is needed.',
     goal:'theorem double\'_unfold (n : Nat) : double\' n = n + n :=\n  sorry\n\ntheorem double\'_three : double\' 3 = 6 :=\n  sorry\n\ntheorem double_unfold (n : Nat) : double n = n + n := by\n  sorry\n\ntheorem double_zero_left (n : Nat) : double n = 0 + n + n := by',
     hints:[
       'The first goal says that <code>double\'</code> applied to an arbitrary <code>n</code> is <code>n + n</code>. The second says <code>double\' 3</code> is <code>6</code>. The third says exactly what the first says, with <code>double</code> in place of <code>double\'</code>. The fourth says <code>double n</code> is <code>0 + n + n</code>, which is <code>(0 + n) + n</code> — the bracketing matters, and so does which side of the <code>+</code> the <code>0</code> is on.',
       'Ask of each: is Lean <i>permitted</i> to get from one side to the other by unfolding and computing alone? Unfolding <code>double\'</code> is permitted, because <code>abbrev</code> says so. Unfolding <code>double</code> inside a <code>theorem</code> is not. Computing <code>3 + 3</code> is permitted, because both arguments are numerals. Computing <code>0 + n</code> is not, because the second argument is a variable and addition splits on it — but <code>0 + n = n</code> is still a theorem, and somebody has already proved it.',
       'The first two want <code>rfl</code>, written as a term: <code>:=</code> and then the word, with no <code>by</code>. The last two want <code>simp</code>, and <code>simp</code> has to be told that <code>double</code> is one of the equations it may use — the bracketed form from Unit 00 is what tells it. In the fourth, the theorem that clears the <code>0 +</code> is <code>Nat.zero_add</code>, and that one is already in <code>simp</code>\'s default stock, so it does not go in the bracket.',
       'The first is <code>:= rfl</code>: unfolding <code>double\' n</code> gives <code>n + n</code> on the nose. The second is <code>:= rfl</code> as well. The third and fourth are both <code>by</code> and then <code>simp [double]</code> — in the third that bracket is the whole of the work, and in the fourth it is half of it.'
     ],
     sol:'theorem double\'_unfold (n : Nat) : double\' n = n + n := rfl\n\ntheorem double\'_three : double\' 3 = 6 := rfl\n\ntheorem double_unfold (n : Nat) : double n = n + n := by\n  simp [double]\n\ntheorem double_zero_left (n : Nat) : double n = 0 + n + n := by\n  simp [double]',
     solNote:'If you climbed all four hints and are still stuck, open this without hesitation. The lesson here is the classification, not the typing.',
     expl:'<code>double\'_unfold</code> holds because unfolding an <code>abbrev</code> is part of reduction; there is no computation in it at all. <code>double\'_three</code> holds because both sides then reduce to the same numeral. <code>double_unfold</code> is the same statement as the first one and <code>rfl</code> will not have it, because a plain <code>def</code> is not unfolded inside a <code>theorem</code> — <code>simp [double]</code> closes it by naming the definition, and nothing propositional happens in that proof at all. <code>double_zero_left</code> would fail even if <code>double</code> were an <code>abbrev</code>: <code>0 + n</code> stops reduction on its own account, and <code>simp</code> closes it not by computing harder but by applying a theorem that was proved by induction long before you got here.',
     walk:[
       {tac:'double\'_unfold := rfl', h:'The goal is <code>double\' n = n + n</code>. Reduction unfolds <code>double\'</code> on the left — it is an <code>abbrev</code>, so <code>rfl</code> may — and then stops, because <code>n + n</code> can go no further with <code>n</code> a variable. The right-hand side is already <code>n + n</code>. Same term, so <code>rfl</code> typechecks.'},
       {tac:'double\'_three := rfl', h:'Unfolding gives <code>3 + 3</code>, and now both arguments of <code>+</code> are numerals, so the case split has something to split on and runs to the end. Both sides become the same numeral. Nothing here differs in kind from the previous line; it only does more work.'},
       {tac:'double_unfold := by simp [double]', h:'The same statement as the first line, and <code>rfl</code> is refused on it, because <code>double</code> is a <code>def</code> and a <code>theorem</code> may not unfold one. <code>simp [double]</code> supplies by name the step <code>rfl</code> was not allowed to take: the bracket adds <code>double</code>\'s defining equation to <code>simp</code>\'s stock, the left-hand side becomes <code>n + n</code>, and two identical sides close. Every ingredient of this proof is the unfolding; there is no theorem in it.'},
       {tac:'double_zero_left := by simp [double]', h:'Turned <code>double n = 0 + n + n</code> into <code>n + n = 0 + n + n</code> by the same bracketed equation, then cleared the <code>0 +</code> by <code>Nat.zero_add</code>, which is in <code>simp</code>\'s default stock, leaving two identical sides and no goal. This is the one with both halves in it. Without the bracket <code>simp</code> would not have touched <code>double</code>: a <code>def</code> is not a rewrite rule until you say so.'}
     ],
     deep:[
       {t:'trace', title:'The fourth one, split in two so you can see which half is which',
        start:'n : Nat\n⊢ double n = 0 + n + n',
        steps:[
          {tac:'simp only [double]',
           state:'n : Nat\n⊢ n + n = 0 + n + n',
           h:'<code>simp only [f]</code> rewrites with the listed equations and <b>nothing else</b>. Here that unfolds <code>double</code> and then stops, leaving a goal that is visibly true and visibly not <code>rfl</code>. This is the definitional half of the work.'},
          {tac:'simp',
           state:'No goals.',
           h:'Bare <code>simp</code> brings in its default stock, which contains <code>Nat.zero_add</code>. This is the propositional half: a theorem, proved by induction, being used. Name it by hand and the whole proof fits on one line with nothing implicit in it — <code>simp only [double, Nat.zero_add]</code> closes the goal, and those two entries are exactly the definitional half and the propositional half. Running them together as <code>simp [double]</code> is what the solution does.'}
        ]},
       {t:'p', h:'The failure to provoke once, deliberately, is the one where you stop after the first half:'},
       {t:'code', tag:'sketch', src:'example (n : Nat) : double n = 0 + n + n := by\n  simp only [double]'},
       {t:'state', cap:'<code>simp only</code> made progress and then had nothing left to do. It does not report failure; it reports what survived.',
        src:'error: unsolved goals\nn : Nat\n⊢ n + n = 0 + n + n'},
       {t:'p', h:'And the fourth one written as a term, the way the first two are. It is the refusal you already met on <code>double_unfold</code> with one thing missing, and the missing thing is the diagnosis:'},
       {t:'code', tag:'sketch', src:'theorem double_zero_left (n : Nat) : double n = 0 + n + n := rfl'},
       {t:'state', cap:'Two errors from one line, and <b>no <code>Note:</code></b> under either. The first is the real one; the second is what is left over once the first has failed, and it says nothing about your goal. The note that appeared on <code>double_unfold</code> is absent here because exposing <code>double</code> would not have saved this goal — <code>0 + n</code> blocks it whatever keyword the definition carries.',
        src:'error: Not a definitional equality: the left-hand side\n  double n\nis not definitionally equal to the right-hand side\n  0 + n + n\n\nerror: Type mismatch\n  rfl\nhas type\n  ?m.13 = ?m.13\nbut is expected to have type\n  double n = 0 + n + n'}
     ],
     pitfall:'Two of them, one per refusal. On the third, reaching for <code>rfl</code> because the first two took it: the statement is word for word the first one\'s, and the only thing standing between you and a term proof is three letters in a declaration you did not write. On the fourth, reading the refusal as "Lean cannot see that <code>0 + n</code> is <code>n</code>". Lean can prove that and is not being asked to: <code>rfl</code> is a request for a syntactic outcome after reduction, and reduction of <code>0 + n</code> stops at the variable. What makes both messages hard to use is printed above. They give you the two sides <i>as you wrote them</i> — <code>double n</code> against <code>0 + n + n</code> — and not the normal forms they actually compared, so the subterm that blocked them is never pointed at. Finding it is your job, and there is exactly one piece of help on offer: the <code>Note:</code> line. Present, and the keyword is your problem. Absent, and the term is.',
     variants:'Change the third statement\'s <code>double</code> to <code>double\'</code> and it <i>is</i> the first statement, closed by <code>rfl</code>; leave it alone and change the word <code>theorem</code> to <code>example</code> and <code>rfl</code> is accepted as it stands, because an <code>example</code> exports nothing and nothing is hidden from it. Those are the same observation from opposite ends. Change the fourth to <code>double n = n + 0 + n</code> and <code>rfl</code> still fails — but now with the note, because <code>n + 0</code> reduces where <code>0 + n</code> does not, so the keyword is the last thing standing and <code>double\' n = n + 0 + n := rfl</code> goes through. Change it instead to <code>double\' n = n * 2</code> and something stranger happens: <code>rfl</code> fails, and <code>simp [double\']</code> fails too, leaving <code>n + n = n * 2</code>. Yet <code>n * 2</code> and <code>0 + n + n</code> are the <i>same term</i>. Multiplication recurses on its second argument exactly as addition does, so <code>n * 2</code> unrolls to <code>n * 1 + n</code>, to <code>(n * 0 + n) + n</code>, to <code>(0 + n) + n</code> — and <code>example (n : Nat) : n * 2 = 0 + n + n := rfl</code> is accepted. So <code>double\' n = 0 + n + n</code> and <code>double\' n = n * 2</code> are definitionally the same statement, and <code>simp [double\']</code> closes one of them and not the other, because <code>simp</code> rewrites the syntax in front of it and never reduces to find out what that syntax means. Drop the bracket from the fourth\'s <code>simp [double]</code> and the goal comes back as <code>double n = n + n</code>, with the <code>0 +</code> cleared and the definition untouched — the clearest single demonstration on this page that unfolding and rewriting are two different operations.'
    },

    /* ---------------------------------------------------------- rw --- */

    {t:'sec', s:'Using an equation you cannot compute with'},

    {t:'p', h:'A propositional equality that is not definitional is a hypothesis, and a hypothesis has to be applied to something. The tactic that applies an equation is <code>rw</code>: given <code>h : a = b</code>, <code>rw [h]</code> finds every occurrence of <code>a</code> in the goal and replaces it with <code>b</code>. It is the direct counterpart of the sentence "substituting <code>b</code> for <code>a</code>" you would write on paper, and it is directional — the left-hand side of the equation is what it hunts for.'},

    {t:'code', tag:'verified', src:'theorem rw_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  rw [h1, h2]'},

    {t:'trace', title:'rw_demo, one rewrite at a time',
     start:'a b c : Nat\nh1 : a = b\nh2 : b = c\n⊢ a = c',
     steps:[
       {tac:'rw [h1]',
        state:'a b c : Nat\nh1 : a = b\nh2 : b = c\n⊢ b = c',
        h:'The <code>a</code> in the goal became <code>b</code>. The hypothesis is unchanged and still available; <code>rw</code> rewrote the goal, not the context.'},
       {tac:'rw [h2]',
        state:'No goals.',
        h:'The <code>b</code> became <code>c</code>, leaving <code>c = c</code> — and the goal closed with no further line. <b><code>rw</code> tries <code>rfl</code> after every rewrite.</b> That is why most proofs in this course end at a <code>rw</code> with nothing after it, and why deleting the last <code>rw</code> from a working proof leaves you not with one readable goal but with a goal whose shape you cannot see.'}
     ]},

    {t:'code', tag:'illustration',
     cap:'Two variations, both needed constantly. <code>rw [← h]</code> runs the equation right to left, hunting for <code>b</code> and writing <code>a</code>; the arrow is typed <code>\\l</code>. <code>rw [h] at h\'</code> rewrites inside a hypothesis instead of the goal, which is how two hypotheses are made to talk to each other. In the first proof the goal becomes <code>a = a</code> and the trailing <code>rfl</code> takes it; in the second, <code>h1</code> becomes the goal exactly.',
     src:'example (a b : Nat) (h1 : a = b) : b = a := by\n  rw [← h1]\n\nexample (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  rw [h2] at h1\n  exact h1'},

    {t:'p', h:'Definitional equality is not only a test the kernel runs on your behalf; it is also a licence. Anywhere a goal is expected, any definitionally equal goal will do, and <code>show T</code> takes that up — it replaces the current goal with <code>T</code>, and is accepted precisely when <code>T</code> is definitionally equal to what was there. Nothing is proved by a <code>show</code>. What it buys is a goal you can read, which starts to matter as soon as the definitions are deep enough to hide the shape of the thing.'},

    {t:'code', tag:'illustration',
     cap:'The goal was <code>double\' n = n + n</code> and became <code>n + n = n + n</code>, with no proof obligation incurred, because the two are the same term. It is the <code>abbrev</code> of the pair for that reason.',
     src:'example (n : Nat) : double\' n = n + n := by\n  show n + n = n + n\n  rfl'},

    {t:'p', h:'<code>unfold f</code> does the same job with the name of the definition supplied instead of the result: it replaces <code>f</code> by its body in the goal. Because you supply the name, it works on a plain <code>def</code> — it is the second of the two ways of asking, alongside <code>simp [f]</code>. It differs from <code>rw</code> in one way that costs people time. <code>unfold double</code> leaves the goal <code>n + n = n + n</code> standing, and Lean reports <code>unsolved goals</code> under two identical sides — which reads as a bug and is not one, because <code>rw</code> tries <code>rfl</code> when it finishes and <code>unfold</code> does not. Going the other way, <code>have h : T := e</code> puts a fact <i>into</i> the context: given a proof <code>e</code> of <code>T</code> it adds <code>h : T</code> above the line, so something needed twice is established once. The proof <code>e</code> may be a <code>by</code> block, since a tactic proof is a term like any other and stands wherever a term is wanted. Omit the name and the hypothesis is called <code>this</code>, which is worth doing exactly when the fact is used on the very next line.'},

    {t:'code', tag:'illustration',
     cap:'Three proofs of two statements. The first needs its <code>rfl</code> on the line after <code>unfold</code>; the second and third are one proof, named and unnamed.',
     src:'example (n : Nat) : double n = n + n := by\n  unfold double\n  rfl\n\nexample (a b c : Nat) (h1 : a = b) (h2 : b = c) : double a = double c := by\n  have h : a = c := by rw [h1, h2]\n  rw [h]\n\nexample (a b c : Nat) (h1 : a = b) (h2 : b = c) : double a = double c := by\n  have : a = c := by rw [h1, h2]\n  rw [this]'},

    {t:'p', h:'<code>simp</code> and <code>simp only</code> differ in a way that has not been said yet. <code>simp</code> rewrites with a large default stock of equations, left to right, until nothing applies; brackets add to that stock. <code>simp only [f]</code> throws the stock away and uses nothing but what is listed — x07 showed you both halves of that. Bare <code>simp</code> is the right tactic when you want a goal cleared and do not care how. <code>simp only</code> is the right one when you want a goal in a particular shape and cannot afford <code>simp</code> to keep going and leave it in a different one. Proofs from Unit 06 onwards use <code>simp only</code> for exactly that reason, and the choice is never cosmetic.'},

    {t:'detail', title:'Putting the intermediate terms on the page: calc', tag:'aside', open:false,
     blocks:[
       {t:'p', h:'A chain of rewrites is quick to write and hard to read: <code>rw [h1, h2]</code> does not say what the intermediate term was. When the chain is the point, <code>calc</code> puts the intermediate terms in the source.'},
       {t:'anat', tag:'verified',
        src:'theorem calc_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=\n  calc a = b := h1\n    _ = c := h2',
        parts:[
          {m:':=', h:'No <code>by</code>. A <code>calc</code> block is a term, not a tactic — admissible anywhere a proof is, including inside a tactic proof, and it is what a displayed chain of equalities on paper corresponds to.'},
          {m:'calc a = b := h1', h:'The first link. To the left of <code>:=</code> is a claim, <code>a = b</code>; to the right is its proof. The claim is written out in full, and that is the entire benefit — a reader sees <code>b</code> without simulating <code>rw</code> in their head.'},
          {m:'_ = c := h2', h:'The underscore stands for the right-hand side of the previous link, so this line claims <code>b = c</code>. Writing <code>b</code> there instead is legal and is what the underscore abbreviates; the underscore is preferred because it cannot drift out of step with the line above it.'}
        ]}
     ]},

    /* ------------------------------------------------------ Option --- */

    {t:'sec', s:'Option, and the two facts about it'},

    {t:'p', h:'A heap is <code>Loc → Option Val</code>: a total function whose values carry the partiality. That much was settled in Unit 00. What was not settled is what <code>Option</code> <i>is</i>, and the answer has the same shape as <code>Nat</code>\'s — a name, and a list of ways to build a value.'},

    {t:'code', tag:'illustration', src:'#print Option'},

    {t:'state', cap:'The <code>.{u}</code> and the <code>Type u</code> record that <code>Option</code> works at every level of Lean\'s hierarchy of types. Nothing in this course needs more than one level; read past them.',
     src:'inductive Option.{u} : Type u → Type u\nnumber of parameters: 1\nconstructors:\nOption.none : {α : Type u} → Option α\nOption.some : {α : Type u} → α → Option α'},

    {t:'p', h:'One parameter, <code>α</code>, which for us is always <code>Val</code>. Two constructors: <code>none</code>, carrying nothing, and <code>some</code>, carrying one <code>α</code>. Their full names are <code>Option.none</code> and <code>Option.some</code>, and you have been writing them unqualified because Lean resolves a bare <code>none</code> against the type it is expecting. Where such an expectation exists the name may also be written with a leading dot and no namespace at all — <code>.none</code> means "the constructor called <code>none</code> belonging to whatever type is wanted here". That spelling is how patterns are usually written, and it is how the syntax of the programming language in Unit 18 will be taken apart.'},

    {t:'code', tag:'illustration',
     cap:'A <code>def</code> by cases on an <code>Option</code>, in the leading-dot spelling. Both equations hold by <code>rfl</code>, for the reason the <code>addNat</code> equations did: the argument being split on is a constructor, so the split has somewhere to go.',
     src:'def orDefault : Option Val → Val → Val\n  | .none,   d => d\n  | .some v, _ => v\n\nexample (d : Val)   : orDefault none d = d := rfl\nexample (v d : Val) : orDefault (some v) d = v := rfl'},

    {t:'p', h:'Now the two facts the constructor list gives you, in the form you will use them. <b>Distinctness:</b> <code>some v</code> and <code>none</code> are built by different constructors, so they are different values — <code>some v = none</code> is not an unproved statement but a refutable one, and a proof of it would let you conclude anything at all. <b>Injectivity:</b> <code>some</code> is a constructor, so it cannot collapse two values into one; from <code>some v = some w</code> you get <code>v = w</code>, by the lemma <code>Option.some.inj</code>. The other direction needs no lemma about <code>Option</code> whatever, since applying any function to equal arguments gives equal results — that is <code>congrArg f</code>.'},

    {t:'p', h:'"Conclude anything at all" is itself a term. <code>absurd h hn</code> takes a proof <code>h : P</code> and a proof <code>hn : ¬ P</code>, and has whatever type the goal has. Nothing about that is arbitrary. <code>¬ P</code> is <code>P → False</code>, so <code>hn h</code> is an inhabitant of <code>False</code> — and <code>False</code> is declared the way <code>Nat</code> and <code>Option</code> are, by listing its constructors, of which it has none. A type with no constructors has no values, so a context that hands you one is a context that could never have arisen — and there is nothing a goal can demand of a situation that does not occur.'},

    {t:'code', tag:'illustration',
     cap:'Injectivity backwards, with no <code>Option</code> lemma in sight; then a false hypothesis closing a goal that has nothing to do with it. <code>absurd</code> wants the claim and its refutation. The refutation is distinctness — the fact stated two paragraphs up — carried here as a value under the name <code>some_ne_none</code>, which is the theorem you prove in the exercise directly below.',
     src:'example (v w : Val) (h : v = w) : some v = some w := congrArg some h\n\nexample (v : Val) (h : some v = none) : 2 + 2 = 5 := absurd h (some_ne_none v)'},

    {t:'ex',
     id:'x08',
     name:'some_inj / some_ne_none',
     hard:false,
     why:'These two facts are the entire content of several later proofs. <code>Option.some.inj</code> is what makes <code>pointsTo_value_unique</code> go through in Unit 13 — the theorem that a location holds at most one value — and distinctness of the constructors is what makes an assertion about an unallocated address refutable rather than unproven. Doing them by hand once means that later, when either appears as one step inside a six-step proof, you know which fact is being spent.',
     setup:'Three theorems, and the editor opens with all three statements and a <code>sorry</code> under each. The first is a term: one lemma applied to one hypothesis, no <code>by</code>. The second and third state the same thing and must be proved differently — the second in one tactic, the third by taking the negation apart the way Unit 00 did and then asking Lean which cases of the equation are possible.',
     goal:'theorem some_inj (v w : Val) (h : some v = some w) : v = w :=\n  sorry\n\ntheorem some_ne_none (v : Val) : some v ≠ none := by\n  sorry\n\ntheorem some_ne_none\' (v : Val) : some v ≠ none := by',
     hints:[
       'The first goal has <code>h : some v = some w</code> above the line and wants <code>v = w</code>. The second and third both want <code>some v ≠ none</code>, which unfolds to <code>some v = none → False</code>.',
       'The first is injectivity of a constructor, and it is a lemma rather than a computation — <code>v</code> and <code>w</code> are variables, so nothing reduces. For the other two: constructors of an inductive type build distinct values, so an equation between two values made by <i>different</i> constructors has no proofs at all. You can either let a tactic know that, or assume such a proof and ask what shape it could possibly have.',
       'The lemma the first one wants is called <code>Option.some.inj</code> — watch where the dot goes. The second wants <code>simp</code>, alone. The third wants <code>intro</code> and then <code>cases</code>, and nothing after them.',
       '<code>Option.some.inj h</code> is the whole of the first term. The second is <code>by simp</code>. In the third, <code>intro h</code> leaves <code>h : some v = none</code> with goal <code>False</code>; <code>cases h</code> then asks which constructor of <code>Eq</code> could have produced <code>h</code>, finds that none could, and closes the goal by having no cases left to prove.'
     ],
     sol:'theorem some_inj (v w : Val) (h : some v = some w) : v = w :=\n  Option.some.inj h\n\ntheorem some_ne_none (v : Val) : some v ≠ none := by\n  simp\n\ntheorem some_ne_none\' (v : Val) : some v ≠ none := by\n  intro h\n  cases h',
     solNote:'The third proof has no visible final step, and that is the point of it: <code>cases h</code> produced zero goals, so there was nothing left to write.',
     expl:'The first is a lemma applied to a hypothesis and nothing else. The second and third differ only in who does the work: <code>simp</code> knows a lemma saying constructors are distinct, whereas <code>cases</code> goes to the source and asks the type itself. Both are correct; the third is the one to understand, because it shows where the fact comes from.',
     walk:[
       {tac:'Option.some.inj h', h:'The name reads as three parts: the type <code>Option</code>, its constructor <code>some</code>, and the injectivity lemma <code>inj</code> that Lean generates for every constructor of every inductive type. Applying it to <code>h : some v = some w</code> produces a proof of <code>v = w</code>, which is the goal, so the term is complete.'},
       {tac:'simp', h:'Closed <code>some v ≠ none</code> outright, in three rewrites it does not show you: the <code>≠</code> became <code>¬ (some v = none)</code>, the equation between two different constructors became <code>False</code>, and <code>¬ False</code> became <code>True</code>. Nothing about <code>Option</code> in particular is used — the middle step runs for any two distinct constructors of any inductive type.'},
       {tac:'intro h', h:'Turned the goal <code>some v ≠ none</code> into <code>False</code>, with <code>h : some v = none</code> above the line — the move from Unit 00, unchanged, because <code>≠</code> is still <code>→ False</code>.'},
       {tac:'cases h', h:'Split <code>h</code> into the cases that could have built it. <code>h</code> proves an equation whose two sides are made by different constructors, and no such proof can be built, so the split yields zero cases and the goal is discharged. Nothing follows this line because there is nothing left.'}
     ],
     deep:[
       {t:'trace', title:'The third proof',
        start:'v : Val\n⊢ some v ≠ none',
        steps:[
          {tac:'intro h',
           state:'v : Val\nh : some v = none\n⊢ False',
           h:'The goal display no longer contains <code>≠</code>. What was a negation is now an obligation to derive <code>False</code> from an assumption Lean has written into the context for you.'},
          {tac:'cases h',
           state:'No goals.',
           h:'Zero goals, not one goal closed by an argument. This is the shape of every impossible-case discharge in this course, and it is why the branch of a heap case split you "cannot prove" is often the branch with nothing to prove.'}
        ]},
       {t:'cmp',
        left:{t:'The fact, delegated', tag:'sketch',
              h:'Correct, one tactic, and it tells you nothing about why. Use it in a proof whose interest lies elsewhere.',
              src:'by simp'},
        right:{t:'The fact, exhibited', tag:'sketch',
               h:'Two tactics, and they name the mechanism: an equation between distinct constructors has no proofs, so a case analysis on one is a case analysis over the empty list of cases.',
               src:'by\n  intro h\n  cases h'}},
       {t:'p', h:'The near miss on the first theorem, and what Lean says about it:'},
       {t:'code', tag:'sketch', src:'example (v w : Val) (h : some v = some w) : v = w :=\n  Option.some_inj h'},
       {t:'state', cap:'The <code>Note:</code> line is kept here, because it is the line that says what the complaint actually is. The type printed on the third and fourth lines is the whole diagnosis.',
        src:'error: Function expected at\n  Option.some_inj\nbut this term has type\n  some ?m.6 = some ?m.7 ↔ ?m.6 = ?m.7\n\nNote: Expected a function because this term is being applied to the argument\n  h'}
     ],
     pitfall:'Writing <code>Option.some_inj</code>, which also exists and is not the same thing. It is an <code>↔</code>, not an implication, so it is not a function and cannot be applied to <code>h</code> at all — the message is above, and the type it prints for the name is the tell: an <code>↔</code> where you wanted an arrow. Both repairs are one token: <code>Option.some.inj h</code>, or <code>Option.some_inj.mp h</code> with the <code>.mp</code> from Unit 01. The underscore-versus-dot difference is not decoration: <code>Option.some.inj</code> is generated from the constructor <code>some</code>, and every constructor in this course has one.',
     variants:'Reverse the second statement to <code>none ≠ some v</code> and <code>by simp</code> still closes it, because the distinctness lemmas are stated in both directions — a courtesy of the library rather than something to rely on generally, as Unit 03 will show you for <code>≠</code> between variables. Run <code>cases h</code> instead on a hypothesis <code>h : v = w</code> between two <i>variables</i> and it does something completely different and useful: one case survives, labelled <code>case refl</code> after the single constructor of <code>Eq</code>, with <code>w</code> gone from the context and <code>v</code> standing in its place everywhere. The tactic is the same both times, and so is the question it asks: which uses of <code>Eq</code>\'s one constructor could have built this proof? Here <code>refl</code> could, once <code>w</code> is taken to be <code>v</code>, so you get one branch. Above it could not, so you get none, and a goal with no branches is a goal that is finished. And drop the hypothesis from the first theorem, leaving <code>v = w</code> with nothing above the line, and it is false at the first pair you try — <code>v := 0</code>, <code>w := 1</code> — because no amount of injectivity manufactures a hypothesis you were not given.'
    },

    /* -------------------------------------------------- Decidable --- */

    {t:'sec', s:'What an if demands, and why Loc is Nat'},

    {t:'p', h:'Every heap written down in this course so far is a chain of conditionals — <code>fun x =&gt; if x = 4 then some 5 else none</code>. To evaluate that at an argument, Lean has to establish whether <code>x = 4</code>, and <code>x = 4</code> is a proposition, not a yes-or-no answer. Something has to turn one into the other, and <code>if</code> will not proceed until it is supplied. That something has a type: a value of <code>Decidable p</code> is a settled verdict on <code>p</code> with its evidence attached — either a proof of <code>p</code> or a proof of <code>¬ p</code> — and <code>if p then a else b</code> is a function of such a value. For equations between naturals the verdict is produced by <code>Nat.decEq</code>, which walks both numbers down to <code>zero</code>. For equations between two functions there is no such walk to take, so no verdict gets produced and the definition does not go through.'},

    {t:'code', tag:'sketch',
     cap:'A heap addressed by functions instead of numbers. The <code>#check</code> succeeds and the definition is refused.',
     src:'#check @Nat.decEq\n\nabbrev FunLoc := Nat → Nat\n\ndef funHeap : FunLoc → Option Val :=\n  fun x => if x = (fun _ => 4) then some 5 else none'},

    {t:'state', cap:'The <code>Hint:</code> line that follows the error is dropped.',
     src:'Nat.decEq : (n m : Nat) → Decidable (n = m)\nerror: failed to synthesize instance of type class\n  Decidable (x = fun x => 4)'},

    {t:'p', h:'You never wrote <code>Nat.decEq</code> into <code>aliasedAfter</code> and you never will, because it is registered with the keyword <code>instance</code>, which marks a definition as one Lean may go and find for itself whenever a value of that type is required. That is the whole mechanism: an instance is a value Lean supplies without being asked. Deciding whether two functions <code>Nat → Nat</code> agree at every argument is not a computation, so no instance is registered for it, and the conditional above never gets a meaning. Which makes the first line of the model a choice with consequences rather than a formality.'},

    {t:'code', tag:'verified',
     cap:'From Unit 00, and now readable twice over. <code>Loc := Nat</code> is what makes the conditional in every heap literal legal; <code>Var := Nat</code> is the same decision taken a second time, for the same reason, since a store literal tests a variable the way a heap literal tests an address. And every one of the five is an <code>abbrev</code>, which is x07\'s other lesson applied to the model itself. Make <code>Heap</code> a <code>def</code> and the declaration is accepted and everything after it stops: <code>h l</code> is no longer a function application, because the name no longer unfolds to a function type on its own, and Lean says <code>Function expected at h</code>.',
     src:'abbrev Loc   := Nat\nabbrev Val   := Nat\nabbrev Heap  := Loc → Option Val\nabbrev Var   := Nat\nabbrev Store := Var → Val'},

    {t:'detail', title:'What decidability costs, and what open Classical would buy', tag:'aside', open:false,
     blocks:[
       {t:'p', h:'<code>Decidable</code> is an ordinary inductive type and its constructors say exactly what a verdict is.'},
       {t:'code', tag:'illustration', src:'#print Decidable'},
       {t:'state', src:'inductive Decidable : Prop → Type\nnumber of parameters: 1\nconstructors:\nDecidable.isFalse : {p : Prop} → ¬p → Decidable p\nDecidable.isTrue : {p : Prop} → p → Decidable p'},
       {t:'p', h:'The objection this invites: classically every proposition is true or false, so why should Lean need a witness of that? It need not, and there is a switch. <code>Classical.propDecidable</code> is a value of <code>Decidable p</code> for every <code>p</code> whatever, and <code>open Classical</code> puts it where instance search will find it. Then <code>if</code> works on anything, including the equality of two functions.'},
       {t:'code', tag:'sketch', src:'open Classical in\ndef pickC (P : Prop) (a b : Nat) : Nat := if P then a else b'},
       {t:'state', cap:'The price, stated by Lean in one word.',
        src:'error: failed to compile definition, consider marking it as \'noncomputable\' because it depends on \'propDecidable\', which is \'noncomputable\''},
       {t:'p', h:'A classical verdict has no way to produce its evidence, so a definition that consumes one cannot be run. Marking it <code>noncomputable</code> makes it legal and keeps it un-runnable. For this course that is a real loss: <code>#eval</code> on a heap literal is how the model gets checked against intuition throughout Module 1, and an interpreter that cannot execute is not an interpreter. Keeping <code>Loc</code> decidable is what keeps every definition in the course a program.'},
       {t:'p', h:'It costs something too, and the bill arrives in the next unit. Every proof about a heap has to dispose of a conditional whose test is a proposition about variables, and Lean will not do that silently: the case split has to be performed by hand, on the page, in every proof that touches a heap literal.'}
     ]},

    /* ------------------------------------------------- cases hl : --- */

    {t:'sec', s:'Splitting on a value'},

    {t:'p', h:'Here is the situation the rest of this course is made of. You hold a heap <code>h</code> and a location <code>l</code>, and you know something about <code>h l</code> — that it is not <code>none</code>, say. You want to name the value it holds. But <code>h l</code> is neither <code>none</code> nor <code>some v</code> for any <code>v</code> you can name: <code>h</code> is a variable, so nothing reduces, and both of <code>Option</code>\'s constructors are still on the table. What you need is a case split on the <i>value of an expression</i>, and <code>cases</code> does that as well as splitting hypotheses. Its syntax carries one piece that is easy to leave out and costly when you do: writing <code>cases hl : h l with</code> — a name and a colon before the expression — records in each branch an equation saying which case that branch is. Writing <code>cases h l with</code> does not.'},

    {t:'cmp',
     left:{t:'cases hl : h l with', kind:'good', tag:'sketch',
           h:'The <code>some</code> branch. <code>v</code> arrives with <code>hl : h l = some v</code> beside it, and that equation is the only thing connecting <code>v</code> to the heap you started with. In the other branch the same equation contradicts <code>hne</code>; in this one, <code>⟨v, hl⟩</code> is already a proof.',
           src:'case some\nh : Heap\nl : Loc\nhne : h l ≠ none\nv : Val\nhl : h l = some v\n⊢ defined h l'},
     right:{t:'cases h l with', tag:'sketch',
            h:'The same branch without the equation. <code>v</code> is a value out of nowhere: nothing in the context says it has anything to do with <code>h</code>, or with <code>l</code>. The goal did not change either, because the split had no term in it to rewrite. This branch is unprovable, and the reason is not visible in the tactic that caused it.',
            src:'case some\nh : Heap\nl : Loc\nhne : h l ≠ none\nv : Val\n⊢ defined h l'}},

    {t:'p', h:'The right-hand context is a very common way to get stuck, and it takes a while to recognise because everything in it looks reasonable. The tell is a hypothesis or a goal that still mentions <code>h l</code> while the branch you are in is supposedly the <code>some</code> branch: the split told you which case you were in and then threw the note away. One definition to prove it on — the first predicate in this course about a heap rather than about a number, saying what "this address holds something" means.'},

    {t:'code', tag:'verified', src:'def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v'},

    {t:'ex',
     id:'x09',
     name:'defined_of_ne_none',
     hard:false,
     why:'The saved equation is the most-forgotten piece of syntax in this course, and the cost of forgetting it is a branch that looks provable and is not. From Unit 09 onwards the pattern here — split on a lookup, kill the <code>none</code> branch with a contradiction, produce a witness in the <code>some</code> branch — opens a large fraction of every proof about disjointness and union. This is that pattern at its smallest.',
     setup:'<code>def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v</code> is in scope, and unfolds definitionally, so a <code>⟨…⟩</code> may be given for it directly. You have <code>hne : h l ≠ none</code>. Two branches: one is a contradiction, the other is a witness.',
     goal:'theorem defined_of_ne_none (h : Heap) (l : Loc) (hne : h l ≠ none) : defined h l := by',
     hints:[
       'The goal is <code>∃ v, h l = some v</code> written under a name. You are given that <code>h l</code> is not <code>none</code>. Nothing about <code>h l</code> reduces, because <code>h</code> is a variable.',
       'There are two things <code>h l</code> can be. If it is <code>none</code>, the hypothesis you were handed says that cannot happen. If it is <code>some</code> of something, that something is the witness the goal is asking for. So: split, discharge one branch by contradiction, supply the other.',
       'The tactic is <code>cases</code> applied to the expression <code>h l</code>, in the <code>with | none =&gt; … | some v =&gt; …</code> form — and it must be written so that each branch records the equation it stands for. In the <code>none</code> branch, <code>absurd</code> takes that equation and <code>hne</code>. In the <code>some</code> branch the equation is already the second half of the pair you owe.',
       'Open with <code>cases hl : h l with</code>. The <code>none</code> branch then holds <code>hl : h l = none</code> against <code>hne : h l ≠ none</code>, so <code>exact absurd hl hne</code>. The <code>some</code> branch holds <code>v : Val</code> and <code>hl : h l = some v</code>, so the pair is <code>⟨v, hl⟩</code>.'
     ],
     sol:'theorem defined_of_ne_none (h : Heap) (l : Loc) (hne : h l ≠ none) : defined h l := by\n  cases hl : h l with\n  | none   => exact absurd hl hne\n  | some v => exact ⟨v, hl⟩',
     solNote:'Four lines, three of them the case analysis. The proof proper is <code>⟨v, hl⟩</code>.',
     expl:'The whole proof is the observation that <code>Option</code> has two constructors and that the hypothesis rules one of them out. What makes it work rather than nearly work is the <code>hl :</code>, which turns "I am in the <code>some</code> branch" from a fact about the proof tree into a hypothesis you can hand to <code>absurd</code> and to <code>⟨…⟩</code>.',
     walk:[
       {tac:'cases hl : h l with', h:'Replaced one goal by two, one per constructor of <code>Option</code>, and added to each an equation named <code>hl</code> saying what <code>h l</code> is in that branch. The goal <code>defined h l</code> is untouched in both — the split was on an expression, not on the goal.'},
       {tac:'| none   => exact absurd hl hne', h:'In this branch <code>hl : h l = none</code> and <code>hne : h l ≠ none</code>, which are a proposition and its negation. <code>absurd hl hne</code> has whatever type is asked for, so it closes a goal that nothing else in this branch could reach.'},
       {tac:'| some v => exact ⟨v, hl⟩', h:'In this branch <code>hl : h l = some v</code>. The goal unfolds to <code>∃ w, h l = some w</code>; the witness is <code>v</code> and the proof that it works is <code>hl</code> itself. <code>exact</code> accepts the pair because <code>defined h l</code> and the existential are definitionally equal — the notion this page opened with, doing a job.'}
     ],
     deep:[
       {t:'trace', title:'Both branches, as Lean prints them',
        start:'h : Heap\nl : Loc\nhne : h l ≠ none\n⊢ defined h l',
        steps:[
          {tac:'cases hl : h l with',
           state:'case none\nh : Heap\nl : Loc\nhne : h l ≠ none\nhl : h l = none\n⊢ defined h l',
           h:'The first of the two goals. <code>hl</code> is the saved equation, and in this branch it says the thing <code>hne</code> denies.'},
          {tac:'exact absurd hl hne',
           state:'case some\nh : Heap\nl : Loc\nhne : h l ≠ none\nv : Val\nhl : h l = some v\n⊢ defined h l',
           h:'The first goal is gone and the second is on display. <code>v</code> has appeared, and so has the equation tying it to <code>h l</code> — without which <code>v</code> would be an unrelated value of the right type.'},
          {tac:'exact ⟨v, hl⟩',
           state:'No goals.',
           h:'The pair is accepted against <code>defined h l</code> with no <code>unfold</code> and no <code>show</code>, because <code>exact</code> unfolds definitions while it checks.'}
        ]},
       {t:'p', h:'What the same proof looks like when the equation is dropped, with the two errors it produces:'},
       {t:'code', tag:'sketch', src:'example (h : Heap) (l : Loc) (hne : h l ≠ none) : defined h l := by\n  cases h l with\n  | none   => exact absurd rfl hne\n  | some v => exact ⟨v, rfl⟩'},
       {t:'state', cap:'Two failures, one per branch, and neither mentions the missing <code>hl :</code>. Both are complaints about <code>rfl</code>, because <code>rfl</code> is what a reader reaches for when the equation they needed is not in the context.',
        src:'error: Application type mismatch: The argument\n  hne\nhas type\n  h l ≠ none\nbut is expected to have type\n  ¬?m.28 = ?m.28\nin the application\n  absurd rfl hne\n\nerror: Application type mismatch: The argument\n  rfl\nhas type\n  ?m.42 = ?m.42\nbut is expected to have type\n  h l = some v\nin the application\n  Exists.intro v rfl'}
     ],
     pitfall:'Swapping the arguments of <code>absurd</code>. It takes the proof first and the negation second, and <code>exact absurd hne hl</code> reports that <code>hl</code> has type <code>h l = none</code> but is expected to have type <code>¬h l ≠ none</code> — a doubled negation that appears nowhere in your proof and is Lean unifying <code>P</code> with <code>h l ≠ none</code>. When an <code>absurd</code> error mentions a negation you did not write, the arguments are the wrong way round.',
     variants:'Drop <code>hne</code> and the theorem is false, at one witness: <code>fun _ =&gt; none</code>, the heap that is defined nowhere, for which <code>¬ defined (fun _ =&gt; none) l</code> is provable at every <code>l</code>. The collapse is visible in the proof rather than in the statement — the <code>some</code> branch still goes through unchanged, and it is the <code>none</code> branch that is left holding <code>hl : h l = none</code> and a goal it cannot reach, with nothing to contradict. Reverse the hypothesis to <code>none ≠ h l</code> instead and the statement stays true while the proof breaks, at <code>absurd hl hne</code>, with <code>hne has type none ≠ h l but is expected to have type ¬h l = none</code>. Those are two different terms and Lean will not turn one into the other on its own; the repair is to flip one of them, and the next unit gives you the lemma that does it. Replace the conclusion by <code>∃ v, h l = some v</code> written out and the proof is unchanged to the character, because that is what it always was.'
    },

    /* -------------------------------------------------------- close --- */

    {t:'dod', h:'You can read an <code>inductive</code> declaration and say what builds the type and what does not. You can classify an equation before running Lean: <code>rfl</code> if both sides reduce to the same term, something else if a variable sits where a definition wants to take cases, and something else again if the definition in the way is a plain <code>def</code> — in which case you name it, with <code>simp [f]</code> or <code>unfold f</code>, or you declare it <code>abbrev</code> as this course\'s model is declared. You can use an equation you cannot compute with — <code>rw</code> in either direction, in the goal or in a hypothesis, with its silent trailing <code>rfl</code> — and lay a chain of them out as <code>calc</code>. You can restate a goal with <code>show</code>, name a fact with <code>have</code>, unfold by name, and choose between <code>simp</code> and <code>simp only</code> for a reason. You know that <code>some</code> is injective and that <code>some v</code> is not <code>none</code>, and you can close an impossible branch with <code>absurd</code>. And you can split on the value of a lookup and keep the equation that says which branch you are in.'},

    {t:'p', h:'<code>Heap</code> is a type now, and it has no operations. The smallest useful one changes what is stored at one address and leaves every other address alone — and writing it will show you that <code>rfl</code> was never going to be enough here, because two heaps are two <i>functions</i>, and nothing on this page can prove two functions equal.'}

  ]
});
