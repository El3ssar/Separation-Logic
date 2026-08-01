registerChapter({
  id: 'aliasing',
  num: '00',
  phase: 'Phase 0 · Getting started',
  title: 'The rule that is false',
  blurb: 'A rule about memory that looks like bookkeeping and is not sound, the repair everyone reaches for, and what that repair costs.',

  /* Named once, by name, in the promissory note: the theorem this course is
     built to reach uses vocabulary from Units 07, 12, 18 and 22. */
  ledgerForward: ['Hoare', 'ptsAtLeast', 'aAnd', 'star'],

  /* The promissory note is quoted verbatim from Unit 28 and the page says in so
     many words that it cannot be read yet. Waived by name, never wholesale. */
  ledgerAllow: ['∀', 'leading-dot name resolution (.ctor)', 'Hoare', 'ptsAtLeast', 'aAnd'],

  orient: {
    youWill: [
      'Say why the innocent-looking rule <code>{[x]=3} [y]:=5 {[x]=3 ∧ [y]=5}</code> is unsound, and exhibit the state that breaks it.',
      'Write a heap in Lean as a function, and prove what it holds at an address.',
      'Read a <code>theorem</code> header and name its four parts.',
      'Read a goal display: the hypotheses above the <code>⊢</code>, the goal below it.',
      'Drive two tactics, <code>intro</code> and <code>simp</code>, and interpret both a success and a failure.',
      'Say why adding disequality hypotheses repairs the rule, and why the repair cannot be used.'
    ],
    needs: [
      'Functions, and the difference between a function and its values.',
      '<code>∧ ¬ → ∀ ∃</code> as notation, and what a counterexample is.',
      'A browser. No Lean installation, no prior proof assistant, no separation logic.'
    ],
    payoff: 'The problem posed here is the one the next twenty-eight units solve; the last theorem of Unit 28 is the one written down, unproved, at the bottom of this page.'
  },

  blocks: [

    /* ---------------------------------------------------------- the rule --- */

    {t:'p', h:'Here is a rule about programs. It is the kind of rule a logic of programs is made of, it is the kind of rule nobody stops to check, and it is false. Write <code>[x]</code> for the contents of the memory cell whose address is held in the program variable <code>x</code>. The rule says that assigning to one cell leaves what you knew about another cell intact.'},

    {t:'txt', cap:'A <b>Hoare triple</b>: assume the left, run the middle, conclude the right. The precise definition is built in Unit 22; the reading is all you need here.',
     src:'{ [x] = 3 }        [y] := 5        { [x] = 3  ∧  [y] = 5 }'},

    {t:'p', h:'Read it as a promise. From any state in which the precondition holds, running the command lands you in a state where the postcondition holds. It looks like bookkeeping: you knew <code>[x] = 3</code> before, the assignment did not touch <code>x</code>, so carry that fact across and add the one the assignment made true. Every clause of that is right except <i>the assignment did not touch <code>x</code></i>. Nothing in the triple says <code>x</code> and <code>y</code> hold different addresses. Let both hold 4. The command writes 5 into cell 4, and the postcondition then claims that cell 4 holds 3 and cell 4 holds 5 — so the triple promises a state that cannot exist.'},

    {t:'defn', term:'Aliasing', h:'Two syntactically different expressions denoting the same memory cell. <code>x</code> and <code>y</code> alias when they hold the same address; <code>[x]</code> and <code>[y]</code> are then one cell under two names, and any reasoning that treats them as independent is unsound.'},

    /* ----------------------------------------------------- memory as data --- */

    {t:'h3', s:'What memory has to be'},

    {t:'p', h:'“Cell 4 holds 3 and cell 4 holds 5” is absurd because a function cannot take two values at one argument. To make that argument in Lean rather than in English, memory has to be a mathematical object, and the object it wants to be is a function: address in, value out. It cannot be a <i>total</i> function. At any moment most addresses hold nothing — they have not been allocated, and reading one is an error rather than a value. Memory is a partial function from addresses to values, Lean has no primitive type of partial functions, and so the partiality has to be encoded.'},

    {t:'p', h:'The encoding used here widens the codomain: a heap is a total function whose values are either <code>some v</code>, meaning the address holds <code>v</code>, or <code>none</code>, meaning it holds nothing. The alternative is to package a domain — a set <code>D</code> of allocated addresses together with a function defined only on <code>D</code>. That is more faithful, and it is unusable here, because every heap in this course gets rewritten, split and recombined, and under the packaged encoding each of those steps drags along a proof that the address in hand is still in the domain. Widening the codomain concentrates the obligation in one place: the moment you look at a value and have to say what happens if there is none.'},

    {t:'anat', tag:'verified',
     src:'abbrev Loc   := Nat\nabbrev Val   := Nat\nabbrev Heap  := Loc → Option Val\nabbrev Var   := Nat\nabbrev Store := Var → Val',
     parts:[
       {m:'abbrev', h:'Names a type, transparently: Lean unfolds the name whenever it needs to, so <code>Heap</code> and <code>Loc → Option Val</code> are interchangeable everywhere and no step of any proof is spent converting between them. <code>def</code> would make the name opaque, and you would pay for that on every line.'},
       {m:'Loc   := Nat', h:'Addresses are natural numbers. That is a modelling decision with one technical consequence, met properly in Unit 02: <code>Nat</code> has decidable equality, which is what lets Lean actually run a test like <code>x = 4</code>.'},
       {m:'Loc → Option Val', h:'The type of functions from <code>Loc</code> to <code>Option Val</code>. <code>→</code> is the function arrow; you type it <code>\\to</code>.'},
       {m:'Option Val', h:'Either <code>some v</code> for a value <code>v</code>, or <code>none</code>. This is the widened codomain, and it is why a heap can be a total function and still describe a partial one.'},
       {m:'Store', h:'Program variables are a different thing from memory. In <code>[x] := 5</code> the variable <code>x</code> lives in the store; the cell it names lives in the heap. The store is total — every variable has a value, and none of them can be deallocated. The two are kept apart because only one of them is a resource that can be owned in pieces.'}
     ]},

    {t:'svg', cap:'The set of addresses where <code>h</code> is <code>some</code> — its domain of definition — is the part to watch. Everything this course does to memory is done to that set.',
     src:'\n<svg viewBox="0 0 560 168" role="img" aria-label="A heap is a partial function from locations to values">\n  <g class="dg">\n    <text x="8" y="18" class="dg-lab">locations (Nat)</text>\n    <text x="392" y="18" class="dg-lab">values (Nat)</text>\n    <g class="dg-dot">\n      <circle cx="60" cy="46" r="5"/><text x="26" y="51" class="dg-t">0</text>\n      <circle cx="60" cy="80" r="5"/><text x="26" y="85" class="dg-t">1</text>\n      <circle cx="60" cy="114" r="5"/><text x="26" y="119" class="dg-t">2</text>\n      <circle cx="60" cy="148" r="5"/><text x="26" y="153" class="dg-t">3</text>\n    </g>\n    <g class="dg-dot">\n      <circle cx="470" cy="60" r="5"/><text x="486" y="65" class="dg-t">7</text>\n      <circle cx="470" cy="110" r="5"/><text x="486" y="115" class="dg-t">4</text>\n    </g>\n    <path class="dg-arr" d="M66 80 C 200 80, 340 60, 464 60"/>\n    <path class="dg-arr" d="M66 148 C 200 148, 340 112, 464 110"/>\n    <text x="130" y="42" class="dg-note">h 0 = none  (unallocated)</text>\n    <text x="130" y="128" class="dg-note">h 1 = some 7  (allocated)</text>\n  </g>\n</svg>'},

    /* --------------------------------------------------- writing one down --- */

    {t:'code', tag:'verified', cap:'The memory left behind by <code>[y] := 5</code> when <code>y</code> holds 4 and nothing else has been allocated: one cell, one value.',
     src:'def aliasedAfter : Heap := fun x => if x = 4 then some 5 else none'},

    {t:'p', h:'<code>def</code> introduces a definition: a name, its type after the colon, and after <code>:=</code> the thing the name stands for. <code>fun x => …</code> is Lean\'s lambda — the function sending <code>x</code> to the body. Read the body as a two-row table: address 4 holds 5, every other address holds nothing. Two commands interrogate a definition without proving anything about it, and a third asks for a proof.'},

    {t:'code', tag:'illustration',
     src:'#check aliasedAfter\n#eval aliasedAfter 4\n#eval aliasedAfter 7\n\nexample : aliasedAfter 4 = some 5 := by\n  simp [aliasedAfter]'},

    {t:'state', cap:'Everything Lean printed. The <code>example</code> printed nothing, which is what success looks like.',
     src:'aliasedAfter : Heap\nsome 5\nnone'},

    {t:'p', h:'<code>#check</code> answers with a type; <code>#eval</code> runs a computation and answers with a value. But <code>#eval</code> computed and did not prove: <code>aliasedAfter 7</code> reduced to <code>none</code> inside Lean\'s evaluator, the answer was printed and forgotten, and no theorem exists afterwards for anything else to use. <code>example : S := p</code> is the smallest way to ask for the other thing — <i>here is a proof <code>p</code> of the statement <code>S</code></i>, with no name attached. <code>:= by</code> says the proof is not written out directly but assembled by <b>tactics</b>, instructions that change the goal until there is no goal left.'},

    {t:'p', h:'There is one tactic here. <code>simp</code> simplifies, and the bracketed list names the definitions it is allowed to unfold: <code>simp [aliasedAfter]</code> replaces <code>aliasedAfter 4</code> by <code>if 4 = 4 then some 5 else none</code>, settles <code>4 = 4</code>, takes the <code>then</code> branch, and is left with <code>some 5 = some 5</code>, which it closes. Every code block on this page is editable, and <b>Check</b> runs a real Lean kernel on what you typed: success is a green tick, failure is Lean\'s own message with a line and a column, reproduced without editing. There is a real one further down.'},

    {t:'tbl', cap:'Type the backslash form followed by a space, or pick the glyph from the palette above the editor. The last two are here so your fingers know them before the mathematics arrives.',
     head:['type this', 'and you get', 'what it is for'],
     rows:[
       ['<code>\\to</code>', '<code>→</code>', 'the function arrow'],
       ['<code>\\forall</code>', '<code>∀</code>', 'for all'],
       ['<code>\\exists</code>', '<code>∃</code>', 'there exists'],
       ['<code>\\and</code>', '<code>∧</code>', 'and'],
       ['<code>\\not</code>', '<code>¬</code>', 'not'],
       ['<code>\\ne</code>', '<code>≠</code>', 'not equal'],
       ['<code>\\vdash</code>', '<code>⊢</code>', 'the turnstile Lean prints in front of a goal'],
       ['<code>\\mapsto</code>', '<code>↦</code>', 'the ownership arrow, from Unit 13'],
       ['<code>\\star</code>', '<code>∗</code>', 'the connective this course is about, from Unit 14']
     ]},

    {t:'txt', cap:'Your turn: a heap of your own, and a lookup at an address it does not allocate. <code>sorry</code> is Lean\'s placeholder — it makes any goal go away and marks the result unproved. It is here so that you have something to replace, and it appears nowhere else in this course.',
     src:'def twoAllocated : Heap := sorry\n\nexample : twoAllocated 7 = none := by\n  sorry'},

    {t:'ex',
     id:'x01',
     name:'write a heap, prove a lookup',
     why:'A heap is not an abstract gadget: it is a function you can type out, and every theorem about memory in this course is ultimately a theorem about functions like this one. Writing your own is also the fastest way to find out whether the <code>Option</code> encoding has landed, because an address that holds nothing must get <code>none</code> and not <code>some 0</code>.',
     setup:'Define <code>twoAllocated</code> above the <code>example</code>. It must allocate cells 4 and 9 and nothing else; the values it stores there are yours to choose. Then prove the lookup.',
     goal:'example : twoAllocated 7 = none := by',
     hints:[
       'The goal is an equation between two values of type <code>Option Val</code>. On the left, your function applied to 7. On the right, <code>none</code>. There are no hypotheses — nothing is being assumed, so nothing has to be used.',
       'Your function is a two-row table with a default underneath. Applied to 7 it matches neither row, so it falls through to the default, and the default is “unallocated”. The whole content of the proof is that 7 is neither 4 nor 9.',
       'One tactic, the same one that closed <code>aliasedAfter 4 = some 5</code> above. It unfolds a definition and evaluates the conditionals — but only for definitions you name in its bracketed list, so it has to be told what you called your heap.',
       'Write <code>simp [twoAllocated]</code>, substituting whatever name you gave the definition. It unfolds it, decides <code>7 = 4</code> and <code>7 = 9</code> to be false, takes the <code>else</code> branch twice, and is left with <code>none = none</code>, which it closes. Nothing remains after it.'
     ],
     sol:'def twoAllocated : Heap := fun x => if x = 4 then some 5 else if x = 9 then some 2 else none\n\nexample : twoAllocated 7 = none := by\n  simp [twoAllocated]',
     solNote:'Any heap allocating exactly 4 and 9 is correct, with any values in them and the conditionals in either order. The editor checks your text, not this one.',
     expl:'A finite partial function written in Lean is a nested conditional with <code>none</code> at the bottom. The <code>none</code> is not a special case bolted on at the end; it is the value the function takes everywhere the table says nothing, which is almost everywhere.',
     walk:[
       {tac:'def twoAllocated : Heap := fun x => if x = 4 then some 5 else if x = 9 then some 2 else none',
        h:'Introduces the function. The nested <code>if</code>s enumerate the allocated addresses; the final <code>else none</code> covers the infinitely many that are not. Because <code>Heap</code> is an <code>abbrev</code>, Lean accepts a plain function here with no conversion step in between.'},
       {tac:'simp [twoAllocated]',
        h:'Replaces <code>twoAllocated 7</code> by the body with <code>x</code> set to 7, then decides both conditions. <code>7 = 4</code> is false, so the outer <code>if</code> collapses to its <code>else</code>; <code>7 = 9</code> is false, so the inner one collapses too. The goal becomes <code>none = none</code>, and <code>simp</code> closes that, which is why no second tactic is needed.'}
     ],
     deep:[
       {t:'trace', title:'x01, tactic by tactic',
        start:'⊢ twoAllocated 7 = none',
        steps:[
          {tac:'simp [twoAllocated]', state:'No goals.',
           h:'One tactic does the unfolding, two decisions and the final equality. Later you will separate those jobs on purpose, because when a proof fails you need to know which of them failed.'}
        ]},
       {t:'p', h:'The same definition answers at the addresses it does allocate, by the same single tactic:'},
       {t:'code', tag:'illustration',
        src:'example : twoAllocated 4 = some 5 := by\n  simp [twoAllocated]\n\nexample : twoAllocated 9 = some 2 := by\n  simp [twoAllocated]'}
     ],
     pitfall:'Writing <code>else some 0</code> for the unallocated case. It type-checks, and it is a different heap: it allocates every address in memory and stores 0 in almost all of them. Then <code>twoAllocated 7 = none</code> is false and no tactic will prove it. “Holds nothing” is <code>none</code>; “holds zero” is <code>some 0</code>; keeping those apart is the entire reason for the <code>Option</code>.',
     variants:'Ask instead for <code>twoAllocated 4 = none</code> and the statement is false — <code>simp</code> reduces it to <code>some 5 = none</code> and stops, leaving that on screen as an unsolved goal. Leave <code>twoAllocated</code> out of the bracket and write bare <code>simp</code>: the definition is never unfolded, Lean reports that <code>simp</code> made no progress, and the goal is untouched. That message is worth provoking once, because it marks the difference between a tactic that failed and a tactic that was not given what it needed.'
    },

    /* ----------------------------------------------------- the refutation --- */

    {t:'h3', s:'The refutation'},

    {t:'p', h:'Now the argument from the top of the page, in Lean. <code>aliasedAfter</code> is the memory the command actually produces, so it is where the aliased postcondition should be tested — and no memory satisfies that postcondition, this one included. Saying <i>this cannot hold</i> needs negation. In Lean <code>¬ P</code> is notation for <code>P → False</code>: to deny <code>P</code> is to supply a procedure turning a proof of <code>P</code> into a proof of the absurd. That reading is what makes a refutation mechanical — you assume the thing you are denying, and work forwards.'},

    {t:'code', tag:'sketch', cap:'One tactic short of a proof. Supplying the missing line is the exercise below.',
     src:'example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by\n  intro ⟨h3, _⟩'},

    {t:'p', h:'<code>intro</code> is the tactic for an arrow: it moves the antecedent into your hypotheses and leaves the consequent as the goal. Since <code>¬ P</code> <i>is</i> <code>P → False</code>, running <code>intro</code> here assumes the conjunction and leaves <code>False</code> to be proved. The pattern <code>⟨h3, _⟩</code> takes the conjunction apart on the way in: the first component is named <code>h3</code>, and <code>_</code> says the second is not wanted.'},

    {t:'trace', title:'The first goal state you will read',
     start:'⊢ ¬(aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5)',
     steps:[
       {tac:'intro ⟨h3, _⟩',
        state:'h3 : aliasedAfter 4 = some 3\nright✝ : aliasedAfter 4 = some 5\n⊢ False',
        h:'The conjunction has moved above the line and split in two; the goal below the line is now <code>False</code>.'}
     ]},

    {t:'p', h:'Above the <code>⊢</code> is the context — named facts you may use. Below it is the goal. <code>right✝</code> is the component you declined to name: Lean invented a name from the field the hypothesis came out of and marked it with a dagger to say the name is not yours to type. What is left is to derive <code>False</code> from <code>h3</code>, which is wrong on its face, because <code>aliasedAfter 4</code> is <code>some 5</code>. The tactic that says so is the one you have, aimed differently: <code>simp [f] at h</code> does to the hypothesis <code>h</code> what <code>simp [f]</code> does to a goal. When a hypothesis simplifies all the way to <code>False</code>, Lean uses it to close whatever goal was standing.'},

    {t:'ex',
     id:'x02',
     name:'the aliased postcondition is unsatisfiable',
     why:'This is the shard of the aliasing problem that can be stated on day one, and proving it yourself is the difference between a counterexample you were shown and a counterexample you own. It also draws the distinction the rest of the course depends on: the aliased rule is not unproved, it is <i>false</i>, and a false rule is not repaired by working harder on its proof.',
     setup:'You are given the statement and the first tactic. Add the second. <code>aliasedAfter</code> is the one-cell heap defined above.',
     goal:'example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by\n  intro ⟨h3, _⟩',
     hints:[
       'After <code>intro ⟨h3, _⟩</code> the goal is <code>False</code> and the context holds <code>h3 : aliasedAfter 4 = some 3</code>. You are not being asked to prove anything about memory in general — only that this one hypothesis, about this one heap, cannot be true.',
       'Compute the left-hand side of <code>h3</code>. <code>aliasedAfter</code> at address 4 is <code>some 5</code>, so <code>h3</code> asserts <code>some 5 = some 3</code>. Two different values wrapped the same way are different, so <code>h3</code> is itself absurd — and from an absurd hypothesis anything follows, the goal included.',
       'The work happens in the hypothesis, not in the goal. <code>simp</code> can be aimed at a hypothesis; it needs the name of the definition it may unfold, and the name of the hypothesis to work on.',
       'Write <code>simp [aliasedAfter] at h3</code>. It unfolds the definition inside <code>h3</code>, evaluates <code>if 4 = 4 then some 5 else none</code> to <code>some 5</code>, reduces <code>some 5 = some 3</code> to <code>False</code>, and — finding a hypothesis that has become <code>False</code> — closes the goal. There is no third line.'
     ],
     sol:'example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by\n  intro ⟨h3, _⟩\n  simp [aliasedAfter] at h3',
     solNote:'Four hints and still stuck is not a failure; reading a finished proof and retyping it from memory is a legitimate way to learn this. It stops being legitimate around Unit 04.',
     expl:'The proof never mentions the second conjunct. One of the two claims is already false about <code>aliasedAfter</code>, so the conjunction is false and its negation is true. That is why <code>_</code> was an honest thing to write in the <code>intro</code> pattern: the second component is genuinely unused.',
     walk:[
       {tac:'intro ⟨h3, _⟩',
        h:'Turns the goal <code>¬ (A ∧ B)</code> into <code>False</code> and puts <code>A</code> and <code>B</code> into the context, since <code>¬ P</code> unfolds to <code>P → False</code>. The angle brackets split the conjunction as it arrives, so you get two separate hypotheses rather than one conjunctive one; <code>h3</code> is the first, and the second is left anonymous.'},
       {tac:'simp [aliasedAfter] at h3',
        h:'Rewrites <b>inside <code>h3</code></b> rather than in the goal. Unfolding <code>aliasedAfter</code> turns the left-hand side into a conditional; the condition <code>4 = 4</code> is true, so that side becomes <code>some 5</code> and <code>h3</code> becomes <code>some 5 = some 3</code>. Distinct values under <code>some</code> are distinct, so <code>h3</code> collapses to <code>False</code> — and a hypothesis that is <code>False</code> discharges any goal, so nothing is left to do.'}
     ],
     deep:[
       {t:'trace', title:'x02, tactic by tactic',
        start:'⊢ ¬(aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5)',
        steps:[
          {tac:'intro ⟨h3, _⟩',
           state:'h3 : aliasedAfter 4 = some 3\nright✝ : aliasedAfter 4 = some 5\n⊢ False',
           h:'Assume what is being denied. Both conjuncts land in the context; the goal becomes the absurd.'},
          {tac:'simp [aliasedAfter] at h3',
           state:'No goals.',
           h:'The hypothesis, not the goal, is what gets simplified — and it simplifies to <code>False</code>, which ends the proof.'}
        ]},
       {t:'p', h:'Two facts about <code>Option</code> do the arithmetic in that last step, and both get proper treatment in Unit 02: <code>some</code> is injective, so <code>some 5 = some 3</code> forces <code>5 = 3</code>; and <code>5 = 3</code> is decidably false. <code>simp</code> performs both without being asked, which is convenient now and worth distrusting later, when the goals stop being about literals.'}
     ],
     pitfall:'Aiming the tactic at the goal: <code>simp [aliasedAfter]</code> with no <code>at h3</code>. The goal is <code>False</code>, there is nothing in it to simplify, and Lean answers <code>simp made no progress</code> — an error, not a hint, so the proof stops there. The whole content of this exercise is the direction of the work: the contradiction lives in the context, so the tactic has to be pointed at the context.',
     variants:'Change <code>some 3</code> to <code>some 5</code> and the statement becomes false: the conjunction is then satisfied by <code>aliasedAfter</code>, which is exactly the case where <code>x</code> and <code>y</code> do not alias and the triple is sound. Change the address in the first conjunct from 4 to 7 and the statement stays true for a different reason — <code>aliasedAfter 7</code> is <code>none</code>, so <code>h3</code> becomes <code>none = some 3</code>, false because the two constructors of <code>Option</code> are distinct rather than because two values differ. Drop the negation and you are asked to <i>prove</i> the conjunction, which no tactic can do, because it is not true.'
    },

    /* --------------------------------------------------------- the repair --- */

    {t:'h3', s:'The repair everyone reaches for'},

    {t:'p', h:'The triple is not beyond saving. It fails in exactly one circumstance — when <code>x</code> and <code>y</code> hold the same address — so add the hypothesis that they do not, and the rule becomes sound. Here is the same move one level down, at the model rather than at the program: a lookup in <code>aliasedAfter</code> at any address other than 4 gives <code>none</code>, and the disequality is a hypothesis of the theorem.'},

    {t:'anat', tag:'illustration',
     src:'theorem lookup_of_unallocated (x : Loc) (hx : x ≠ 4) : aliasedAfter x = none := by\n  simp [aliasedAfter, hx]',
     parts:[
       {m:'theorem', h:'The keyword, and the first of the four parts of a header. A <code>theorem</code> is an <code>example</code> with a name, and the name is how every later proof refers to it.'},
       {m:'lookup_of_unallocated', h:'The name — part two. Names in this course are meant to be read as sentences: this one says <i>lookup, at an address that is not allocated</i>.'},
       {m:'(x : Loc)', h:'Part three: the binders, between the name and the colon. This one is an ordinary argument — to use the theorem you supply an address. Read it as <i>for every <code>x</code> of type <code>Loc</code></i>.'},
       {m:'(hx : x ≠ 4)', h:'A binder whose type is a proposition, so the argument you supply for it is a <i>proof</i>. Hypotheses and arguments are the same thing in Lean; that identification is the subject of Unit 01, and it is why a theorem with a side condition looks like a function with an extra parameter.'},
       {m:'aliasedAfter x = none', h:'Part four: the statement, everything after the last colon. It is what you are left holding once every binder has been supplied.'},
       {m:'simp [aliasedAfter, hx]', h:'<code>hx</code> is in the bracketed list; being in the context is not enough. That is what lets <code>simp</code> rewrite the condition <code>x = 4</code> to <code>False</code>, collapse the conditional to its <code>else</code> branch, and finish. A hypothesis sitting in the context that <code>simp</code> was not told about is a hypothesis <code>simp</code> will not use.'}
     ]},

    {t:'p', h:'Keyword, name, binders, statement: every declaration from here to the end of the course has that shape, and reading one means finding the last colon before the <code>:=</code> and taking what follows as the claim. In this one <code>hx</code> is not decoration, it is the entire content. Delete it and the claim is false, because <code>x</code> could be 4 — and Lean, asked to prove the deleted version, says something more useful than “no”.'},

    {t:'code', tag:'sketch', cap:'The same theorem with the disequality removed.',
     src:'theorem bad (x : Loc) : aliasedAfter x = none := by\n  simp [aliasedAfter]'},

    {t:'state', cap:'A real message, produced by deleting <code>hx</code> and pressing Check.',
     src:'error: unsolved goals\nx : Loc\n⊢ ¬x = 4'},

    {t:'p', h:'Read the residue rather than the word “error”. <code>simp</code> did everything it could and came to rest at <code>⊢ ¬x = 4</code>: it has reduced the entire theorem to the one fact it was not given. Lean is telling you what it is owed. This is the most common shape of failure in the first half of this course — a proof complete except for a claim that two addresses are different — and the habit of reading a leftover goal as a bill rather than as a rejection is worth forming now.'},

    /* ---------------------------------------------------------- the cost --- */

    {t:'h3', s:'What the repair costs'},

    {t:'p', h:'Adding disequality hypotheses works. Classical Hoare logics for languages with pointers do exactly this, and the resulting rules are sound. The damage is not to soundness; it is to specifications. Take a routine that swaps the contents of two cells. Its honest description mentions two addresses. To be usable inside a program that also maintains a linked list, a counter and a buffer, its specification must further say that those two addresses differ from every address the rest of the program is using — and it must say so before anyone knows what the rest of the program is. So the specification of a routine that touches two cells now mentions memory the routine never reads and never writes; it has to be rewritten every time a caller allocates anything new; and with <code>n</code> live cells it carries on the order of <code>n²</code> side conditions, not one of which is about swapping. That is the failure, and it is worth being exact about which failure it is. Nothing here is unsound. What is lost is modularity: a specification you cannot write down without knowing the whole program is not a specification.'},

    {t:'cmp',
     left:{t:'Carry non-aliasing as hypotheses', kind:'bad',
           h:'The swap routine is specified against a precondition naming every other live address, with a disequality for each. Sound, and mechanical. The specification grows with the caller, so it cannot be written before the caller exists, and it changes when the caller changes.'},
     right:{t:'Change what an assertion means', kind:'good',
            h:'An assertion stops saying <i>this is true of memory</i> and starts saying <i>this is the memory I own</i>. Combining two assertions then demands that their memories be disjoint, non-aliasing becomes a consequence of the combination instead of a hypothesis dragged along, and the specification of the swap routine mentions two cells and stops.'}},

    {t:'p', h:'The right-hand column is one sentence, and turning it into mathematics is what the rest of the course does. The work divides cleanly. Memory has to become an object that can be split into disjoint pieces and put back together; the connectives of the logic have to be defined in terms of that splitting; a language and a semantics have to exist before there are programs to reason about; and then one theorem has to be proved — that a command correct on the memory it owns stays correct in the presence of any other memory. That theorem is the frame rule, and it is not an axiom here. It is proved, in Unit 27, from a property of how commands run.'},

    /* ----------------------------------------------------------- the debt --- */

    {t:'h3', s:'The statement this course exists to refute'},

    {t:'p', h:'What you proved in <code>x02</code> is a fact about <code>Option</code>. It is not a fact about Hoare logic, because there is no Hoare logic on this page for it to be a fact about: no language, no semantics, no definition of a triple. The statement genuinely worth refuting is the one below, and the honest thing to do with it now is to write it down, unproved, and leave it standing.'},

    {t:'code', tag:'sketch', cap:'Quoted from Unit 28, where it is proved. It has no proof here, and is not meant to have one.',
     src:'theorem classical_conjunction_rule_is_false :\n    ¬ (∀ (l₁ l₂ : Loc) (a b : Val),\n        Hoare (ptsAtLeast l₁ a) (.write l₂ (.const b))\n              (aAnd (ptsAtLeast l₁ a) (ptsAtLeast l₂ b)))'},

    {t:'note', kind:'key', title:'The promissory note',
     h:'You cannot read that statement yet, and nothing on this page will help you. <code>Hoare</code> is defined in Unit 22. <code>ptsAtLeast</code> is one of two competing answers to a question Unit 07 poses and Unit 13 settles — how much memory does “address <code>l</code> holds <code>a</code>” claim to own? <code>.write</code> and <code>.const</code> are constructors of a small language built in Unit 18, and <code>aAnd</code> is ordinary conjunction lifted to assertions in Unit 12. Unit 28 proves this theorem, and proves its separating replacement in four lines beside it. Everything between here and there exists to make those two theorems sayable, and you should be able to read this one unaided long before you reach it.'},

    {t:'dod', h:'You have written a heap as a function and proved a lookup about it, and you have refuted the postcondition of an aliased triple in Lean. You can read a <code>theorem</code> header and name its four parts, read a goal display and say which side of the <code>⊢</code> you are allowed to use, drive <code>intro</code> and <code>simp</code>, and read an unsolved goal as a statement of what Lean is owed. You can say why disequality hypotheses repair the aliased rule, and why that repair is one nobody can use.'},

    {t:'p', h:'That refutation is a fact about <code>Option</code>, not about Hoare logic — there is no Hoare logic here yet. Before we can even write the statement we want to refute, we need to be able to write mathematics down at all, and Lean\'s answer to what a proof is turns out to be unusually simple.'}

  ]
});
