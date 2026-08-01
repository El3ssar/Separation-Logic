registerChapter({
  id: 'update',
  num: '04',
  phase: 'Phase 0 · Getting started',
  title: 'LAB — the update family',
  blurb: 'Five theorems about changing a function at one point, proved with the tactics you already have — and one of them is the reason the frame rule will be true.',

  /* The closing paragraph is §D's contractual hook and names `emp`, which is
     Unit 13's. It is the "here is where this is going" kind of forward
     reference: the sentence says the reader has not met it, and nothing on the
     page uses it. ERRATA §10's first kind. `Heap.write` (Unit 05) is named the
     same way in the brief. */
  ledgerForward: ['emp', 'Heap.write', 'write_same', 'write_other', 'write_shadow', 'write_comm', 'write_of_eq'],

  orient: {
    youWill: [
      'Prove the four laws of <code>update</code> and name, for each <code>simp</code> call, which rewrites fired and what each one contributed.',
      'Recognise the residue <code>⊢ y = x → value = f y</code> as an undischarged disequality, and know that the hypothesis has to be handed to <code>simp</code> by name.',
      'Open an equation between two functions with <code>funext</code>, split on the point, and close both branches, without being told to.',
      'Drive a three-region case analysis by hand with <code>if_pos</code> and <code>if_neg</code>, and point at the one line that consumes the disequality.',
      'Choose between <code>simp</code> and a hand-driven <code>rw</code> by a stated rule rather than by taste.',
      'State a theorem yourself, given only what it should say in English.'
    ],
    needs: [
      'Unit 03: <code>funext</code>, <code>by_cases h : p</code> with <code>case pos</code> / <code>case neg</code>, <code>if_pos</code> / <code>if_neg</code>, <code>&lt;;&gt;</code>, <code>Ne.symm</code>.',
      'Unit 02: what blocks reduction — a variable in a position being cased on — plus <code>rw</code>, <code>unfold</code> and <code>have</code>.',
      'Unit 00: <code>simp [f]</code> and <code>simp [f, h]</code>.'
    ],
    payoff: 'Change <code>Nat → Nat</code> to a type with <code>Option</code> in the codomain and these five theorems are the first heap laws. Unit 05 proves the first two again in longer type; Unit 06 proves the last three, and two of them are these proofs line for line.'
  },

  blocks: [

    /* ------------------------------------------------------------ brief --- */

    {t:'p', h:'Here is the operation those theorems are about. <code>update f x value</code> is the function that agrees with <code>f</code> everywhere except at <code>x</code>, where it returns <code>value</code>. Four things are true of it: what you read at the point you wrote to, what you read at any other point, what two writes to the same point come to, and what two writes to different points come to in either order. You prove all four, and then state and prove a fifth from an English description. There is no new syntax on this page — every tactic these proofs need is already in your hands. That is deliberate: a page that introduces nothing is the only place where what is being measured is your own speed.'},

    {t:'p', h:'Where it is spent: change <code>Nat → Nat</code> to a function type with <code>Option</code> in the codomain and <code>update</code> becomes <code>Heap.write</code>, the operation Unit 05 opens with. Unit 05\'s six lookup laws are the first two theorems on this page in longer type, three times over; Unit 06\'s equations between heaps are the last three, two of them line for line. The type is not a toy either — <code>Store</code>, which Unit 02 gave a meaning, is <code>Var → Val</code>, and that is <code>Nat → Nat</code>. The theorems here are small. The proof shapes are not, and they do not change again.'},

    {t:'code', tag:'verified',
     cap:'The whole subject of this page. Two of the three arguments say where and what; the third is the function being changed.',
     src:'def update (f : Nat → Nat) (x value : Nat) : Nat → Nat :=\n  fun y => if y = x then value else f y'},

    {t:'anat', src:'def update (f : Nat → Nat) (x value : Nat) : Nat → Nat :=\n  fun y => if y = x then value else f y',
     parts:[
       {m:'(x value : Nat)', h:'The point being written to and the value being written. Both are fixed before the result is a function of anything: <code>update f 3 7</code> is already a complete function, waiting for a point to be read at.'},
       {m:'fun y => ', h:'The point being read at. Three of the five theorems below start by introducing this <code>y</code> with <code>funext</code>, because they are equations between two of these functions rather than between two numbers.'},
       {m:'if y = x then', h:'The condition, and its <i>orientation</i>. The read point is on the left and the write point on the right. A hypothesis <code>y ≠ x</code> matches this condition; a hypothesis <code>x ≠ y</code> is a different term and does not, which is the single commonest way these proofs fail.'},
       {m:'else f y', h:'Every point other than <code>x</code> is answered by <code>f</code> unchanged. This clause is what makes an update <i>local</i>: one address moves and no other is disturbed.'}
     ]},

    {t:'code', tag:'illustration',
     cap:'At concrete numbers there is nothing to prove: reduction decides <code>3 = 3</code> and <code>5 = 3</code> on its own, and both lines are closed by the term <code>rfl</code> with no tactic block at all.',
     src:'example : update (fun _ => 0) 3 7 3 = 7 := rfl\nexample : update (fun _ => 0) 3 7 5 = 0 := rfl'},

    /* ------------------------------------------------- the worked example --- */

    {t:'sec', s:'Worked: reading back what you wrote'},

    {t:'p', h:'The smallest claim available is that reading at the point you wrote to returns the value you wrote. The first of the two concrete lines above is an instance of it. So state it for an arbitrary point and an arbitrary value, and try the same thing that closed the instance.'},

    {t:'code', tag:'sketch', cap:'True, and a generalisation of the line <code>rfl</code> closed a moment ago. Not closable this way.',
     src:'example (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  rfl'},

    {t:'state', cap:'The <code>file:line:column</code> prefix is dropped here and everywhere on this page.',
     src:'error: Tactic `rfl` failed: The left-hand side\n  update f x value x\nis not definitionally equal to the right-hand side\n  value\n\nf : Nat → Nat\nx value : Nat\n⊢ update f x value x = value'},

    {t:'p', h:'Nothing about the lambda is responsible; this is Unit 02\'s rule, at a new place. Unfolding the definition and substituting <code>x</code> for <code>y</code> gives <code>if x = x then value else f x</code>, and there reduction stops. The <code>if</code> cannot choose a branch until something decides <code>x = x</code>, deciding an equation between two <code>Nat</code>s runs <code>Nat.decEq</code>, and <code>Nat.decEq</code> takes cases on both of its arguments. At <code>3</code> and <code>3</code> those cases run. At a variable <code>x</code> there is nothing to take cases on, and it makes no difference that the same variable stands on both sides.'},

    {t:'p', h:'Take the two steps apart, then, and watch which one is blocked. <code>unfold update</code> leaves the conditional standing in the goal, undecided, where you can look at it. <code>if_pos</code> then wants a proof of the condition — and the condition here is <code>x = x</code>, whose proof is <code>rfl</code>. So the step reduction could not take is one you can take for it, by name.'},

    {t:'code', tag:'illustration', cap:'The same theorem, with the blocked step supplied by hand.',
     src:'example (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  unfold update\n  rw [if_pos rfl]'},

    {t:'trace', title:'By hand, tactic by tactic',
     start:'f : Nat → Nat\nx value : Nat\n⊢ update f x value x = value',
     steps:[
       {tac:'unfold update',
        state:'f : Nat → Nat\nx value : Nat\n⊢ (if x = x then value else f x) = value',
        h:'The name is gone and the argument has been substituted for <code>y</code>. The conditional survives untouched, which is the point: <code>unfold</code> has done everything reduction can do here, and the goal is exactly where <code>rfl</code> gave up.'},
       {tac:'rw [if_pos rfl]',
        state:'No goals.',
        h:'<code>if_pos rfl</code> is the equation <code>(if x = x then value else f x) = value</code>, so rewriting with it turns the goal into <code>value = value</code> — and <code>rw</code>\'s silent trailing <code>rfl</code> closes that without a further line.'}
     ],
     done:'No goals.'},

    {t:'p', h:'One tactic does both steps, and this is the form the course keeps.'},

    {t:'code', tag:'verified', src:'theorem update_same (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  simp [update]'},

    {t:'p', h:'Two rewrites fired there, and the next theorem needs a third, so name them now. The first is <code>update</code>: a definition put in the brackets becomes a rewrite rule replacing the name by its body. The second is <code>↓reduceIte</code> — the arrow is part of the name — the built-in rule that collapses a conditional once its condition has been settled. Neither of those settles <code>x = x</code>; <code>simp</code> does that unprompted, because an equation with the same term on both sides is one of the facts it always carries. That is why there are two rules here and three in the next theorem, where the condition is an equation between two different variables and nothing settles it for free. Exercise <code>m0-1</code> traces the two steps with the intermediate goal printed.'},

    {t:'cmp',
     left:{t:'Reach for <code>simp</code> when…', kind:'good',
       h:'…both branches of the split want the same text, and which conditional collapsed is not part of what you are trying to show. <code>simp</code> will unfold, decide, collapse and close, and you will not be told in which order. Four of the five proofs on this page end in a single <code>simp</code> call for this reason.',
       src:'simp [update, h]'},
     right:{t:'Reach for <code>rw</code> when…',
       h:'…the <i>location</i> at which a hypothesis is used is the content. In the last proof on this page a disequality is consumed on exactly one line out of eight, and a reader who cannot point at that line has not learned the thing the proof is for. Hand-driving costs six lines and buys the ability to point.',
       src:'rw [if_neg hzy, if_pos hzx, if_pos hzx]'}},

    /* --------------------------------------------------------- exercises --- */

    {t:'sec', s:'The five'},

    {t:'ex',
     id:'m0-1',
     name:'update_same',
     hard:false,
     why:'The first of the six lookup equations that will characterise memory. Its heap form, <code>Heap.write h l v l = some v</code>, is Unit 05\'s <code>write_same</code>, and it is used in almost every proof after it. Typing it once now, having read it worked in full, is how you find out whether the pattern <code>simp [definition]</code> is yours yet.',
     setup:'The definition of <code>update</code> is in scope. The editor starts you at the statement with <code>sorry</code> in place of the proof; replace the <code>sorry</code>.',
     goal:'theorem update_same (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by',
     hints:[
       'The goal says: the function <code>update f x value</code>, applied to <code>x</code>, equals <code>value</code>. Unfolded, its left-hand side is <code>if x = x then value else f x</code>. There are no hypotheses — <code>f</code>, <code>x</code> and <code>value</code> are arbitrary.',
       'The condition is an equation between a term and itself, so it holds, so the then-branch is taken, and the then-branch is <code>value</code>. That is the entire argument: one conditional, decided, collapsed. No case split is needed because there is no case to consider.',
       'The tactic is <code>simp</code>. On its own it will not move this goal at all: <code>update</code> is a name it has no rule for, and a definition is not in its rule set unless you put it there. What goes in the brackets is the only decision left.',
       '<code>simp [update]</code>, and nothing after it. It replaces <code>update</code> by its body, reduces <code>x = x</code>, collapses the conditional to <code>value</code>, and closes <code>value = value</code>, leaving no goals.'
     ],
     sol:'theorem update_same (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  simp [update]',
     expl:'The condition is <code>x = x</code>. It is true whatever <code>x</code> is, but nothing reduces it, which is why the goal survived <code>rfl</code>. What disposes of it is a <i>proof</i> of the condition — handed over by name as <code>if_pos rfl</code>, or found by <code>simp</code>, which carries that fact without being asked. Either way there is no hypothesis to supply and no case to consider, and that is what makes this the one law of the five with no side condition.',
     walk:[
       {tac:'simp [update]', h:'Replaced <code>update</code> by its body and applied it to <code>x</code>, leaving <code>(if x = x then value else f x) = value</code>; recognised <code>x = x</code> as true; collapsed the conditional to its then-branch; and closed the resulting <code>value = value</code>. Four actions, one tactic.'}
     ],
     deep:[
       {t:'p', h:'The same proof, with the two rewrites separated so the goal between them prints. <code>simp only [ … ]</code> runs the rules named instead of the whole default set — it keeps its own small stock of facts, which is visible in the first state below.'},
       {t:'trace', title:'What simp did, in two named steps',
        start:'f : Nat → Nat\nx value : Nat\n⊢ update f x value x = value',
        steps:[
          {tac:'simp only [update]',
           state:'f : Nat → Nat\nx value : Nat\n⊢ (if True then value else f x) = value',
           h:'The definition was unfolded, the argument substituted — and the condition has already become <code>True</code>. That last part is not <code>update</code>\'s doing: it is <code>simp</code> recognising an equation between a term and itself, which it does whether or not you ask.'},
          {tac:'simp only [↓reduceIte]',
           state:'No goals.',
           h:'A conditional whose condition is <code>True</code> collapses to its then-branch, giving <code>value = value</code>, which closes. This is the rule that <code>if_pos</code> supplies by hand when you drive the proof yourself.'}
        ],
        done:'No goals.'}
     ],
     pitfall:'Writing <code>simp</code> with nothing in the brackets. The goal mentions <code>update</code> and <code>simp</code> has no rule about it, so it cannot see the conditional at all and reports <code>`simp` made no progress</code> — an error whose wording suggests the goal is hard when in fact <code>simp</code> never got inside it. A definition is not in the simp set unless you put it there.',
     variants:'Change the conclusion to <code>f x</code> and the statement becomes false — reading at the point you wrote to gives what you wrote, not what was there before. <code>simp [update]</code> gets as far as it can and hands back <code>⊢ value = f x</code>, with no hypothesis available to close it and none derivable, since <code>value</code> and <code>f</code> are independent. Change the read point instead of the conclusion and you get the next exercise, where the missing hypothesis <i>is</i> supplied.'
    },

    {t:'p', h:'Read anywhere else and the answer comes from <code>f</code> — but only if "anywhere else" is stated, and stated the right way round.'},

    {t:'ex',
     id:'m0-2',
     name:'update_other',
     hard:false,
     why:'The second lookup equation, and the first proof in the course where a hypothesis has to be handed to a tactic by name. Its heap form, Unit 05\'s <code>write_other</code>, is what says that writing to one address leaves every other address alone — the sentence "an update is local", turned into something you can rewrite with.',
     setup:'The hypothesis is <code>hne : y ≠ x</code>, in that order. Look at the conditional in the definition before you decide that the order does not matter.',
     goal:'theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :\n    update f x value y = f y := by',
     hints:[
       'The goal says: the function <code>update f x value</code>, applied to a point <code>y</code> known to differ from <code>x</code>, equals <code>f y</code>. Unfolded, the left-hand side is <code>if y = x then value else f y</code>. The context holds <code>hne : y ≠ x</code>, which is <code>¬ (y = x)</code>.',
       'The condition of the conditional is the very proposition the hypothesis denies. So the else-branch is taken, and the else-branch is <code>f y</code>, which is the right-hand side on the nose. Again there is no case split: the case has been decided for you, in the hypothesis.',
       '<code>simp</code> again, and the brackets take more than definitions: a hypothesis put there is used as a rewrite rule. <code>hne</code> is a negated equation, and what <code>simp</code> does with one of those is rewrite the equation it denies to <code>False</code> wherever that equation occurs — including inside the condition of a conditional.',
       '<code>simp [update, hne]</code>, and nothing after it. Without <code>hne</code> in the brackets the unfolding still happens and the conditional still stands, and what comes back is <code>⊢ y = x → value = f y</code>.'
     ],
     sol:'theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :\n    update f x value y = f y := by\n  simp [update, hne]',
     expl:'Three rules fire, against two in <code>update_same</code>, and the extra one is <code>hne</code>. A negated equation, given to <code>simp</code>, is used to rewrite that equation to <code>False</code>; a conditional on <code>False</code> collapses to its else-branch. The hypothesis is not decoration and not a side condition Lean carries about — it is the step, and the proof does not go through without it.',
     walk:[
       {tac:'simp [update, hne]', h:'Unfolded <code>update</code> to leave <code>(if y = x then value else f y) = f y</code>; used <code>hne</code> to rewrite the condition <code>y = x</code> to <code>False</code>; collapsed the conditional to <code>f y</code>; closed <code>f y = f y</code>.'}
     ],
     deep:[
       {t:'p', h:'Separated into the three rules, so the two intermediate goals print. Compare the first state with <code>update_same</code>\'s: the condition is <i>not</i> settled there, because <code>y</code> and <code>x</code> are two different variables and nothing about the shape of the term decides them.'},
       {t:'trace', title:'What simp did, in three named steps',
        start:'f : Nat → Nat\nx y value : Nat\nhne : y ≠ x\n⊢ update f x value y = f y',
        steps:[
          {tac:'simp only [update]',
           state:'f : Nat → Nat\nx y value : Nat\nhne : y ≠ x\n⊢ (if y = x then value else f y) = f y',
           h:'Unfolded and substituted, and stopped. The conditional stands, undecided, and the goal is stuck in exactly the sense Unit 02 named.'},
          {tac:'simp only [hne]',
           state:'f : Nat → Nat\nx y value : Nat\nhne : y ≠ x\n⊢ (if False then value else f y) = f y',
           h:'This is the whole contribution of the hypothesis, and it is one rewrite: the proposition <code>y = x</code> in the condition became <code>False</code>. Nothing else in the goal changed.'},
          {tac:'simp only [↓reduceIte]',
           state:'No goals.',
           h:'The same collapsing rule as in <code>update_same</code>, taking the else-branch this time, leaving <code>f y = f y</code>.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Leave <code>hne</code> out of the brackets and the residue names precisely what is missing:'},
       {t:'code', tag:'sketch', src:'example (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :\n    update f x value y = f y := by\n  simp [update]'},
       {t:'state', cap:'The hypothesis is sitting in the context, unused. <code>simp</code> does not go looking.',
        src:'error: unsolved goals\nf : Nat → Nat\nx y value : Nat\nhne : y ≠ x\n⊢ y = x → value = f y'},
       {t:'p', h:'Read that residue as a bill: <i>if the two points coincide you still owe me the equation, and I have no way to rule that out</i>. Every stuck goal of this shape on this page and in Unit 05 is the same bill, and it is always paid by naming a disequality.'}
     ],
     pitfall:'Stating the hypothesis as <code>x ≠ y</code>. It is the same mathematical fact and a different term, and the conditional in the goal asks about <code>y = x</code>. Lean answers twice, and the order is the reverse of the useful one. First the familiar residue, <code>⊢ y = x → value = f y</code>, identical to what you get with no hypothesis at all — which is the tell. Then, separately, <code>warning: This simp argument is unused:</code> followed by <code>hne</code>. That second message is the diagnosis: the rewrite you supplied never matched anything, which is a different complaint from <i>the goal is hard</i>. The repair is <code>hne.symm</code>, and <code>simp [update, hne.symm]</code> closes it.',
     variants:'Drop <code>hne</code> altogether and the statement is false rather than unproved: take <code>y = x</code>, <code>f = fun _ => 0</code> and <code>value = 1</code>, and the left-hand side is <code>1</code> while the right-hand side is <code>0</code>. That single point is the whole failure — everywhere else the theorem still holds. Replace <code>hne</code> by <code>h : f y = value</code> — neither stronger nor weaker, a different fact altogether — and the theorem is true again by a different route, with no case analysis anywhere: <code>simp [update, h]</code> closes it, because <code>h</code> rewrites <code>f y</code> to <code>value</code> on the right and in the else-branch, and a conditional whose two branches are the same term collapses without its condition ever being decided. That is the shape of the last exercise on this page.'
    },

    {t:'p', h:'The next two are equations between <i>functions</i> rather than between numbers, so each of them opens with the move Unit 03 installed.'},

    {t:'ex',
     id:'m0-3',
     name:'update_shadow',
     hard:false,
     why:'The first three-move proof in the course: reduce to a point, split on it, close both branches. That shape opens the equations between heaps, which are what Unit 06 is made of; its heap form is <code>write_shadow</code>, and the proof you are about to write is that proof with <code>Heap.write</code> in place of <code>update</code>. It is also the first goal whose two branches close for different reasons under one <code>&lt;;&gt;</code>.',
     setup:'Two writes to the same point, with the second one arriving later. No hypotheses, and nothing is known about the point. Both sides are functions, so the first move is not about conditionals at all.',
     goal:'theorem update_shadow (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by',
     hints:[
       'The goal says: writing <code>a</code> at <code>x</code> and then <code>b</code> at <code>x</code> gives the same function as writing <code>b</code> at <code>x</code> once. Both sides are functions <code>Nat → Nat</code>. There are no hypotheses and nothing is known about <code>x</code>, <code>a</code>, <code>b</code> or <code>f</code>.',
       'Two functions are equal when they agree at every point, so fix an arbitrary point and compare the values there. At that point there are two possibilities and no information: either it is <code>x</code>, in which case both sides answer <code>b</code> — the left because the outer write wins, the right because it is the only write — or it is not, in which case every conditional in sight takes its else-branch and both sides answer <code>f</code> at that point.',
       'Three tactics and one combinator, all of them Unit 03\'s. <code>funext</code> turns an equation between functions into an equation at a point. <code>by_cases</code> splits on a proposition nothing else decides for you. <code>simp</code>, with the definition and the branch hypothesis in its brackets, is what you have been running for two exercises. And <code>&lt;;&gt;</code> is the move to reach for when the same text closes every branch, which is the case here.',
       'Open with <code>funext y</code>. That leaves <code>⊢ update (update f x a) x b y = update f x b y</code>: an equation between two <code>Nat</code>s, with a fresh <code>y</code> in the context and no hypothesis about it. Split it with <code>by_cases h : y = x</code>, and each of the two goals that makes is closed by <code>simp [update, h]</code> — the same call character for character, so <code>&lt;;&gt;</code> writes it once.'
     ],
     sol:'theorem update_shadow (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x <;> simp [update, h]',
     solNote:'Two lines, and the second one runs one tactic over two goals whose reasons for closing are different. That difference is what the retrospective asks about at the bottom of this page.',
     expl:'The statement is unconditional — no disequality, no hypothesis at all — because two writes to the same point cannot disagree about anything except which value survives, and the later one always survives. The proof still needs a split, but only because the goal is about an arbitrary point and the conditionals cannot move until that point is compared with <code>x</code>.',
     walk:[
       {tac:'funext y', h:'Turned an equation between two functions into an equation between two <code>Nat</code>s, and put a point <code>y</code> in the context to split on. Both sides gained an application: <code>update (update f x a) x b</code> is now being read <i>at</i> <code>y</code>.'},
       {tac:'by_cases h : y = x', h:'Replaced the goal by two copies, <code>case pos</code> carrying <code>h : y = x</code> and <code>case neg</code> carrying <code>h : ¬y = x</code>. The goal text is unchanged in both; what has changed is that each branch now contains something that decides all three conditionals in it.'},
       {tac:'<;> simp [update, h]', h:'Ran one call on both goals. In <code>case pos</code> it rewrote <code>y</code> to <code>x</code>, which made all three conditions true and collapsed the nested conditional on the left to <code>b</code> and the one on the right to <code>b</code>. In <code>case neg</code> it rewrote all three conditions to <code>False</code>, so both sides collapsed to <code>f y</code>. Same text, two mechanisms.'}
     ],
     deep:[
       {t:'trace', title:'The three moves, driven one branch at a time so each state prints',
        start:'f : Nat → Nat\nx a b : Nat\n⊢ update (update f x a) x b = update f x b',
        steps:[
          {tac:'funext y',
           state:'f : Nat → Nat\nx a b y : Nat\n⊢ update (update f x a) x b y = update f x b y',
           h:'An equation between numbers, with the point on the far right of each side.'},
          {tac:'by_cases h : y = x',
           state:'case pos\nf : Nat → Nat\nx a b y : Nat\nh : y = x\n⊢ update (update f x a) x b y = update f x b y',
           h:'The branch where the point being read is the point that was written. Nothing in the goal has moved.'},
          {tac:'· simp [update, h]',
           state:'case neg\nf : Nat → Nat\nx a b y : Nat\nh : ¬y = x\n⊢ update (update f x a) x b y = update f x b y',
           h:'The first goal is closed and the second has come forward, character for character the same goal with the hypothesis negated.'},
          {tac:'· simp [update, h]', state:'No goals.',
           h:'Two bullets carrying identical text: replace them with <code>&lt;;&gt;</code>.'}
        ],
        done:'No goals.'},
       {t:'detail', title:'What the two branches look like with the hypothesis left out', open:false,
        blocks:[
          {t:'p', h:'Splitting and then not using what the split gave you leaves both branches standing, unfolded, with three conditionals apiece and no way to move:'},
          {t:'code', tag:'sketch', src:'example (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x <;> simp [update]'},
          {t:'state', cap:'Two goals, printed one after the other with a blank line between them. The goal text is identical; only the hypothesis differs.',
           src:'error: unsolved goals\ncase pos\nf : Nat → Nat\nx a b y : Nat\nh : y = x\n⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y\n\ncase neg\nf : Nat → Nat\nx a b y : Nat\nh : ¬y = x\n⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y'},
          {t:'p', h:'Three conditionals, all on the same condition, and <code>simp</code> is unwilling to guess. This is the state the retrospective\'s third question is about.'}
        ]}
     ],
     pitfall:'Trying <code>simp [update]</code> before <code>funext</code>. The goal is then an equation between two lambdas, and Lean answers <code>`simp` made no progress</code> — which reads as though the definition were not in the simp set, when in fact the obstacle is that there is no point to read at yet. The order is fixed: reduce to a point first, then unfold.',
     variants:'Reverse the conclusion to <code>update f x a</code> and the theorem is false: the two writes are to the same point, the second one wins, and at <code>x</code> the left-hand side answers <code>b</code> while the claim asks for <code>a</code>. The positive branch is where it breaks and no hypothesis is available, since the statement has none. Make the two write points different instead of equal and you no longer have a theorem at all without an extra assumption — which is the next exercise.'
    },

    {t:'p', h:'Two writes to two different points, in either order. That is one more region than the last proof had, and the extra region is where the hypothesis goes.'},

    {t:'ex',
     id:'m0-4',
     name:'update_comm',
     hard:false,
     why:'The last thing that can be said about memory before it has to be split, and the first proof in the course that consumes a non-aliasing hypothesis. Its heap form is <code>write_comm</code>, Unit 06\'s hardest exercise and, twenty-three units later, the engine of the frame rule; the point of driving it by hand rather than with <code>&lt;;&gt;</code> is that you can afterwards point at the one line where the disequality is spent.',
     setup:'The hypothesis is <code>hne : x ≠ y</code> — about the two <i>write</i> points, since neither of them is the point you will be reading at. Drive the branches by hand with <code>if_pos</code> and <code>if_neg</code> rather than with <code>simp</code>; the location of each step is what this exercise is for.',
     goal:'theorem update_comm (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f x a) y b = update (update f y b) x a := by',
     hints:[
       'The goal says: writing <code>a</code> at <code>x</code> and then <code>b</code> at <code>y</code> gives the same function as writing <code>b</code> at <code>y</code> and then <code>a</code> at <code>x</code>, given that <code>x</code> and <code>y</code> are different. Both sides are functions. Unfolded and read at a point <code>z</code>, the left-hand side is <code>if z = y then b else if z = x then a else f z</code> and the right-hand side is the same two conditionals in the other order.',
       'Fix a point and consider where it can be. There are three regions, not two: it is <code>x</code>, or it is <code>y</code>, or it is neither. In the first region the left-hand side must skip its outer conditional and take the inner one — and that step is the only place in the whole proof where you need to know that <code>x</code> and <code>y</code> differ, because you have to get from "this point is <code>x</code>" to "this point is not <code>y</code>".',
       '<code>funext</code> to reduce to a point, <code>unfold update</code> to put the conditionals somewhere <code>if_pos</code> and <code>if_neg</code> can reach them, then <code>by_cases</code> twice: once on whether the point is <code>x</code>, and inside the negative branch again on whether it is <code>y</code>. In the first region you need a small intermediate fact of your own, which is what <code>have</code> is for. Its statement is <code>z ≠ y</code>; you get it by rewriting that goal along the branch hypothesis and finishing with <code>hne</code>. Then collapse each conditional with <code>if_pos</code> or <code>if_neg</code> according to which branch you are in.',
       'Open with <code>funext z</code>, then <code>unfold update</code>. That leaves the goal the rest of the proof is about — <code>⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z</code>, four conditionals testing two conditions, nested in opposite orders. Now <code>by_cases hzx : z = x</code>. In the positive branch write <code>have hzy : z ≠ y := by rw [hzx]; exact hne</code> — that line is the one to remember — and then <code>rw [if_neg hzy, if_pos hzx, if_pos hzx]</code>. In the negative branch split again with <code>by_cases hzy : z = y</code> and rewrite each of the two remaining regions by hand.'
     ],
     sol:'theorem update_comm (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f x a) y b = update (update f y b) x a := by\n  funext z\n  unfold update\n  by_cases hzx : z = x\n  · have hzy : z ≠ y := by rw [hzx]; exact hne\n    rw [if_neg hzy, if_pos hzx, if_pos hzx]\n  · by_cases hzy : z = y\n    · rw [if_pos hzy, if_neg hzx, if_pos hzy]\n    · rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]',
     solNote:'A three-line automated proof does exist, and it is in the <i>Why it works</i> panel below along with what it costs. Write this version once anyway: the retrospective asks which line consumes <code>hne</code>, and after the hand-driven proof the answer is a line number.',
     expl:'Three regions and four conditionals. In the region <code>z = x</code> the two sides disagree about which conditional to collapse first, and reconciling them needs a fact that is nowhere in the goal: that <code>z</code>, being <code>x</code>, is not <code>y</code>. That fact is manufactured on one line, from the branch hypothesis and the non-aliasing assumption, and it is used once. In the other two regions no such fact is needed — the branch hypothesis decides every conditional directly — which is why the proof looks lopsided.',
     walk:[
       {tac:'funext z', h:'Turned the equation between functions into an equation at a point <code>z</code>, which is now the thing the case analysis will be about. Neither <code>x</code> nor <code>y</code> is that point.'},
       {tac:'unfold update', h:'Replaced all four occurrences of <code>update</code> by their bodies and substituted <code>z</code>, giving two nested conditionals on the left and the same two in the opposite order on the right. Nothing was decided; <code>unfold</code> does not try to close anything, which is exactly why it is used here rather than <code>simp</code>.'},
       {tac:'by_cases hzx : z = x', h:'Split on the first region. <code>case pos</code> gets <code>hzx : z = x</code> and <code>case neg</code> gets <code>hzx : ¬z = x</code>; the goal text is untouched in both.'},
       {tac:'have hzy : z ≠ y := by rw [hzx]; exact hne', h:'Manufactured the missing fact and named it, leaving the goal untouched. Inside the subproof, <code>rw [hzx]</code> rewrote the claim <code>z ≠ y</code> into <code>x ≠ y</code> — the branch hypothesis pointed at the goal rather than at a conditional — and <code>exact hne</code> closed it. <b>This is the line that consumes <code>hne</code>, and it is the only one.</b>'},
       {tac:'rw [if_neg hzy, if_pos hzx, if_pos hzx]', h:'Three collapses, left to right. <code>if_neg hzy</code> skipped the outer conditional on the left, leaving <code>(if z = x then a else f z) = if z = x then a else if z = y then b else f z</code>. The first <code>if_pos hzx</code> collapsed the left to <code>a</code>. The second collapsed the right — a separate instance, because its else-branch is different text — leaving <code>a = a</code>, which <code>rw</code>\'s trailing <code>rfl</code> closed.'},
       {tac:'by_cases hzy : z = y', h:'Inside <code>case neg</code>, split on the second region. From here on <code>hne</code> is not needed and is not used: knowing <code>z ≠ x</code> and knowing whether <code>z = y</code> decides every conditional on both sides.'},
       {tac:'rw [if_pos hzy, if_neg hzx, if_pos hzy]', h:'The region <code>z = y</code>. The left collapses to <code>b</code> at once; the right has to skip its outer conditional first, which is what <code>if_neg hzx</code> does, and then collapses to <code>b</code>.'},
       {tac:'rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]', h:'The region that is neither. Four skips — two on each side, in the order each side nests them — and both sides arrive at <code>f z</code>.'}
     ],
     deep:[
       {t:'trace', title:'The first region, where the hypothesis is spent',
        start:'f : Nat → Nat\nx y a b : Nat\nhne : x ≠ y\nz : Nat\n⊢ update (update f x a) y b z = update (update f y b) x a z',
        steps:[
          {tac:'unfold update',
           state:'f : Nat → Nat\nx y a b : Nat\nhne : x ≠ y\nz : Nat\n⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z',
           h:'Four conditionals, testing two conditions, nested in opposite orders. The whole difficulty of the proof is visible in this one line.'},
          {tac:'by_cases hzx : z = x',
           state:'case pos\nf : Nat → Nat\nx y a b : Nat\nhne : x ≠ y\nz : Nat\nhzx : z = x\n⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z',
           h:'The right-hand side can now move: its outer condition is <code>z = x</code>, which <code>hzx</code> settles. The left-hand side cannot, because its outer condition is <code>z = y</code> and nothing in the context says anything about that.'},
          {tac:'have hzy : z ≠ y := by rw [hzx]; exact hne',
           state:'case pos\nf : Nat → Nat\nx y a b : Nat\nhne : x ≠ y\nz : Nat\nhzx : z = x\nhzy : z ≠ y\n⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z',
           h:'One new line in the context and no change to the goal. Everything after this point is bookkeeping; this is where the two hypotheses were combined.'},
          {tac:'rw [if_neg hzy]',
           state:'case pos\nf : Nat → Nat\nx y a b : Nat\nhne : x ≠ y\nz : Nat\nhzx : z = x\nhzy : z ≠ y\n⊢ (if z = x then a else f z) = if z = x then a else if z = y then b else f z',
           h:'The left-hand side has skipped its outer conditional. Both sides are now conditionals on <code>z = x</code>, which <code>hzx</code> settles.'},
          {tac:'rw [if_pos hzx, if_pos hzx]', state:'No goals.',
           h:'Twice, because the two remaining conditionals are different terms — same condition, different else-branches — so one rewrite cannot reach both.'}
        ],
        done:'No goals.'},
       {t:'p', h:'What happens if you try to use <code>hne</code> where <code>hzy</code> is wanted, which is the first thing most readers attempt:'},
       {t:'code', tag:'sketch', cap:'Only the first bullet has been changed; the other two regions are the real proof, and they still close.',
        src:'example (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f x a) y b = update (update f y b) x a := by\n  funext z\n  unfold update\n  by_cases hzx : z = x\n  · rw [if_neg hne]\n  · by_cases hzy : z = y\n    · rw [if_pos hzy, if_neg hzx, if_pos hzy]\n    · rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]'},
       {t:'state', cap:'The pattern <code>rw</code> built from <code>hne</code> is about <code>x</code> and <code>y</code>. Every conditional in the goal is about <code>z</code> and something.',
        src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  if x = y then ?m.25 else ?m.26\nin the target expression\n  (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z\n\ncase pos\nf : Nat → Nat\nx y a b : Nat\nhne : x ≠ y\nz : Nat\nhzx : z = x\n⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z'},
       {t:'p', h:'The hypothesis is about the two write points; the goal is about the read point. Getting from one to the other is the <code>have</code>, and it is the entire mathematical content of the theorem.'},
       {t:'p', h:'The automated proof, for comparison. Split twice, then hand <code>simp</code> everything:'},
       {t:'code', tag:'illustration', cap:'Closes. The last two entries in the brackets are the ones to look at.',
        src:'example (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f x a) y b = update (update f y b) x a := by\n  funext z\n  by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [update, hzx, hzy, hne, hne.symm]'},
       {t:'p', h:'Both orientations of <code>hne</code> are needed, and neither is optional: with only <code>hne</code> the split leaves one goal of four open, <code>⊢ y = x → b = a</code>, in the region where the read point is <code>y</code> and the conditional being decided is written the other way round. Drop <code>hne</code> entirely and three of the four are left open. So the automated proof does not hide the disequality — it uses it three times instead of once, in two spellings, and does not say where. That is the trade the rule at the top of the page is about.'}
     ],
     pitfall:'Reaching for <code>hne</code> directly, as above, or reaching for it in the third region where it is not needed at all. A related and slower failure is dropping <code>unfold update</code> and going straight to <code>rw [if_neg hzy]</code>: the conditionals are still hidden inside <code>update</code>, so the rewrite finds no pattern and quotes back <code>in the target expression</code> / <code>update (update f x a) y b z = update (update f y b) x a z</code> — the goal <i>as it is printed</i>, with no <code>if</code> visible anywhere in it. <code>unfold</code> is not decoration here — it is what puts the conditionals where <code>if_pos</code> and <code>if_neg</code> can see them.',
     variants:'Drop <code>hne</code> and the statement is false. Take <code>x = y = 0</code>, <code>f = fun _ => 0</code>, <code>a = 1</code> and <code>b = 2</code>: the left-hand side writes <code>1</code> then <code>2</code> and answers <code>2</code> at <code>0</code>, the right-hand side writes <code>2</code> then <code>1</code> and answers <code>1</code>. Exactly one of the three regions collapses — the first and second become the same region — and it is the one the <code>have</code> was for. Reverse the hypothesis to <code>hne : y ≠ x</code> and the theorem is still true and the proof still goes through, with one token added on the line that consumes it: <code>exact Ne.symm hne</code> in place of <code>exact hne</code>, and nothing else in the proof moves. Reverse the <i>conclusion</i> instead, swapping which side is which, and the theorem is the same theorem — that is what "commute" means — and the proof does <i>not</i> survive verbatim. Each side now nests its two conditionals the other way round, so every <code>rw</code> list has to be reordered to match: the first region becomes <code>rw [if_pos hzx, if_neg hzy, if_pos hzx]</code>, and running the original line there fails at its third entry with <code>Did not find an occurrence of the pattern</code> — the pattern being a conditional on <code>z = x</code>, the target at that moment being <code>a = if z = y then b else a</code>, which has none left. The mathematics is symmetric; the rewriting is not, because <code>rw</code> is told <i>which</i> conditional to collapse and there is now a different one in front.'
    },

    {t:'note', kind:'key', title:'One of the four needs a hypothesis. Only one.',
     h:'Two writes to the same point commute in no sense at all — they shadow, and the later one wins, unconditionally. Two writes to different points commute completely, but the words "to different points" are load-bearing and have to be supplied. That asymmetry is the whole subject in miniature, and it is why <code>update_comm</code> earns the name <i>the baby frame rule</i>. Everything this course builds is machinery for supplying that hypothesis at scale and for arbitrarily many addresses at once, and the shape of the answer is already visible in <code>update_comm</code>: what licenses the exchange is that the two writes do not overlap — not that they agree about anything.'},

    {t:'p', h:'The last one is yours to state as well as to prove.'},

    {t:'ex',
     id:'x13',
     name:'update_idem',
     hard:false,
     why:'A design exercise: turning an English sentence into a theorem is a skill this course will ask for repeatedly, and it is much easier to practise on a statement whose proof you can already write in your sleep. The statement you are aiming at also has a second life: a write that installs the value already there produces the same heap. Unit 06 has it as <code>write_of_eq</code> — in the more general spelling that the <i>variants</i> panel below asks you to compare yours with.',
     setup:'<b>State and prove that updating a point with the value already stored there does nothing.</b> The editor starts you with a placeholder line rather than a statement; delete it and write your own <code>theorem update_idem …</code>. Your text is what gets checked, so a different correct statement of the same fact passes too — the <i>variants</i> panel names two of them and says what each is good for.',
     goal:'-- Delete the line below and write your own `theorem update_idem …`.\n-- Any correct statement of the fact will be accepted.\nexample : True := by',
     hints:[
       'What has to be decided first: which things are quantified, and what the two sides of the equation are. "Updating a point" needs a function and a point. "With the value already stored there" is not a third quantified variable — it is determined by the first two. "Does nothing" is an equation, and its right-hand side is the function you started with.',
       'So the statement takes a function and a point, has no hypothesis, and equates a function with a function. Once written, it is proved by the shape you used in <code>update_shadow</code>: reduce to a point, split on whether that point is the one written to, close both branches. In the positive branch both sides are the function\'s value at the write point; in the negative branch the update is invisible.',
       'The statement is <code>theorem update_idem (f : Nat → Nat) (x : Nat) : update f x (f x) = f</code>. Note where <code>f x</code> appears: as the third argument of <code>update</code>, not as a separate binder. If you wrote it with an extra variable <code>v</code> and a hypothesis <code>f x = v</code>, that is also correct and is discussed under <i>variants</i>.',
       'Open with <code>funext y</code>, leaving <code>⊢ update f x (f x) y = f y</code>. Then <code>by_cases h : y = x</code>, and <code>simp [update, h]</code> closes both branches, so <code>&lt;;&gt;</code> writes it once.'
     ],
     sol:'theorem update_idem (f : Nat → Nat) (x : Nat) : update f x (f x) = f := by\n  funext y\n  by_cases h : y = x <;> simp [update, h]',
     solNote:'If your own statement was different and Lean accepted your proof of it, you were right; the checker runs your text, not this one. Compare yours with this one anyway, because which variables are bound and which are determined is the part that will keep mattering.',
     expl:'The proof is <code>update_shadow</code>\'s, character for character, which is the sign that the two facts are the same fact: a write is invisible exactly when the value it installs is the value that would have been read anyway. In the positive branch the update collapses to <code>f x</code> and the goal to <code>f x = f x</code> only because <code>h</code> has been used on the goal as well as on the condition; in the negative branch the update is skipped and never mattered.',
     walk:[
       {tac:'funext y', h:'Turned the equation between <code>update f x (f x)</code> and <code>f</code> into an equation between their values at an arbitrary <code>y</code>, and gave you <code>y</code> to split on.'},
       {tac:'by_cases h : y = x', h:'Split into the point that was written and every other point. The goal is unchanged in both branches; each now carries a hypothesis that decides the conditional inside <code>update</code>.'},
       {tac:'<;> simp [update, h]', h:'In <code>case pos</code>: rewrote <code>y</code> to <code>x</code> throughout, which turned the goal into <code>update f x (f x) x = f x</code>, collapsed the conditional to its then-branch <code>f x</code>, and closed <code>f x = f x</code>. In <code>case neg</code>: rewrote the condition to <code>False</code>, collapsed to the else-branch <code>f y</code>, closed <code>f y = f y</code>.'}
     ],
     deep:[
       {t:'trace', title:'Both branches, one at a time',
        start:'f : Nat → Nat\nx : Nat\n⊢ update f x (f x) = f',
        steps:[
          {tac:'funext y',
           state:'f : Nat → Nat\nx y : Nat\n⊢ update f x (f x) y = f y',
           h:'Note the right-hand side: <code>f</code> applied to <code>y</code>, which is what an equation with a bare <code>f</code> on one side becomes once a point is fixed.'},
          {tac:'by_cases h : y = x',
           state:'case pos\nf : Nat → Nat\nx y : Nat\nh : y = x\n⊢ update f x (f x) y = f y',
           h:'The written point. Both sides will become <code>f x</code>, but only after <code>h</code> has been used on the right-hand side too.'},
          {tac:'· simp [update, h]',
           state:'case neg\nf : Nat → Nat\nx y : Nat\nh : ¬y = x\n⊢ update f x (f x) y = f y',
           h:'The other points, where the value <code>f x</code> written by the update is never consulted.'},
          {tac:'· simp [update, h]', state:'No goals.', h:'Identical text on both bullets, so the two lines become one.'}
        ],
        done:'No goals.'},
       {t:'p', h:'The <i>variants</i> panel below says the pointwise spelling <code>∀ y, update f x (f x) y = f y</code> is the one to avoid. That is a claim you can watch fail. Hand yourself the pointwise statement as a hypothesis and try to rewrite an equation between functions with it:'},
       {t:'code', tag:'sketch',
        src:'example (f : Nat → Nat) (x : Nat) (hpt : ∀ y, update f x (f x) y = f y) :\n    update f x (f x) = f := by\n  rw [hpt]'},
       {t:'state', cap:'The pattern <code>rw</code> builds from a family of equations carries the point as a metavariable, <code>?y</code>, so it matches only a term with a point already applied to it. The goal has none — <code>update f x (f x)</code> stands there bare.',
        src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  update f x (f x) ?y\nin the target expression\n  update f x (f x) = f\n\nf : Nat → Nat\nx : Nat\nhpt : ∀ (y : Nat), update f x (f x) y = f y\n⊢ update f x (f x) = f'}
     ],
     pitfall:'Writing the statement with the value as a free variable — <code>update f x v = f</code> — which is false: nothing forces <code>v</code> to be what <code>f</code> already holds at <code>x</code>. The counterexample is one line: <code>f = fun _ => 0</code>, <code>x = 0</code>, <code>v = 1</code>. A design exercise fails in the statement more often than in the proof, so read your statement back as an English sentence and check that it says what you were asked for.',
     variants:'Two other correct statements, both compiled. <b>The hypothesis form</b>, <code>(h : f x = v) : update f x v = f</code>, is strictly more general — the given statement is the case <code>v := f x</code> — and it is the form to prefer when the value you are writing arrives from somewhere else in a proof and you have an equation about it rather than a syntactic match. That is the spelling the course keeps: Unit 06\'s <code>write_of_eq</code> takes the equation as a hypothesis, for exactly that reason. Its proof here is <code>funext y</code>, <code>by_cases hy : y = x &lt;;&gt; simp [update, hy, h]</code>. <b>The pointwise form</b>, <code>∀ y, update f x (f x) y = f y</code>, is true and provable — <code>intro y</code> in place of <code>funext y</code> and the rest is unchanged — and is the one to avoid: Unit 03 showed that a family of equations cannot be rewritten with when the function occurs somewhere that is not an application, and every later use of this law is exactly such an occurrence. The <i>Why it works</i> panel above shows that failure happening.'
    },

    /* ----------------------------------------------------- retrospective --- */

    {t:'sec', s:'Retrospective'},

    {t:'p', h:'Three questions. Answer each before opening it.'},

    {t:'detail', title:'Which of the four laws needs a hypothesis, and why only that one?', open:false,
     blocks:[
       {t:'p', h:'Only <code>update_comm</code>. The other three are unconditional, and the reason is the same in each case: their two sides can only ever disagree at points where every conditional involved is testing the <i>same</i> condition, so whichever way that condition falls, both sides fall with it.'},
       {t:'p', h:'In <code>update_same</code> and <code>update_other</code> there is one write point and the read point is pinned to it or excluded from it in the statement itself. In <code>update_shadow</code> there are two writes but at one point, so a single split settles both sides at once. <code>update_comm</code> is the first statement whose two sides test <i>different</i> conditions — <code>z = x</code> on one side, <code>z = y</code> on the other, at the outer position — and they can only be made to agree if the two conditions cannot both hold. That is what <code>hne</code> says, and it is the only thing it is used for.'},
       {t:'p', h:'The same accounting, in the same words, decides which of the heap laws of Units 05 and 06 carry a disequality and which do not.'}
     ]},

    {t:'detail', title:'In update_comm, which line consumes hne?', open:false,
     blocks:[
       {t:'code', tag:'verified', cap:'The fourth of the proof\'s eight lines. Nothing before it mentions <code>hne</code> and nothing after it does either.',
        src:'    have hzy : z ≠ y := by rw [hzx]; exact hne'},
       {t:'p', h:'The line converts a fact about the two write points into a fact about the read point, and it can only do so inside the branch where the read point has been identified with one of them. That is why it sits inside <code>case pos</code> and not at the top of the proof: at the top there is no <code>hzx</code> to rewrite along, and <code>z ≠ y</code> is not derivable.'},
       {t:'p', h:'When the same argument is made about heaps, <code>hne</code> becomes an assumption that two whole regions of memory do not overlap, and this line becomes the step that says a location held by one region is not held by the other. The frame rule is that step, applied to every location at once.'}
     ]},

    {t:'detail', title:'What did &lt;;&gt; simp hide in update_shadow that if_pos and if_neg show in update_comm?', open:false,
     blocks:[
       {t:'p', h:'How many conditionals there were, which one collapsed, and in which order. The unfolded goal of <code>update_shadow</code> carries three — two nested on the left and one on the right — all testing <code>y = x</code>, and <code>simp [update, h]</code> disposes of every one of them without saying so. The hand-driven proof has to name them:'},
       {t:'code', tag:'illustration', cap:'The same theorem, driven by hand. Two collapses in the positive branch, three in the negative.',
        src:'example (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  unfold update\n  by_cases h : y = x\n  · rw [if_pos h, if_pos h]\n  · rw [if_neg h, if_neg h, if_neg h]'},
       {t:'p', h:'The counts differ between the branches because a conditional that is skipped exposes another conditional underneath it, while a conditional that is taken does not. Two rewrites in one branch and three in the other, from one goal, is the kind of asymmetry <code>simp</code> exists to absorb — and the kind that has to be visible when the question is <i>where</i> a hypothesis was used rather than <i>whether</i> the theorem is true.'},
       {t:'p', h:'That is the rule stated at the top of this page, now with a case behind it: <code>simp</code> when both branches want the same text and the route is not the content; hand-driven <code>rw</code> when the route is.'}
     ]},

    {t:'dod', h:'You can prove all four laws of <code>update</code> and name, for each <code>simp</code> call, which rewrites fired and what each one contributed. You can recognise a residue of the form <code>⊢ y = x → value = f y</code> as an unpaid disequality, and you know it is paid by naming a hypothesis in the brackets and not by <code>simp</code> looking harder. You can open an equation between functions with <code>funext</code>, split on the point, and close both branches with one tactic when they agree and with two when they do not. You can drive a three-region analysis by hand with <code>if_pos</code> and <code>if_neg</code>, and point at the single line that consumes a disequality. You can choose between <code>simp</code> and <code>rw</code> by the stated rule. And you can take an English sentence about memory and produce a theorem statement that says it.'},

    {t:'p', h:'<code>update_comm</code> used <code>hne</code> exactly once, to derive <code>z ≠ y</code> from <code>z = x</code>. Remember that line: in twenty-three units it is the reason the frame rule is true. But nobody hands you <code>hne</code> in a real program, and <code>update</code> cannot give a cell up — "not mine" is what <code>emp</code> will be made of.'}

  ]
});
