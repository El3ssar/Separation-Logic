registerChapter({
  id: 'errors',
  num: '§',
  phase: 'Phase 0 · Getting started',
  title: 'When Lean says no',
  blurb: 'Twelve real error messages, indexed by their opening words: what Lean printed, what it means, the commonest cause, and the fix.',

  /* `Heap.write` is unit 05's operation. It is here as the exhibit for
     "Unknown constant": a reader who has read ahead types it, and this page
     shows what Lean says. The entry itself says the name does not exist yet.
     `induction` and `generalizing` belong to unit 20; they appear once, in a
     closed fold whose title says so, because the message they produce cannot
     be produced any other way. */
  ledgerAllow: [
    'Heap.write',
    /* the misspelling in the `Unknown identifier` exhibit, and a Lean-core
       name quoted in entry 12 to show where a collision comes from */
    'update_othr', 'cond_true',
    'induction', 'induction … generalizing',
    /* the banned tactics, quoted in order to show what happens when you try
       them — that section is the whole point of the exhibit */
    'set', 'omega', 'linarith', 'ring', 'simp_arith', 'aesop', 'decide',
    'Function.funext_iff'
  ],

  orient: {
    youWill: [
      'Find a message you are looking at by matching its opening words against a table.',
      'Tell <code>Type mismatch</code> from <code>Application type mismatch</code>, and know which one means "the orientation is wrong".',
      'Read a <code>motive is not type correct</code> failure without reading the essay Lean attaches to it.',
      'Ask Lean three questions — <code>simp?</code>, <code>exact?</code>, <code>#print axioms</code> — and know what each will and will not tell you.',
      'Make a goal display bigger with <code>set_option pp.explicit true</code> when two terms print the same and are not the same.',
      'Say why a tactic you read about somewhere else does not work here, and why "Lean accepted it" is not the test.'
    ],
    needs: [
      'Units 00–04. Every broken proof on this page is built out of their definitions and lemmas, so you can run any of them.'
    ],
    payoff: 'This is the page you keep open in a second tab at two in the morning.'
  },

  blocks: [

    /* ---------------------------------------------------------- framing --- */

    {t:'p', h:'This is a reference page, not a lecture. The course does not pass through it: Unit 05 follows Unit 04 whether or not you stop here. What it is for is the twenty minutes you are about to lose to a message you have never seen, and the way to use it is to find your message in the table below and go to that entry.'},

    {t:'p', h:'Every message on this page was produced by breaking a proof in one place and copying what Lean said. The proofs are built out of Units 00–04 — usually one you have already done, sometimes a two-line theorem written to aim the mistake — and the broken version is printed beside the fix, so you can run either. Nothing here is remembered or paraphrased: if the text on your screen differs from the text here by more than a name, you have a different problem and the entry may be the wrong one.'},

    {t:'note', kind:'tip', title:'Read the first message, not the last',
     h:'Lean reports every failure it finds, and one broken line usually produces several. The first is the cause; the ones after it are what the cause did to the rest of the proof. An <code>unsolved goals</code> at the bottom of a list is almost always the echo of something above it.'},

    /* ------------------------------------------------------------ index --- */

    {t:'h3', s:'Find your message'},

    {t:'tbl', cap:'Match the opening words. The two <code>rewrite</code> failures share a first line and differ after the colon. The numbers are the headings below, in the same order.',
     head:['#', 'what Lean printed', 'what has gone wrong'],
     rows:[
       ['1', '<code>Unknown identifier …</code> / <code>Unknown constant …</code>', 'A name that is misspelled, or that belongs to a unit you have not reached.'],
       ['2', '<code>Type mismatch</code>', 'The term proves something, and it is not the thing you asked for. Usually the equation runs the other way.'],
       ['3', '<code>Not a definitional equality</code>', '<code>rfl</code> on two sides that reduction cannot bring together.'],
       ['4', '<code>Invalid field `symm` …</code>', 'You projected before you applied.'],
       ['5', '<code>unsolved goals</code>', 'A branch you never closed — commonly the second half of a <code>by_cases</code>.'],
       ['6', '<code>Tactic `rewrite` failed: motive is not type correct</code>', 'You rewrote a proposition that an <code>if</code> is standing on.'],
       ['7', '<code>`simp` made no progress</code>', 'Nothing in the brackets matches anything in the goal.'],
       ['8', '<code>Tactic `rewrite` failed: Did not find an occurrence</code>', 'The pattern is not in the goal, letter for letter.'],
       ['9', '<code>Function expected at …</code>', 'You applied a proof that is not a function.'],
       ['10', '<code>don\'t know how to synthesize implicit argument</code>', 'Nothing in sight tells Lean what an implicit argument is.'],
       ['11', '<code>Application type mismatch</code>', 'One argument out of several has the wrong type. Lean names it.'],
       ['12', '<code>… has already been declared</code>', 'The name is taken — by your own paste, or by Lean.']
     ]},

    /* ============================================================== 1 ===== */

    {t:'sec', s:'The twelve'},

    {t:'h3', s:'1 · <code>Unknown identifier</code> · <code>Unknown constant</code>'},

    {t:'state', cap:'From the proof below. Two conventions hold throughout this page: the <code>snippet:3:8:</code> position prefix Lean puts in front of every message is dropped — the workbook prints the same position as <i>line 3, col 9</i> — and where one mistake produced several messages, a blank line separates them.',
     src:'error(lean.unknownIdentifier): Unknown identifier `update_othr`'},

    {t:'p', h:'Lean is telling you it has never heard of the name. Three things cause it, in descending order of frequency: a typo; a name from a later unit, which does not exist yet in the context your proof is checked against; and a name you have half-remembered from a library — <code>symm h</code> instead of <code>h.symm</code>, because the theorem is called <code>Eq.symm</code> and the bare word <code>symm</code> is nobody\'s name.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'One letter missing.',
       src:'theorem other_typo (f : Nat → Nat) (x y v : Nat) (hne : y ≠ x) :\n    update f x v y = f y := by\n  exact update_othr f x y v hne'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       src:'theorem other_typo (f : Nat → Nat) (x y v : Nat) (hne : y ≠ x) :\n    update f x v y = f y := by\n  exact update_other f x y v hne'}},

    {t:'code', tag:'sketch', cap:'Unit 04\'s <code>update_shadow</code> again, correct except for one name in the brackets.',
     src:'theorem shadow_ahead (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x <;> simp [Heap.write, update, h]'},

    {t:'state', cap:'The same complaint, worded differently. It appears twice because <code>&lt;;&gt;</code> really did run the tactic on both branches.',
     src:'error(lean.unknownIdentifier): Unknown constant `Heap.write`\n\nerror(lean.unknownIdentifier): Unknown constant `Heap.write`'},

    {t:'p', h:'The two wordings carry different information. Lean says <i>constant</i> when the part before the dot names something that exists and the part after it does not: <code>Heap</code> is a real type, so <code>Heap.write</code> is a real namespace with nothing of that name in it. It says <i>identifier</i> when nothing resolves at all — <code>Foo.bar</code>, with no <code>Foo</code> anywhere, gets <i>identifier</i> despite the dot. So <i>constant</i> means <i>right namespace, wrong member</i>, which narrows the search. <code>Heap.write</code> is an operation you will define in Unit 05; reading ahead and using it now is what "not yet" looks like, and the message never says <i>later</i>, only <i>never</i>.'},

    /* ============================================================== 2 ===== */

    {t:'h3', s:'2 · <code>Type mismatch</code>'},

    {t:'state', cap:'<code>update_comm</code> applied to a goal that wants it the other way round.',
     src:'error: Type mismatch\n  update_comm f x y a b hne\nhas type\n  update (update f x a) y b = update (update f y b) x a\nbut is expected to have type\n  update (update f y b) x a = update (update f x a) y b'},

    {t:'p', h:'Read the two terms in the message, the one it has and the one it wanted, and read them to the end. They are the same length, built from the same six symbols, and they differ only in which side of the equals sign each nest is on. That is what almost every <code>Type mismatch</code> in this course looks like: the term you offered is a proof of something, and it is nearly the thing you wanted. The fix is not a different lemma; it is <code>.symm</code> on the one you have.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'The equation points the wrong way.',
       src:'theorem comm_backwards (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f y b) x a = update (update f x a) y b :=\n  update_comm f x y a b hne'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'Turn the equation round rather than the statement.',
       src:'theorem comm_backwards (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f y b) x a = update (update f x a) y b :=\n  (update_comm f x y a b hne).symm'}},

    /* ============================================================== 3 ===== */

    {t:'h3', s:'3 · <code>Not a definitional equality</code>'},

    {t:'state', cap:'<code>rfl</code> offered as a term for <code>update f x v x = v</code>. One mistake, two messages.',
     src:'error: Not a definitional equality: the left-hand side\n  update f x v x\nis not definitionally equal to the right-hand side\n  v\n\nerror: Type mismatch\n  rfl\nhas type\n  ?m.3 = ?m.3\nbut is expected to have type\n  update f x v x = v'},

    {t:'p', h:'The first message is the content: Lean unfolded <code>update f x v x</code> as far as it could, arrived at <code>if x = x then v else f x</code>, and stopped, because deciding <code>x = x</code> for a variable <code>x</code> is not something reduction can do. The second message is the same failure told from the other end — <code>rfl</code> has type <code>?m.3 = ?m.3</code>, an equation whose two sides are the <i>same</i> unknown, and Lean could not choose an unknown that makes both sides of your goal identical. Do not go looking for <code>?m.3</code>; it is not in your proof.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'Nothing can finish the reduction.',
       src:'theorem same_rfl_term (f : Nat → Nat) (x v : Nat) : update f x v x = v := rfl'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'<code>simp</code> settles the condition as a proposition instead of computing it.',
       src:'theorem same_rfl (f : Nat → Nat) (x v : Nat) : update f x v x = v := by\n  simp [update]'}},

    {t:'p', h:'Written as a tactic — <code>:= by rfl</code> rather than <code>:= rfl</code> — the same failure prints once, as <code>Tactic `rfl` failed: The left-hand side …</code>, and appends the goal. The two forms are the same check; only the reporting differs.'},

    /* ============================================================== 4 ===== */

    {t:'h3', s:'4 · <code>Invalid field</code>'},

    {t:'state', cap:'<code>h</code> is a family of equations, not an equation.',
     src:'error(lean.invalidField): Invalid field `symm`: The environment does not contain `Function.symm`, so it is not possible to project the field `symm` from an expression\n  h\nof type `∀ (n : Nat), f n = g n`'},

    {t:'p', h:'This is the diagnostic printing its own working, and the working is what you need. <code>h.foo</code> means <code>Head.foo h</code> where <code>Head</code> is the head of <code>h</code>\'s type; here that type begins <code>∀</code>, so the head is <code>Function</code>, so Lean went looking for <code>Function.symm</code> and did not find it. Nothing is wrong with <code>symm</code>. What is wrong is that you have a family of equations and dot notation was asked to treat it as one. Apply it first, project second.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'Projecting the family.',
       src:'theorem pointwise_symm (f g : Nat → Nat) (h : ∀ n, f n = g n) (m : Nat) : g m = f m :=\n  h.symm m'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'One pair of brackets. <code>h m</code> is an equation; <i>that</i> has a <code>symm</code>.',
       src:'theorem pointwise_symm (f g : Nat → Nat) (h : ∀ n, f n = g n) (m : Nat) : g m = f m :=\n  (h m).symm'}},

    /* ============================================================== 5 ===== */

    {t:'h3', s:'5 · <code>unsolved goals</code>'},

    {t:'state', cap:'A <code>by_cases</code> with one tactic under it. The position Lean reports is the theorem\'s, not the missing branch\'s.',
     src:'error: unsolved goals\ncase neg\nf : Nat → Nat\nx a b y : Nat\nh : ¬y = x\n⊢ update (update f x a) x b y = update f x b y'},

    {t:'p', h:'A splitting tactic leaves two goals and the next tactic sees only the first. Write one tactic after <code>by_cases</code> and you have closed the <code>pos</code> branch and walked away from the <code>neg</code> one; the proof ends, a goal is still standing, and Lean reports it against the theorem it belongs to rather than against any line you wrote. The <code>case neg</code> on the first line of the display tells you which half survived. Two fixes: a focus dot for each branch, or <code>&lt;;&gt;</code> when the same text closes both.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'One <code>simp</code> for two goals.',
       src:'theorem shadow_half (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x\n  simp [update, h]'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'A dot each. Here the two lines are identical, so <code>&lt;;&gt; simp [update, h]</code> would also do.',
       src:'theorem shadow_half (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x\n  · simp [update, h]\n  · simp [update, h]'}},

    /* ============================================================== 6 ===== */

    {t:'h3', s:'6 · <code>motive is not type correct</code>'},

    {t:'state', cap:'The head of the message. Lean attaches a long paragraph beginning <code>Explanation:</code>; it is in the fold below, unedited.',
     src:'error: Tactic `rewrite` failed: motive is not type correct:\n  fun _a => (if _a then v else f y) = v\nError: Application type mismatch: The argument\n  instDecidableEqNat y x\nhas type\n  Decidable (y = x)\nbut is expected to have type\n  Decidable _a\nin the application\n  @ite Nat _a (instDecidableEqNat y x)'},

    {t:'p', h:'To rewrite, Lean has to punch a hole in the goal: it replaces every copy of the thing you are rewriting with a placeholder — here <code>_a</code> — and the result is the <i>motive</i>. That only works if the rest of the goal still makes sense with a hole in it. An <code>if</code> does not. The last line of the message writes the goal\'s <code>if</code> out as an ordinary application — <code>ite</code> is what <code>if _ then _ else _</code> is short for — and there, beside the condition <code>y = x</code>, sits the instance that decides it, <code>instDecidableEqNat y x</code>. That instance\'s <i>type</i> mentions the very proposition you removed. Punch the hole and the instance no longer fits it.'},

    {t:'p', h:'So this message means you rewrote a proposition that something else in the goal depends on, and everywhere in this course that something else is the <code>Decidable</code> instance beside an <code>if</code>. The hypothesis below is contrived — you will not often be handed <code>(y = x) ↔ True</code> — because it is the shortest thing that aims a rewrite at a condition, and the aim is what matters. (<code>rw</code> takes an <code>↔</code> wherever it takes an <code>=</code>; replacing one proposition by another is the same move.) Do not reach for a cleverer <code>rw</code>. Use <code>simp</code>, which rebuilds the instance as it goes, or split the <code>if</code> yourself with <code>by_cases</code> and never touch the condition.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'<code>rw</code> aimed at the condition of an <code>if</code>.',
       src:'theorem update_when_true (f : Nat → Nat) (x y v : Nat) (hp : (y = x) ↔ True) :\n    update f x v y = v := by\n  unfold update\n  rw [hp]'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'Same hypothesis, same goal, one word changed.',
       src:'theorem update_when_true (f : Nat → Nat) (x y v : Nat) (hp : (y = x) ↔ True) :\n    update f x v y = v := by\n  unfold update\n  simp [hp]'}},

    {t:'detail', title:'The <code>Explanation:</code> paragraph, in full', open:false, blocks:[
      {t:'p', h:'Lean prints this after the message above, then the goal. Read it once: it describes the mechanism rather than the symptom, and its last paragraph is Lean recommending <code>simp</code> in as many words.'},
      {t:'state', cap:'Verbatim, including the goal Lean appends at the end.',
       src:'Explanation: The rewrite tactic rewrites an expression \'e\' using an equality \'a = b\' by the following process. First, it looks for all \'a\' in \'e\'. Second, it tries to abstract these occurrences of \'a\' to create a function \'m := fun _a => ...\', called the *motive*, with the property that \'m a\' is definitionally equal to \'e\'. Third, we observe that \'congrArg\' implies that \'m a = m b\', which can be used with lemmas such as \'Eq.mpr\' to change the goal. However, if \'e\' depends on specific properties of \'a\', then the motive \'m\' might not typecheck.\n\nPossible solutions: use rewrite\'s \'occs\' configuration option to limit which occurrences are rewritten, or use \'simp\' or \'conv\' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and \'Decidable\' instances whose types depend on the rewritten term, and \'simp\' can apply user-defined \'@[congr]\' theorems as well).\n\nf : Nat → Nat\nx y v : Nat\nhp : y = x ↔ True\n⊢ (if y = x then v else f y) = v'},
      {t:'p', h:'<code>occs</code> and <code>conv</code> are Lean features this course never uses. Take the other half of the sentence.'}
    ]},

    /* ============================================================== 7 ===== */

    {t:'h3', s:'7 · <code>`simp` made no progress</code>'},

    {t:'state', cap:'Four words, no context, no goal.',
     src:'error: `simp` made no progress'},

    {t:'p', h:'The least informative message in the course, and the commonest. It means <code>simp</code> looked at the goal, found nothing in its rule set that matched any part of it, and refused to pretend otherwise. It is not a failure of the proof; it is a failure of the rules you handed it.'},

    {t:'p', h:'Two causes, and you can tell them apart by looking at the brackets. If they are empty, the definition you want is not there — <code>simp</code> does not unfold <code>update</code> unless you say <code>simp [update]</code>. If the definition <i>is</i> there and you still get this, the goal is the wrong shape: an equation between two <i>functions</i> has nothing at its top level for a rule about values to match, and no amount of unfolding will change that until <code>funext</code> has turned it into an equation between two values.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'The two sides are functions. <code>update</code> is in the brackets and cannot help.',
       src:'theorem shadow_direct (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  simp [update]'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'<code>funext</code> first, then there is something to rewrite.',
       src:'theorem shadow_direct (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x <;> simp [update, h]'}},

    /* ============================================================== 8 ===== */

    {t:'h3', s:'8 · <code>Did not find an occurrence of the pattern</code>'},

    {t:'state', cap:'<code>if_neg</code> handed a disequality pointing the wrong way.',
     src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  if x = y then ?m.8 else ?m.9\nin the target expression\n  (if y = x then v else f y) = f y\n\nf : Nat → Nat\nx y v : Nat\nhne : x ≠ y\n⊢ (if y = x then v else f y) = f y'},

    {t:'p', h:'This message is generous: it prints the pattern it wanted and the expression it searched, one above the other, and the difference between them is your bug. Here the pattern is <code>if x = y</code> and the goal says <code>if y = x</code>. <code>rw</code> matches text, up to filling in the holes marked <code>?m</code>; it has no opinion about equality being symmetric. The disequality you have is <code>x ≠ y</code>, which is a term that remembers which side is which, and <code>if_neg</code> built its pattern from it. <code>Ne.symm</code> turns it round.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'<code>hne : x ≠ y</code>, condition <code>y = x</code>.',
       src:'theorem other_orient (f : Nat → Nat) (x y v : Nat) (hne : x ≠ y) :\n    update f x v y = f y := by\n  unfold update\n  rw [if_neg hne]'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'<code>Ne.symm hne : y ≠ x</code>, and the pattern <code>if y = x</code> is now the one in the goal.',
       src:'theorem other_orient (f : Nat → Nat) (x y v : Nat) (hne : x ≠ y) :\n    update f x v y = f y := by\n  unfold update\n  rw [if_neg (Ne.symm hne)]'}},

    {t:'detail', title:'The same message when nothing is misspelled and nothing is backwards', open:false, blocks:[
      {t:'p', h:'The second cause is subtler and produces an identical-looking message. <code>rw [update_same]</code> below fails not because the goal is wrong but because the goal has already been unfolded: the text <code>update …</code> is not in it, only what <code>update</code> means.'},
      {t:'state', cap:'The pattern is <code>update_same</code>\'s left-hand side with holes in it. The target contains no <code>update</code> at all.',
       src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  update ?f ?x ?value ?x\nin the target expression\n  (fun y => if y = x then v else f y) x = v\n\nf : Nat → Nat\nx v : Nat\n⊢ (fun y => if y = x then v else f y) x = v'},
      {t:'cmp',
       left: {t:'Broken', kind:'bad', tag:'sketch',
         h:'<code>rw</code> needs the word on the page.',
         src:'theorem same_unfolded (f : Nat → Nat) (x v : Nat) :\n    (fun y => if y = x then v else f y) x = v := by\n  rw [update_same]'},
       right:{t:'Fixed', kind:'good', tag:'illustration',
         h:'<code>exact</code> does not. It reduces both sides and finds them the same term.',
         src:'theorem same_unfolded (f : Nat → Nat) (x v : Nat) :\n    (fun y => if y = x then v else f y) x = v := by\n  exact update_same f x v'}},
      {t:'p', h:'That is the general rule behind both halves of this entry. <code>rw</code> is a text operation and <code>exact</code> is a meaning operation. When you are certain the lemma is the right one and <code>rw</code> will not take it, try handing it to <code>exact</code> with its arguments filled in.'}
    ]},

    /* ============================================================== 9 ===== */

    {t:'h3', s:'9 · <code>Function expected</code>'},

    {t:'state', cap:'<code>h : f = g</code>, and <code>h.symm n</code>.',
     src:'error: Function expected at\n  Eq.symm h\nbut this term has type\n  g = f\n\nNote: Expected a function because this term is being applied to the argument\n  n'},

    {t:'p', h:'The companion to <code>Invalid field</code>, and the reason both entries are here: they are the two ways the same slip is reported. There the projection was illegal; here it was legal, and what came out of it is an equation between two functions, which is not itself a function and cannot be applied to <code>n</code>. Notice that Lean has already rewritten <code>h.symm</code> as <code>Eq.symm h</code> in the message — dot notation is a spelling, and the error is printed in the other spelling.'},

    {t:'p', h:'An equation between functions becomes an equation at a point through <code>congrFun</code>, not through application. Anything given one argument more than it has room for produces this message, and in practice that is nearly always a pair of brackets in the wrong place: <code>h.symm n</code> is read as <code>(h.symm) n</code>, and if what you wanted was the symmetric form of <code>h n</code> you have to write <code>(h n).symm</code> — which is the previous entry.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'<code>g = f</code> applied to <code>n</code>.',
       src:'theorem apply_symm (f g : Nat → Nat) (h : f = g) (n : Nat) : g n = f n :=\n  h.symm n'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       src:'theorem apply_symm (f g : Nat → Nat) (h : f = g) (n : Nat) : g n = f n :=\n  congrFun h.symm n'}},

    /* ============================================================= 10 ===== */

    {t:'h3', s:'10 · <code>don\'t know how to synthesize implicit argument</code>'},

    {t:'state', cap:'All four messages from one broken line. The first two are the cause.',
     src:'error: don\'t know how to synthesize implicit argument `g`\n  @function_extensionality ?m.12 ?m.13\ncontext:\n⊢ Nat → Nat\n\nerror: don\'t know how to synthesize implicit argument `f`\n  @function_extensionality ?m.12 ?m.13\ncontext:\n⊢ Nat → Nat\n\nerror: failed to infer `have` declaration type\n\nerror: unsolved goals\n⊢ (fun n => 0 + n) = fun n => n'},

    {t:'p', h:'<code>function_extensionality</code> takes <code>f</code> and <code>g</code> implicitly, which means Lean is expected to read them off the surrounding text. Name the theorem on its own, with nothing around it, and there is no surrounding text: the two arguments become <code>?m.12</code> and <code>?m.13</code> and stay that way. The line under <code>context:</code> is what Lean needs and does not have — a <code>Nat → Nat</code>, twice.'},

    {t:'p', h:'The last two messages are consequences. A <code>have</code> whose right-hand side did not elaborate has no type, so the <code>have</code> fails; with the <code>have</code> gone the proof does not close, so the goal is reported unsolved. Fix the first message and the other three go with it.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'Nothing here says which two functions.',
       src:'theorem zero_add_fun : (fun n : Nat => 0 + n) = (fun n => n) := by\n  have h := function_extensionality\n  exact h (fun n => Nat.zero_add n)'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'<code>@</code> makes every implicit explicit, in order, so you can supply them.',
       src:'theorem zero_add_fun : (fun n : Nat => 0 + n) = (fun n => n) := by\n  have h := @function_extensionality (fun n => 0 + n) (fun n => n)\n  exact h (fun n => Nat.zero_add n)'}},

    /* ============================================================= 11 ===== */

    {t:'h3', s:'11 · <code>Application type mismatch</code>'},

    {t:'state', cap:'<code>update_other</code> wants <code>y ≠ x</code>. It was given <code>x ≠ y</code>.',
     src:'error: Application type mismatch: The argument\n  hne\nhas type\n  x ≠ y\nbut is expected to have type\n  y ≠ x\nin the application\n  update_other f x y v hne'},

    {t:'p', h:'This is not <code>Type mismatch</code>, and the two point you at different places. <code>Type mismatch</code> says <i>the whole term proves the wrong thing</i>; <code>Application type mismatch</code> says <i>the term is fine and one of its arguments is not</i> — and it names the argument, prints its type, prints the type wanted, and shows the application it was found in. Four lines of the message are there so you do not have to count argument positions.'},

    {t:'p', h:'Orientation causes most of these. <code>x ≠ y</code> and <code>y ≠ x</code> are different terms proving different-looking propositions, and which one a lemma asks for is fixed by how that lemma was stated, not by which reads better. <code>Ne.symm</code> converts, and it is a normal argument, so it goes inside the brackets.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       src:'theorem other_flipped (f : Nat → Nat) (x y v : Nat) (hne : x ≠ y) :\n    update f x v y = f y :=\n  update_other f x y v hne'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       src:'theorem other_flipped (f : Nat → Nat) (x y v : Nat) (hne : x ≠ y) :\n    update f x v y = f y :=\n  update_other f x y v (Ne.symm hne)'}},

    {t:'detail', title:'The other place this message comes from — Unit 20, not now', open:false, blocks:[
      {t:'p', h:'Come back to this fold when you get there. It uses induction, which is Unit 20\'s subject, and the point of it is not the mathematics but the fact that the message you will see is the one you have just read, arriving for a reason that has nothing to do with argument order.'},
      {t:'p', h:'When you prove something by induction, everything you introduced <i>before</i> the induction is held fixed while it runs. Below, <code>m</code> was introduced first, so the induction hypothesis is a statement about that one <code>m</code> — and the step needs it at <code>m + 1</code>.'},
      {t:'code', tag:'sketch', cap:'The last line fails.',
       src:'theorem step_down (P : Nat → Nat → Prop) (h0 : ∀ m, P 0 m)\n    (hs : ∀ n m, P n (m + 1) → P (n + 1) m) : ∀ n m, P n m := by\n  intro n m\n  induction n with\n  | zero => exact h0 m\n  | succ k ih => exact hs k m ih'},
      {t:'state', cap:'The argument named is the induction hypothesis itself.',
       src:'error: Application type mismatch: The argument\n  ih\nhas type\n  P k m\nbut is expected to have type\n  P k (m + 1)\nin the application\n  hs k m ih'},
      {t:'p', h:'So when <code>Application type mismatch</code> names an induction hypothesis, the diagnosis is different: the hypothesis is not too weak by accident, it was <i>made</i> too weak by fixing a variable before the induction started. <code>generalizing m</code> puts <code>m</code> back into the statement being proved, and the hypothesis becomes a statement about every <code>m</code>.'},
      {t:'code', tag:'illustration', cap:'Two words added, and the hypothesis takes an argument.',
       src:'theorem step_down (P : Nat → Nat → Prop) (h0 : ∀ m, P 0 m)\n    (hs : ∀ n m, P n (m + 1) → P (n + 1) m) : ∀ n m, P n m := by\n  intro n m\n  induction n generalizing m with\n  | zero => exact h0 m\n  | succ k ih => exact hs k m (ih (m + 1))'}
    ]},

    /* ============================================================= 12 ===== */

    {t:'h3', s:'12 · <code>has already been declared</code>'},

    {t:'state', cap:'One line, and the name in it is the whole diagnosis.',
     src:'error: `update_same` has already been declared'},

    {t:'p', h:'Names in Lean are declared once. The editor gives you the whole course up to but not including the exercise you are on, so the name in front of you is free when you start; you get this message when your own submission declares it twice. The everyday route is copying the solution in to look at it, writing your own attempt underneath, and running both. Delete one.'},

    {t:'p', h:'The other source is a name you did not know was taken. Lean\'s own library is in scope and is full of short names: a demonstration written for this page had to be renamed because <code>cond_true</code> was already a theorem in Lean itself. Same message, same fix — call yours something else. The exhibit below is the first kind, and the error is real: it was produced by declaring <code>update_same</code> a second time on top of Unit 04\'s.'},

    {t:'cmp',
     left: {t:'Broken', kind:'bad', tag:'sketch',
       h:'Correct, complete, and carrying a name Unit 04 has already used.',
       src:'theorem update_same (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  simp [update]'},
     right:{t:'Fixed', kind:'good', tag:'illustration',
       h:'A name of your own. Nothing else changed.',
       src:'theorem update_same_again (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  simp [update]'}},

    /* ==================================================== the three asks === */

    {t:'sec', s:'Three questions you can ask Lean'},

    {t:'p', h:'None of these belongs in a finished proof. They are instruments: you run one, read what comes back, and delete it. All three print their answer under the heading <code>Try this:</code> or as a plain line of output, and none of them changes the proof.'},

    {t:'h3', s:'<code>simp?</code> — which rules fired'},

    {t:'code', tag:'illustration', cap:'A question mark on the end of a tactic you were going to write anyway.',
     src:'theorem simp_question (f : Nat → Nat) (x value : Nat) :\n    update f x value x = value := by\n  simp? [update]'},

    {t:'state', cap:'The <code>[apply]</code> in front is a marker for editors that offer to make the edit for you. The text to copy is what follows it.',
     src:'Try this:\n  [apply] simp only [update, ↓reduceIte]'},

    {t:'p', h:'The proof succeeded and <code>simp?</code> named the two rules it used to do it. That is the instrument\'s whole use: a one-line <code>simp</code> tells you nothing about what it did, and what comes back here is a tactic you can paste in its place, so the proof says what it does instead of delegating.'},

    {t:'h3', s:'<code>exact?</code> — is there a lemma for this'},

    {t:'p', h:'<code>exact?</code> searches everything in scope for a single term that closes the goal on its own. Three runs, on three goals, showing the whole of what it can do here.'},

    {t:'code', tag:'sketch', cap:'Three separate goals, each ending in <code>exact?</code>. The third does not compile, which is the point of it.',
     src:'theorem search_hit (f : Nat → Nat) (x v : Nat) : update f x v x = v := by\n  exact?\n\ntheorem search_absurd (a b : Nat) (h : a = b) : b = a := by\n  exact?\n\ntheorem search_miss (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :\n    update (update f x a) y b x = a := by\n  exact?'},

    {t:'state', cap:'Two answers and a refusal.',
     src:'Try this:\n  [apply] exact update_same f x v\nTry this:\n  [apply] exact some_inj b a (congrArg some (id (Eq.symm h)))\nerror: `exact?` could not close the goal. Try `apply?` to see partial suggestions.'},

    {t:'p', h:'The first is what you hoped for. The second is the warning: the goal was <code>b = a</code> from <code>h : a = b</code>, the answer is <code>h.symm</code>, and what came back instead wraps both sides in <code>some</code>, uses this course\'s own <code>some_inj</code> to unwrap them, and is correct. A search finds <i>a</i> term, not the term you would have written, and it has no taste. Read what it returns before you paste it.'},

    {t:'p', h:'The third is the limit. That goal needs two of your lemmas, one after the other, and <code>exact?</code> looks for one term applied to arguments — not for a proof with steps in it. In a course with no library, most of the goals you are set are of the third kind, so a silent <code>exact?</code> tells you almost nothing about whether you are close.'},

    {t:'h3', s:'<code>#print axioms</code> — what a proof leaned on'},

    {t:'code', tag:'illustration', cap:'Three theorems from earlier units.',
     src:'#print axioms update_shadow\n#print axioms two_add_two\n#print axioms function_extensionality'},

    {t:'state', cap:'Output, one line each.',
     src:'\'update_shadow\' depends on axioms: [propext, Quot.sound]\n\'two_add_two\' does not depend on any axioms\n\'function_extensionality\' depends on axioms: [Quot.sound]'},

    {t:'p', h:'Useful in exactly one situation: you have proved something and you want to know whether it went through machinery you did not intend to use. A proof that computes needs nothing. A proof that used <code>simp</code> on a proposition will usually show <code>propext</code>. If a name you do not recognise ever appears in that list, this is where you find out.'},

    /* ============================================== making the goal bigger === */

    {t:'sec', s:'When two terms print the same'},

    {t:'p', h:'A goal display hides things: implicit arguments, instances, the types of numerals. Most of the time that is a kindness. Now and then it costs you an hour, because the two sides of your equation print identically and Lean insists they are not the same. Two options turn the hiding off, for one declaration each.'},

    {t:'code', tag:'illustration', cap:'<code>set_option … in</code> applies to the single declaration that follows it.',
     src:'set_option pp.explicit true in\ntheorem pp_explicit (f : Nat → Nat) (x v y : Nat) :\n    update f x v y = if y = x then v else f y := by\n  trace_state\n  rfl\n\nset_option pp.numericTypes true in\ntheorem pp_numeric : aliasedAfter 4 = some 5 := by\n  trace_state\n  simp [aliasedAfter]'},

    {t:'state', cap:'What the two <code>trace_state</code> lines printed.',
     src:'f : Nat → Nat\nx v y : Nat\n⊢ @Eq Nat (update f x v y) (@ite Nat (@Eq Nat y x) (instDecidableEqNat y x) v (f y))\n⊢ aliasedAfter (4 : Loc) = some (5 : Val)'},

    {t:'p', h:'<code>pp.explicit</code> writes every application in full: <code>=</code> becomes <code>@Eq Nat</code>, the <code>if</code> becomes <code>@ite</code> with its <code>Decidable</code> instance visible as an argument. That instance is the thing the <code>motive</code> entry above is about, and this is how you see it. <code>pp.numericTypes</code> is narrower — it labels every numeral with its type, which is what you want when <code>4</code> and <code>4</code> are not the same <code>4</code>. Turn both off again; they make everything else unreadable.'},

    /* ===================================================== the whitelist === */

    {t:'sec', s:'Tactics that do not exist here'},

    {t:'p', h:'This course runs on Lean with nothing imported. No Mathlib, no libraries of any kind — which is why <code>exact?</code> had so little to search above, and why almost every lemma you use is one you proved. A tactic you read about on the internet is quite likely to be Mathlib\'s, and here it will not run.'},

    {t:'code', tag:'sketch', cap:'<code>set</code> is Mathlib\'s.',
     src:'theorem set_demo (f : Nat → Nat) (x v : Nat) : update f x v x = v := by\n  set g := update f x v\n  simp [update]'},

    {t:'state', cap:'Two messages: the line did not parse as a tactic, so nothing ran, so the goal is still there.',
     src:'error: unknown tactic\n\nerror: unsolved goals\nf : Nat → Nat\nx v : Nat\n⊢ update f x v x = v'},

    {t:'p', h:'<code>unknown tactic</code> is the friendly case: nothing ran, and you find out at once. The names this course bans do not all fail that loudly.'},

    {t:'tbl', cap:'All compiled against this course\'s context. Where what happens depends on the goal, the row names the goal.',
     head:['what you type', 'what happens'],
     rows:[
       ['<code>set</code>, <code>linarith</code>, <code>ring</code>, <code>aesop</code>', '<code>unknown tactic</code>, then <code>unsolved goals</code>. They are Mathlib\'s and are not here.'],
       ['<code>Function.funext_iff</code>', '<code>Unknown identifier</code>. Use <code>funext</code> in one direction and <code>congrFun</code> in the other.'],
       ['<code>simp_arith</code>', 'On <code>n + 0 = n</code>: closes it, then reports as an <i>error</i> that the name is deprecated — it was shorthand for <code>simp +arith +decide</code>. So the declaration still fails.'],
       ['<code>decide</code>', 'Closes <code>2 + 2 = 4</code>. On <code>n + 0 = n</code>, with a variable in it: <code>Expected type must not contain free variables</code>.'],
       ['<code>omega</code>', '<b>Closes <code>n + 0 = n</code>.</b> It is part of Lean itself, not Mathlib. It will not touch <code>update f x v x = v</code> — it knows arithmetic, not your definitions.']
     ]},

    {t:'note', kind:'warn', title:'The index is the authority, not the compiler',
     h:'The last two rows are the ones to remember. <code>omega</code> compiling does not make it available to you: this course is a fixed vocabulary, every item of it introduced in a named unit, and the tactic index lists all of them. If a tactic is not on that page it does not exist here, whatever Lean does when you type it. The reason is not discipline for its own sake — a goal closed by an arithmetic decision procedure teaches you nothing about the goal, and every proof in this course is set because the proof is the point.'},

    /* ======================================================== the ritual === */

    {t:'sec', s:'What to do when you are stuck'},

    {t:'p', h:'In this order. The first two settle most of it.'},

    {t:'steps', title:'The order', items:[
      {k:'Read the first message', h:'Not the last one, and not all of them. Entry 10 above is one mistake producing four messages, only the first of which is yours.'},
      {k:'Put <code>trace_state</code> above the line that failed', h:'The message tells you what Lean would not accept. The goal tells you what it was working on, which is more often the thing you have got wrong.'},
      {k:'Ask whether the statement is true', h:'Before debugging the proof, try to break the theorem: pick small numbers, drop a hypothesis, and see whether it survives. A stuck proof of a false statement looks exactly like a stuck proof of a true one.'},
      {k:'Check every orientation', h:'<code>x ≠ y</code> against <code>y ≠ x</code>, and which side of each equation is which. <code>Type mismatch</code>, <code>Did not find an occurrence</code> and <code>Application type mismatch</code> are the same mistake wearing three different messages.'},
      {k:'Check the tactic is on the index', h:'If you got it from outside this course, it is a coin flip.'},
      {k:'Ask Lean', h:'<code>simp?</code> if a <code>simp</code> is doing something you cannot see; <code>exact?</code> if you think a single lemma should finish it. Neither will design a proof for you.'},
      {k:'Climb the hints', h:'Four rungs. The first restates the goal, the second names the shape of the argument, the third names the tactic, and the fourth gives you the first line and says what it leaves.'},
      {k:'Open the solution', h:'If you have been through the four rungs and it is late, open it, read the walkthrough beside it, and close the tab. Reconstructing a proof you have read is worth more than another hour of not having one.'}
    ]},

    {t:'p', h:'Nothing on this page needs remembering. Come back to it with a message in front of you. The course itself resumes at Unit 05, with the thing Unit 04 said <code>update</code> could not do: give a cell up.'}

  ]
});
