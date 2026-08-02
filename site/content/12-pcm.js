registerChapter({
  id: 'pcm',
  num: '10',
  phase: 'Phase 1 · The resource algebra',
  title: 'The partial commutative monoid',
  blurb: 'The last two laws of combination — one that needs no hypothesis and one that is false without one — and the structure those laws add up to, written in Lean as a record of data and proofs and instantiated at heaps.',

  orient: {
    youWill: [
      'Prove <code>union_assoc</code> with <i>no</i> hypothesis at all, and say why an operation that prefers its left argument is associative on the nose.',
      'Exhibit two heaps whose combination depends on the order they are written in, and name the hypothesis that rules them out.',
      'Prove <code>union_comm</code> — the only law in this module that needs anything — by reading a disjointness assumption at one address.',
      'Discharge two obligations at once with <code>refine ⟨fun l =&gt; ?_, fun l =&gt; ?_⟩</code>, and read <code>case refine_1</code>.',
      'Prove <code>disjoint_union_left</code>, and obtain <code>disjoint_union_right</code> from it by conjugating with <code>disjoint_symm</code> rather than proving it again.',
      'Say what a monoid is, what makes one commutative, and what the word <i>partial</i> adds — and then write the structure in Lean and instantiate it, so that "heaps form a partial commutative monoid" is a term you can <code>#check</code>.',
      'Prove that a heap determines its complement, and exhibit a partial commutative monoid in which the same statement is false.'
    ],
    needs: [
      'Unit 09: <code>union_of_none</code>, <code>union_of_some</code>, <code>union_eq_none</code> and both unit laws — and the discipline that <code>Heap.union</code> is never opened again.',
      'Unit 08: <code>Heap.disjoint</code> as a statement about every address at once, <code>disjoint_symm</code>, <code>disjoint_empty_left</code>.',
      'Unit 03: <code>funext</code> and <code>congrFun</code>. Unit 02: <code>cases hl : e with</code>, and <code>absurd</code>. Unit 01: <code>rcases</code>, <code>constructor</code>, <code>Or.inl</code>/<code>Or.inr</code>, <code>.1</code>/<code>.2</code>, <code>.mp</code>/<code>.mpr</code>, and how <code>h.foo</code> resolves.'
    ],
    payoff: 'Three units re-bracket a combination — 11, 16 and 34 — and all three do it with <code>union_assoc</code> and the two <code>disjoint_union_*</code> lemmas, and with nothing else. The structure you build here is put away immediately and taken out once, in Unit 38, where the central connective of Module 3 is redefined over it and two of that module\'s laws are proved again, unchanged, without heaps.'
  },

  blocks: [

    /* ------------------------------------------------------------- the thread --- */

    {t:'p', h:'Two laws are left, and they behave as differently as two facts about one operation can. Associativity holds for <i>every</i> triple of heaps, overlapping or not, and its proof mentions disjointness nowhere. Commutativity is false, and there are two one-cell heaps on this page that refute it.'},

    {t:'p', h:'That is not a defect to be repaired. It is the shape of the structure the laws add up to, and the shape has a name — a name worth having only if it denotes something, because a word you can say is worth less than a term you can <code>#check</code>. So the unit ends by writing the structure down in Lean and instantiating it at heaps.'},

    /* ------------------------------------------------------------ associativity --- */

    {t:'sec', s:'Associativity, for every triple of heaps'},

    {t:'code', tag:'verified', cap:'Three heaps, no assumptions. The statement only; its proof is the first exercise.',
     src:'theorem union_assoc (h₁ h₂ h₃ : Heap) :\n    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by'},

    {t:'p', h:'Be suspicious of that missing hypothesis. The operation is left-biased, and left-biasing is exactly a decision about arguments that overlap; if the two bracketings resolved a clash differently, the theorem would be false. They do not, and the reason is short enough to state in one line: at any address, both sides answer with the first of <code>h₁ l</code>, <code>h₂ l</code>, <code>h₃ l</code> that is defined.'},

    {t:'txt', cap:'The answer at one address, on either side of the equation. Nothing in this scan depends on where the brackets are, because the scan is left to right and the brackets do not reorder anything.',
     src:'  h₁ l      if that is  some _\n  h₂ l      otherwise, if that is  some _\n  h₃ l      otherwise'},

    {t:'code', tag:'illustration', cap:'The claim tested where it should hurt: three one-cell heaps that all claim address 0, holding three different values, so every clash the operation can meet is present at once. <code>union_assoc _ _ _</code> is the theorem applied to them; Lean reads the three heaps off the statement, which is why the arguments can be written as underscores.',
     src:'example :\n    Heap.union (Heap.union (Heap.singleton 0 4) (Heap.singleton 0 7)) (Heap.singleton 0 9)\n      = Heap.union (Heap.singleton 0 4) (Heap.union (Heap.singleton 0 7) (Heap.singleton 0 9)) :=\n  union_assoc _ _ _'},

    {t:'p', h:'The left-to-right scan is an argument about the definition, and the definition is the one thing the proof may not name. So the argument has to be rebuilt out of the three lookup lemmas, and rebuilding it decides the shape of the proof. Fix an address with <code>funext</code>. Then ask what <code>h₁ l</code> is. If it is <code>some v</code> the scan stops there on both sides and neither <code>h₂</code> nor <code>h₃</code> is consulted, so that branch closes without asking anything further. If it is <code>none</code> the scan moves on, and the question about <code>h₂ l</code> has to be asked. Two questions, one of them conditional on the answer to the other: three leaves, not four.'},

    {t:'ex',
     id:'m2-5',
     name:'union_assoc',
     hard:false,
     why:'This is the law that makes every later re-bracketing free. Unit 11 re-brackets a split heap and finds that the <i>equation</i> costs nothing and all the work is in the hypotheses; Unit 16 does the same thing for assertions and finds the same split. Both of those units are readable only because this proof is over before they start. The leaf where both of the left-hand heaps are silent is also where <code>union_eq_none</code> is first used in the direction Unit 09 promised it would be needed; the lemma is called on exactly four times in the whole verified corpus, and all four are in this unit.',
     setup:'No hypothesis, so nothing is handed to you: every fact the proof uses has to be manufactured by a case split. The three lookup lemmas are the only things that may be said about <code>Heap.union</code>. Both sides of the equation are heaps, so the proof opens the way every heap equation has opened since Unit 03.',
     goal:'theorem union_assoc (h₁ h₂ h₃ : Heap) :\n    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by',
     hints:[
       'The goal as it stands is <code>⊢ (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃)</code>, and there is nothing else: no hypothesis, and three heaps about which nothing is known. Both sides are the operation applied twice, and they differ only in which application is inside the other. At a fixed address <code>l</code> that reads <code>(h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l</code>: on the left the outer combination scrutinises <code>h₁.union h₂</code>, on the right it scrutinises <code>h₁</code>.',
       'Split on what <code>h₁</code> holds at <code>l</code>. If it holds a value, both sides answer with that value and you are done. If it does not, both sides reduce to a statement about <code>h₂</code> and <code>h₃</code>, and you split again on what <code>h₂</code> holds. Three leaves: <code>h₁</code> speaks; <code>h₁</code> silent and <code>h₂</code> speaking; both silent. The last of those is the only one where you need a fact about the <i>inner</i> combination that neither split gave you — that a combination of two silent heaps is itself silent.',
       '<code>funext</code>, then <code>cases hl : … with</code> nested inside itself. Every fact about <code>Heap.union</code> comes from the three lookup lemmas and nothing else: <code>union_of_some</code> for the leaves where something speaks, <code>union_of_none</code> for the leaves where <code>h₁</code> does not, and <code>union_eq_none</code> — right to left, so <code>.mpr</code> — for the doubly-silent leaf. One of the three leaves is not covered by any of the three, and that one needs a <code>have</code>.',
       '<code>funext l</code>, then <code>cases hl : h₁ l with</code>. That split leaves the goal <i>exactly</i> as it was in both branches, because <code>h₁ l</code> does not occur in it — it is folded inside two combinations — so all it gives you is <code>hl : h₁ l = some v</code> in one branch and <code>hl : h₁ l = none</code> in the other, and every rewrite you make must still be aimed at a combination that does occur: <code>h₁.union h₂</code> or <code>(h₁.union h₂).union h₃</code> on the left, <code>h₁</code> or <code>h₁.union (h₂.union h₃)</code> on the right. Getting an argument to a lookup lemma wrong shows up as a rewrite that finds no occurrence, and the error names the pattern it went looking for.'
     ],
     sol:'theorem union_assoc (h₁ h₂ h₃ : Heap) :\n    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by\n  funext l\n  cases hl : h₁ l with\n  | none =>\n      rw [union_of_none (Heap.union h₂ h₃) hl]\n      cases hl2 : h₂ l with\n      | none =>\n          rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]\n      | some v =>\n          have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2\n          rw [union_of_some h₃ hu, union_of_some h₃ hl2]\n  | some v =>\n      rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]',
     solNote:'Every argument written to a lookup lemma here is either a hypothesis produced by a split or another lookup lemma. Nothing else is available, and nothing else is needed.',
     expl:'The proof is the left-to-right scan, written out as a decision tree. The <code>some v</code> leaf is the easy one and it is easiest on the side you might not expect: on the right, <code>union_of_some (Heap.union h₂ h₃) hl</code> applies directly, because <code>h₁</code> is the left argument there and <code>hl</code> is about <code>h₁</code>. On the left, <code>h₁</code> is buried one bracket deep, so the fact needed is about <code>h₁.union h₂</code>, and it is obtained by feeding <code>union_of_some h₂ hl</code> into <code>union_of_some h₃</code>. The two remaining leaves differ in exactly the same way, and each needs its own way of saying something about the inner combination: when both parts are silent, <code>union_eq_none.mpr</code> builds the fact from the two halves; when <code>h₂</code> speaks and <code>h₁</code> does not, no lemma states that directly and a <code>have</code> assembles it in two rewrites.',
     walk:[
       {tac:'funext l', h:'Turned the equation between heaps into an equation at an arbitrary address and named it <code>l</code>. Everything after this is about one address.'},
       {tac:'cases hl : h₁ l with', h:'Asked the first question. Two branches, each carrying <code>hl</code> saying which answer it assumed. Nothing in the goal changed: <code>h₁ l</code> does not occur in it, because it is still hidden inside two folded combinations.'},
       {tac:'| none => rw [union_of_none (Heap.union h₂ h₃) hl]', h:'On the right-hand side <code>h₁</code> <i>is</i> the left argument, so this rewrite fires there and nowhere else. The right-hand side collapsed from <code>h₁.union (h₂.union h₃) l</code> to <code>h₂.union h₃ l</code>. The explicit argument is the whole of <code>Heap.union h₂ h₃</code>, because that is what stands to the right of <code>h₁</code>.'},
       {tac:'cases hl2 : h₂ l with', h:'Asked the second question, inside the branch where it matters. Again the goal is untouched and the value of the split is entirely in <code>hl2</code>.'},
       {tac:'| none => rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]', h:'Two rewrites. The first needs <code>h₁.union h₂ l = none</code>, which no hypothesis states; <code>union_eq_none.mpr</code> builds it from the pair <code>⟨hl, hl2⟩</code>. That turns the left-hand side into <code>h₃ l</code>. The second turns the right-hand side into <code>h₃ l</code> as well, and <code>rw</code>\'s trailing step closes the goal.'},
       {tac:'| some v => have hu : Heap.union h₁ h₂ l = some v := …', h:'The fact the left-hand side needs is that the inner combination holds <code>v</code> at <code>l</code> — and it holds it because the <i>right</i> part does, which is not what <code>union_of_some</code> says. So it is assembled: rewrite the goal of the <code>have</code> with <code>union_of_none h₂ hl</code>, leaving <code>h₂ l = some v</code>, which is <code>hl2</code>.'},
       {tac:'rw [union_of_some h₃ hu, union_of_some h₃ hl2]', h:'Both sides become <code>some v</code>. The same lemma with the same explicit heap, applied once to the assembled fact and once to the hypothesis.'},
       {tac:'| some v => rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]', h:'The whole branch. <code>union_of_some h₂ hl</code> is a proof that <code>h₁.union h₂ l = some v</code>, and handing it to <code>union_of_some h₃</code> gives a proof about the outer combination. Neither <code>h₂</code> nor <code>h₃</code> was ever consulted, which is what the scan predicted.'}
     ],
     deep:[
       {t:'trace', title:'Down the left spine, to the leaf that needs union_eq_none',
        start:'h₁ h₂ h₃ : Heap\n⊢ (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃)',
        steps:[
          {tac:'funext l',
           state:'h₁ h₂ h₃ : Heap\nl : Loc\n⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l',
           h:'One address, both sides applied to it.'},
          {tac:'cases hl : h₁ l with  (none branch)',
           state:'case none\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l',
           h:'The goal is unchanged. This is the split doing what it does when the term it splits on does not occur in the goal: it produces a hypothesis and nothing else. That hypothesis is the whole point.'},
          {tac:'rw [union_of_none (Heap.union h₂ h₃) hl]',
           state:'case none\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l',
           h:'Only the right-hand side moved. On the left, <code>h₁</code> is not the left argument of the outer combination — <code>h₁.union h₂</code> is — so the rewrite has nothing to match there.'},
          {tac:'cases hl2 : h₂ l with  (none branch)',
           state:'case none.none\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\nhl2 : h₂ l = none\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l',
           h:'Two hypotheses, one goal, and the left-hand side still bracketed the wrong way for either of them. What is missing is a single fact about <code>h₁.union h₂</code>, and the two hypotheses are exactly its two halves.'}
        ],
        done:'rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2] closes it.'},
       {t:'h4', s:'The leaf where a have is unavoidable'},
       {t:'trace', title:'h₁ silent, h₂ speaking',
        start:'case none.some\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\nv : Val\nhl2 : h₂ l = some v\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l',
        steps:[
          {tac:'have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2',
           state:'case none.some\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\nv : Val\nhl2 : h₂ l = some v\nhu : h₁.union h₂ l = some v\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l',
           h:'The context has gained the fact the outer rewrite needs. Compare this with the branch above: there the missing fact was that the inner combination is <i>silent</i>, and <code>union_eq_none.mpr</code> states it; here the missing fact is that the inner combination <i>speaks</i> because its right half does, and there is no lemma for that. Three lookup lemmas cover the two cases where <code>h₁</code> decides the answer and the case where nobody does. This is the fourth case.'}
        ],
        done:'rw [union_of_some h₃ hu, union_of_some h₃ hl2] closes it.'},
       {t:'p', h:'Why there is no fourth lemma is a judgement rather than a fact: a <i>union_of_some_right</i> would need a hypothesis about <code>h₁</code> <i>and</i> one about <code>h₂</code>, which is two arguments to save one <code>have</code>, in one leaf, of one proof.'}
     ],
     pitfall:'Aiming a lookup lemma at the bracket it does not describe. In the doubly-silent leaf, <code>rw [union_of_none h₃ hl]</code> reads <code>h₁</code> off <code>hl</code> and so goes hunting for <code>h₁.union h₃ l</code> — a combination that does not occur anywhere in the goal:<br><br><code>error: Tactic `rewrite` failed: Did not find an occurrence of the pattern<br>&nbsp;&nbsp;h₁.union h₃ l <br>in the target expression<br>&nbsp;&nbsp;(h₁.union h₂).union h₃ l = h₂.union h₃ l</code><br><br>The left argument of the combination you are rewriting is <code>h₁.union h₂</code>, so the hypothesis you supply has to be about <code>h₁.union h₂</code>, and building it is the step.',
     variants:'Add <code>(hd : Heap.disjoint h₁ h₂)</code> to the statement and the proof still compiles — unchanged, with a <code>Variable name `hd` is not explicitly referenced</code> warning — but the theorem stops applying to the three-singleton example above, because those heaps are not disjoint and nothing can supply the argument. A compiled exhibit on this page would stop compiling, which is a sharper account of what an unused hypothesis costs than the warning is. Drop <code>funext</code> and state the law at a fixed <code>l</code> instead, and the same proof works with one line less. Replace <code>union_eq_none.mpr ⟨hl, hl2⟩</code> by <code>hl</code> and you get the rewrite failure above; replace it by <code>hl2</code> and the rewrite fires on the <i>right</i>-hand side instead, so it is the second rewrite that fails, this time hunting for <code>h₂.union h₃ l</code> in a goal that no longer has one.'
    },

    /* ------------------------------------------------------------ commutativity --- */

    {t:'sec', s:'Commutativity, and the two heaps that refute it'},

    {t:'p', h:'Now swap the arguments instead of moving the brackets. Unit 09 combined two one-cell heaps that both claim one address and observed that the answer depends on which one is written first. Here is that observation with the conclusion drawn.'},

    {t:'code', tag:'illustration', cap:'Two heaps, one address, two orders, two answers. Both lines are closed by <code>rfl</code>: the address is a numeral, so the lookups reduce and the combination computes.',
     src:'example : Heap.union (Heap.singleton 0 4) (Heap.singleton 0 7) 0 = some 4 := rfl\n\nexample : Heap.union (Heap.singleton 0 7) (Heap.singleton 0 4) 0 = some 7 := rfl'},

    {t:'p', h:'<code>some 4</code> and <code>some 7</code> are distinct terms, so the two combinations are distinct heaps, so <code>Heap.union h₁ h₂ = Heap.union h₂ h₁</code> is false in general. The counterexample is as small as a counterexample can be: one address, two cells, and the disagreement is the left-bias made visible. Nothing has gone wrong. The operation was defined to be total, and being total means having an answer where the mathematics has none; the answer it has is the one that breaks the symmetry.'},

    {t:'p', h:'What rules the counterexample out is precisely that the two heaps overlap, and the course has a name for the absence of that. Under <code>Heap.disjoint h₁ h₂</code> the two arguments never both speak at the same address, so at every address there is at most one answer to be had — and a rule for preferring one answer over another has nothing to decide.'},

    {t:'code', tag:'verified', cap:'The statement. The hypothesis is implicit in the heaps it mentions and explicit as an argument, so a citation reads <code>union_comm hd</code>.',
     src:'theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :\n    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by'},

    {t:'p', h:'The hypothesis has to be spent, and where it is spent decides the proof. <code>Heap.disjoint h₁ h₂</code> is <code>∀ l, h₁ l = none ∨ h₂ l = none</code>: applied to an address it becomes a disjunction, and a disjunction is taken apart with <code>rcases</code>. That is a different move from the splits in <code>union_assoc</code>, and the difference is what the two moves ask. <code>cases hl : h₁ l with</code> asks <i>what does this heap hold here</i> and has to consider both answers because nothing rules either out. <code>rcases hd l with h | h</code> asks <i>which of the two heaps is the silent one</i> and considers both answers because the hypothesis says at least one of them is true. The first manufactures a fact; the second spends one.'},

    {t:'p', h:'One branch of the disjunction is not enough on its own. Knowing <code>h₁ l = none</code> settles the left-hand side of the equation — the combination defers to <code>h₂</code> — but the right-hand side has <code>h₂</code> in front, and to say what <code>Heap.union h₂ h₁ l</code> is you still have to know what <code>h₂</code> holds. So each <code>rcases</code> branch opens a <code>cases hl :</code> inside it, and the proof is two levels deep for the same reason <code>union_assoc</code> was: the answer on one side is decided by a heap the hypothesis says nothing about.'},

    {t:'ex',
     id:'m2-6',
     name:'union_comm',
     hard:false,
     why:'The one law in this module that needs a hypothesis, and therefore the one that fixes the whole shape of the structure being built: an operation whose commutativity is conditional is not a commutative monoid, and the word for what it is instead is the subject of the second half of this unit. It is also the field of that structure that carries the qualification — the only one — and it is what makes the right-hand unit law free.',
     setup:'The hypothesis <code>hd</code> is a statement about every address; at one address it is a disjunction. Both sides of the goal are combinations, and only one of the two heaps in each is settled by a given branch of that disjunction — so expect a split inside a split. Four leaves this time rather than three, and one mirror-image pair among them closes with different tactics.',
     goal:'theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :\n    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by',
     hints:[
       'At a fixed address the goal is <code>h₁.union h₂ l = h₂.union h₁ l</code>. The hypothesis, at that address, is <code>h₁ l = none ∨ h₂ l = none</code>. Neither disjunct alone tells you what either side of the goal is, because each side scrutinises a different heap.',
       'Take the disjunction apart. In the branch where <code>h₁</code> is silent, the left-hand side is <code>h₂ l</code>; to reach the right-hand side you must know what <code>h₂ l</code> is, so split on it. The other branch is the mirror image.',
       '<code>funext</code>, then <code>rcases</code> on the hypothesis <i>applied to the address</i>, then <code>cases hl : … with</code> inside each branch. Every leaf is one or two rewrites with <code>union_of_none</code> and <code>union_of_some</code>. Nothing here needs <code>union_eq_none</code> and nothing here needs a <code>have</code>: unlike <code>union_assoc</code>, every fact this proof wants is stated by a lemma exactly as it stands.',
       '<code>funext l</code>, then <code>rcases hd l with h | h</code>, then in the first branch <code>rw [union_of_none h₂ h]</code> — which leaves <code>⊢ h₂ l = h₂.union h₁ l</code> — followed by <code>cases hl : h₂ l with</code>. That second split <i>does</i> rewrite the goal, because <code>h₂ l</code> is now standing in it.'
     ],
     sol:'theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :\n    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by\n  funext l\n  rcases hd l with h | h\n  · rw [union_of_none h₂ h]\n    cases hl : h₂ l with\n    | none   => rw [union_of_none h₁ hl, h]\n    | some v => rw [union_of_some h₁ hl]\n  · rw [union_of_none h₁ h]\n    cases hl : h₁ l with\n    | none   => rw [union_of_none h₂ hl]; exact h\n    | some v => rw [union_of_some h₂ hl]',
     solNote:'The two halves are mirror images of each other in the statement and not quite in the proof: one <code>none</code> leaf ends with a second rewrite and the other ends with <code>exact h</code>. That asymmetry is an artefact of which side of the equation the surviving <code>none</code> ends up on. Watch for it rather than fighting it.',
     expl:'Disjointness is used exactly once, at the top of each address: <code>rcases hd l</code> converts the assumption into the knowledge that one named heap is silent here. Everything after that is the lookup lemmas. In the first branch <code>h₁</code> is silent, so the left-hand side becomes <code>h₂ l</code> immediately; the right-hand side has <code>h₂</code> as its left argument and therefore needs to know whether <code>h₂</code> speaks, which is the inner split. In the second branch <code>h₂</code> is silent and the same argument runs with the roles exchanged. No leaf ever has to compare two values, because the hypothesis has ruled out the only case in which two values could disagree.',
     walk:[
       {tac:'funext l', h:'One address.'},
       {tac:'rcases hd l with h | h', h:'Applied the disjointness assumption at <code>l</code>, turning it into a disjunction, and took that disjunction apart. Two branches, <code>case inl</code> with <code>h : h₁ l = none</code> and <code>case inr</code> with <code>h : h₂ l = none</code>. This is the only line in the proof that touches <code>hd</code>.'},
       {tac:'rw [union_of_none h₂ h]', h:'In the first branch, the left-hand side <code>h₁.union h₂ l</code> became <code>h₂ l</code>. The right-hand side is untouched: its left argument is <code>h₂</code>, and <code>h</code> says nothing about <code>h₂</code>.'},
       {tac:'cases hl : h₂ l with', h:'Split on what <code>h₂</code> holds here. Unlike the splits in <code>union_assoc</code>, this one changes the goal: <code>h₂ l</code> is now standing in it as the left-hand side, so it is rewritten to <code>none</code> in one branch and <code>some v</code> in the other.'},
       {tac:'| none => rw [union_of_none h₁ hl, h]', h:'The goal is <code>none = h₂.union h₁ l</code>. The first rewrite turns the right-hand side into <code>h₁ l</code>, leaving <code>none = h₁ l</code>; the second rewrites <code>h₁ l</code> to <code>none</code> using the branch hypothesis, and <code>rw</code>\'s trailing step finishes.'},
       {tac:'| some v => rw [union_of_some h₁ hl]', h:'The goal is <code>some v = h₂.union h₁ l</code>, and <code>h₂</code> speaks, so the right-hand side is <code>some v</code> too. One rewrite.'},
       {tac:'· rw [union_of_none h₁ h]', h:'The second branch, where <code>h₂</code> is silent. Now it is the <i>right</i>-hand side that collapses, to <code>h₁ l</code>, and the left-hand side waits.'},
       {tac:'cases hl : h₁ l with', h:'Split on <code>h₁</code>. Again the goal moves, because <code>h₁ l</code> is now its right-hand side.'},
       {tac:'| none => rw [union_of_none h₂ hl]; exact h', h:'The goal is <code>h₁.union h₂ l = none</code>. One rewrite makes it <code>h₂ l = none</code> — which is not an identity, so <code>rw</code>\'s trailing step does not fire. It is <code>h</code>, the branch hypothesis from the <code>rcases</code>.'},
       {tac:'| some v => rw [union_of_some h₂ hl]', h:'Both sides become <code>some v</code>.'}
     ],
     deep:[
       {t:'trace', title:'One address, one disjunct, one inner split',
        start:'h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\n⊢ h₁.union h₂ l = h₂.union h₁ l',
        steps:[
          {tac:'rcases hd l with h | h  (inl)',
           state:'case inl\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\n⊢ h₁.union h₂ l = h₂.union h₁ l',
           h:'<code>hd</code> is still in the context and is never used again. The branch label <code>inl</code> is <code>Or</code>\'s first constructor, so the left disjunct is what <code>h</code> asserts.'},
          {tac:'rw [union_of_none h₂ h]',
           state:'case inl\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\n⊢ h₂ l = h₂.union h₁ l',
           h:'Half the goal is settled. The other half needs a fact about <code>h₂</code>, which is what the hypothesis does not supply.'},
          {tac:'cases hl : h₂ l with  (none)',
           state:'case inl.none\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\nhl : h₂ l = none\n⊢ none = h₂.union h₁ l',
           h:'The left-hand side has been rewritten by the split itself. Both heaps are now known to be silent here, which is the leaf where the equation is <code>none = none</code> once the right-hand side is unwound.'},
          {tac:'cases hl : h₂ l with  (some)',
           state:'case inl.some\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\nv : Val\nhl : h₂ l = some v\n⊢ some v = h₂.union h₁ l',
           h:'And here the goal is one rewrite from closed. No leaf in this branch ever needed to know that <code>h₁</code> and <code>h₂</code> agree — only that one of them is silent.'}
        ],
        done:'No goals.'},
       {t:'trace', title:'The other branch, and the leaf that does not close by rewriting',
        start:'case inr\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\n⊢ h₁.union h₂ l = h₂.union h₁ l',
        steps:[
          {tac:'rw [union_of_none h₁ h]',
           state:'case inr\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\n⊢ h₁.union h₂ l = h₁ l',
           h:'Mirror image of the first branch: it is the <i>right</i>-hand side that collapses now, because <code>h₂</code> is the left argument there and <code>h</code> is about <code>h₂</code>.'},
          {tac:'cases hl : h₁ l with  (none)',
           state:'case inr.none\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\nhl : h₁ l = none\n⊢ h₁.union h₂ l = none',
           h:'The split rewrote the goal again — <code>h₁ l</code> was standing in it as the right-hand side — so the surviving <code>none</code> has landed on the <i>right</i>. In the first branch it landed on the left.'},
          {tac:'rw [union_of_none h₂ hl]',
           state:'case inr.none\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\nhl : h₁ l = none\n⊢ h₂ l = none',
           h:'And that is the whole of the asymmetry the solution note warns about. The goal is now <code>h₂ l = none</code>, which is not an identity, so <code>rw</code>\'s trailing step has nothing to fire on and the rewrite leaves the goal open. It is <code>h</code>, verbatim.'}
        ],
        done:'exact h'}
     ],
     pitfall:'Writing <code>rcases hd with h | h</code>, without applying <code>hd</code> to an address first. <code>hd</code> is a <code>∀</code>, not a disjunction, and Lean says so: <code>error: Tactic `rcases` failed: `hd : ∀ (l : Loc), h₁ l = none ∨ h₂ l = none` is not an inductive datatype</code>. Disjointness is a statement about every address at once; it becomes something you can take apart only after you have chosen one.',
     variants:'Drop <code>hd</code> and the theorem is false, with the two singletons at address 0 as the witness — and the proof breaks at exactly one leaf, the one where both heaps speak, which is the fold below. Reverse the hypothesis to <code>Heap.disjoint h₂ h₁</code> and the theorem is still true, since disjointness is symmetric; the proof needs its first line changed to <code>rcases disjoint_symm hd l with h | h</code> and nothing else. Weaken the hypothesis to <code>∀ l v w, h₁ l = some v → h₂ l = some w → v = w</code> — the two heaps agree wherever both are defined — and the theorem is <i>still</i> true, but the proof is no longer this one: the top-level <code>rcases</code> becomes a <code>cases hl : h₁ l with</code>, and the leaf where both heaps speak — the leaf disjointness made unreachable, the one the fold below stops at — becomes reachable and closes by rewriting with the hypothesis applied to <code>l</code>, <code>v</code> and <code>w</code>. Compiled. Unit 08 exhibited exactly that weakening and refused it, because the course wants ownership rather than well-definedness, and a reader who takes the weaker hypothesis loses the theorem that a heap determines its complement.'
    },

    {t:'detail', title:'Where a proof without the hypothesis stops', tag:'aside', open:false,
     blocks:[
       {t:'p', h:'Run the same case analysis without the disjointness assumption and everything closes except one leaf. That leaf is the counterexample, in general form.'},
       {t:'code', tag:'sketch', cap:'The same proof shape with <code>hd</code> deleted and the top-level split done on <code>h₁</code> instead.',
        src:'example (h₁ h₂ : Heap) : Heap.union h₁ h₂ = Heap.union h₂ h₁ := by\n  funext l\n  cases hl : h₁ l with\n  | none   => rw [union_of_none h₂ hl]\n              cases hl2 : h₂ l with\n              | none   => rw [union_of_none h₁ hl2, hl]\n              | some v => rw [union_of_some h₁ hl2]\n  | some v => rw [union_of_some h₂ hl]\n              cases hl2 : h₂ l with\n              | none   => rw [union_of_none h₁ hl2, hl]\n              | some w => rw [union_of_some h₁ hl2]'},
       {t:'state', cap:'Three of the four leaves closed. The line-and-column prefix is dropped here and throughout this page.',
        src:'error: unsolved goals\ncase some.some\nh₁ h₂ : Heap\nl : Loc\nv : Val\nhl : h₁ l = some v\nw : Val\nhl2 : h₂ l = some w\n⊢ some v = some w'},
       {t:'p', h:'<code>⊢ some v = some w</code> with nothing relating <code>v</code> and <code>w</code>. That goal is the statement that two heaps which both claim an address claim it with the same value, and it is exactly what disjointness rules out by making the leaf unreachable. This is the general shape of the two-singleton counterexample: put <code>4</code> for <code>v</code> and <code>7</code> for <code>w</code> and you have it.'}
     ]},

    /* ------------------------------------------------------- disjointness bridges --- */

    {t:'sec', s:'Carrying disjointness across a bracket'},

    {t:'p', h:'Associativity moves the brackets in an equation. It does not move anything else, and in practice an equation between combinations never travels alone: it travels with the assumptions that made the combinations legitimate. Re-bracket <code>(h₁.union h₂).union h₃</code> into <code>h₁.union (h₂.union h₃)</code> and you have an equation whose right-hand side mentions <code>h₂.union h₃</code>, about which you now need a disjointness fact — one nobody proved, because the assumption you were given was about <code>h₁.union h₂</code>. The two lemmas that convert between those are what Units 11, 16 and 34 are built out of.'},

    {t:'code', tag:'verified', cap:'Two statements, one proof. The second is the first with the combination on the other side, and it is not proved again.',
     src:'theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by'},

    {t:'p', h:'Read as a biconditional: a combination is disjoint from a third heap exactly when both of its parts are. Forwards it takes an assumption apart; backwards it builds one. Both directions are needed, and by different callers — the forward one when a hypothesis has to be split across a re-bracketing, the backward one when a new combination has to be shown legitimate.'},

    {t:'h3', s:'refine: a term with holes in it'},

    {t:'state', cap:'The forward direction, after <code>constructor</code> and <code>intro hd</code>. Obtained with <code>trace_state</code>.',
     src:'case mp\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\n⊢ h₁.disjoint h₃ ∧ h₂.disjoint h₃'},

    {t:'p', h:'A conjunction, so <code>constructor</code> splits it into two goals — and then each of those is a <code>Heap.disjoint</code>, which is a <code>∀</code>, so each needs its own <code>intro l</code>. Three tactics before any work starts, and two of them are the same tactic written twice. What you actually know is the <i>shape</i> of the answer: it is a pair, and each component is a function of an address. Writing that shape down and leaving the interesting parts blank is what <code>refine</code> is for.'},

    {t:'code', tag:'illustration', cap:'One hole. <code>hb</code> is a real proof handed straight to the second slot; the first slot is left open.',
     src:'example {h₁ h₂ h₃ : Heap} (hd : Heap.disjoint (Heap.union h₁ h₂) h₃)\n    (hb : Heap.disjoint h₂ h₃) : Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by\n  refine ⟨fun l => ?_, hb⟩\n  rcases hd l with h | h\n  · exact Or.inl (union_eq_none.mp h).1\n  · exact Or.inr h'},

    {t:'state', cap:'The goal left by that <code>refine</code>, printed with <code>trace_state</code>. One goal, not two, and <code>l</code> is already in the context.',
     src:'h₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\n⊢ h₁ l = none ∨ h₃ l = none'},

    {t:'p', h:'So <code>refine e</code> is <code>exact e</code> with permission to leave gaps. Every <code>?_</code> in <code>e</code> becomes a goal, in the order they were written, with whatever the surrounding term has bound already in scope — which is why <code>l</code> arrives without an <code>intro</code>. The term takes two liberties Lean allows without comment: the pair is written with the anonymous constructor although the goal is a <code>∧</code> of two <code>Heap.disjoint</code>s, and the components are written as lambdas although <code>Heap.disjoint</code> is a defined name rather than a visible <code>∀</code>. Both are accepted because elaboration unfolds definitions when it needs to see a type\'s shape, exactly as <code>rfl</code> does.'},

    {t:'p', h:'The question mark is load-bearing. A bare <code>_</code> in a term is a request for Lean to work the term out; <code>?_</code> is a promise that you will. The underscore is what a reader reaches for first, so the message it produces is one to recognise.'},

    {t:'code', tag:'sketch', cap:'The same move with <code>_</code> instead of <code>?_</code>.',
     src:'example {h₁ h₂ h₃ : Heap} (hd : Heap.disjoint (Heap.union h₁ h₂) h₃) :\n    Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by\n  refine ⟨fun l => _, fun l => _⟩'},

    {t:'state', cap:'One of two complaints of the same shape, one per underscore — the other is this with <code>h₂</code> for <code>h₁</code> — followed by an <code>unsolved goals</code> for the original goal. Lean has done what was asked — tried to <i>infer</i> a proof — and failed, and the thing it prints is the goal it could not guess. The support page on the goal display describes the same machinery from the other side: an underscore Lean cannot fill is where a metavariable comes from.',
     src:'error: don\'t know how to synthesize placeholder\ncontext:\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₁ l = none ∨ h₃ l = none'},

    {t:'p', h:'With two holes there are two goals, and Lean has to name them. It numbers them in the order they were written, so they arrive as <code>case refine_1</code> and <code>case refine_2</code>, under whatever case label was already in force:'},

    {t:'state', cap:'The first of the two goals produced by <code>refine ⟨fun l =&gt; ?_, fun l =&gt; ?_⟩</code>. The second is the same with <code>h₂</code> in place of <code>h₁</code>; both are printed below.',
     src:'case mp.refine_1\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₁ l = none ∨ h₃ l = none'},

    {t:'detail', title:'Both goals, as Lean prints them at once', tag:'aside', open:false,
     blocks:[
       {t:'state', cap:'A blank line separates the two goals, and every later tactic sees only the first — which is why the proof continues with a focus dot.',
        src:'case mp.refine_1\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₁ l = none ∨ h₃ l = none\n\ncase mp.refine_2\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₂ l = none ∨ h₃ l = none'}
     ]},

    {t:'ex',
     id:'m2-7',
     name:'disjoint_union_left / disjoint_union_right',
     hard:true,
     why:'Every re-bracketing in the rest of the course is one of these two, in one direction or the other. Unit 11\'s associativity of splitting has three moving parts and two of them are these — <code>disjoint_union_left.mp</code> to take a disjointness apart and <code>disjoint_union_right.mpr</code> to build a new one, with <code>union_assoc</code> supplying the equation between the two. Unit 16 proves the associativity of the central connective of this logic with the same three, and Unit 34 uses them again. They are also the first pair of theorems in this course where the second is <i>derived</i> from the first rather than proved again, a habit best acquired here, where the saving is small enough to check by eye.',
     setup:'An <code>↔</code> whose two sides are both statements about every address. Three obligations in total: the backward direction, and the two components of the conjunction the forward direction produces. In the backward direction the conjunction can be taken apart in the <code>intro</code> pattern, and the address introduced in the same <code>intro</code>. The second theorem takes no new ideas at all: <code>disjoint_symm</code> turns each of its four disjointness statements into one the first theorem can speak about.',
     goal:'theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by\n  sorry\n\ntheorem disjoint_union_right {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by',
     hints:[
       'Forwards: from "the combination is disjoint from <code>h₃</code>" produce two facts, that <code>h₁</code> is and that <code>h₂</code> is. Backwards: from those two produce the first. At a single address every one of these statements is a disjunction of two lookups being <code>none</code>.',
       'At an address, the assumption gives you either "the combination is silent here" or "<code>h₃</code> is silent here". The second case proves both halves at once, and the same term proves both. The first case turns on the one fact about combinations Unit 09 proved in <i>both</i> directions: a combination is silent at an address exactly when both of its parts are. Forwards you read that left to right; backwards, right to left, and that is the only leaf of the backward direction with any content.',
       'Forwards the goal is a pair, each of whose components quantifies over addresses: <code>refine</code> writes the pair and the two lambdas at once and leaves the two bodies as goals, so the address arrives without an <code>intro</code>. Inside each component, <code>rcases</code> on the assumption applied to the address, and then <code>union_eq_none</code> — <code>.mp</code> forwards, <code>.mpr</code> backwards — with <code>Or.inl</code>, <code>Or.inr</code> and <code>.1</code>/<code>.2</code> doing the rest. For the second theorem write no proof of your own: <code>disjoint_symm</code> conjugates a disjointness statement, and conjugating the first theorem by it gives the second.',
       '<code>constructor</code>, then <code>· intro hd</code> and <code>refine ⟨fun l => ?_, fun l => ?_⟩</code>, which leaves <code>case mp.refine_1</code> with <code>l : Loc</code> in context and <code>⊢ h₁ l = none ∨ h₃ l = none</code>. Each of the two forward components is then one <code>rcases hd l with h | h</code> and two <code>exact</code>s; the backward direction is an <code>rcases</code> with another <code>rcases</code> inside one of its branches.'
     ],
     sol:'theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by\n  constructor\n  · intro hd\n    refine ⟨fun l => ?_, fun l => ?_⟩\n    · rcases hd l with h | h\n      · exact Or.inl (union_eq_none.mp h).1\n      · exact Or.inr h\n    · rcases hd l with h | h\n      · exact Or.inl (union_eq_none.mp h).2\n      · exact Or.inr h\n  · intro ⟨ha, hb⟩ l\n    rcases ha l with h | h\n    · rcases hb l with h\' | h\'\n      · exact Or.inl (union_eq_none.mpr ⟨h, h\'⟩)\n      · exact Or.inr h\'\n    · exact Or.inr h\n\ntheorem disjoint_union_right {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by\n  constructor\n  · intro hd\n    have h\' := disjoint_union_left.mp (disjoint_symm hd)\n    exact ⟨disjoint_symm h\'.1, disjoint_symm h\'.2⟩\n  · intro ⟨ha, hb⟩\n    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)',
     solNote:'Fifteen lines of proof and then six. The second theorem never mentions an address, a lookup lemma or a disjunction: everything it needs has already been proved, and its whole content is the bookkeeping of turning four statements round.',
     expl:'The forward direction rests on one observation: at an address, the assumption offers two cases and only one of them is interesting. If <code>h₃</code> is silent there, both halves of the conclusion are immediate, and the same term proves both. If instead the combination is silent there, <code>union_eq_none.mp</code> splits that into the two parts being silent, and the first half of the conclusion wants the first of those and the second half wants the second. The backward direction runs the same lemma in reverse: the interesting case is the one where both parts are silent, and <code>union_eq_none.mpr</code> assembles that into a statement about the combination. The mirror theorem then follows because disjointness is symmetric and the first theorem is about combinations on the left: conjugate the assumption by <code>disjoint_symm</code>, apply, conjugate the two results back.',
     walk:[
       {tac:'constructor', h:'Split the <code>↔</code> into <code>case mp</code> and <code>case mpr</code>.'},
       {tac:'intro hd', h:'Named the assumption <code>hd : (h₁.union h₂).disjoint h₃</code>. The goal is a conjunction of two statements about every address.'},
       {tac:'refine ⟨fun l => ?_, fun l => ?_⟩', h:'Wrote the shape of the answer — a pair whose components are functions of an address — and left both bodies open. Two goals, <code>case mp.refine_1</code> and <code>case mp.refine_2</code>, each already carrying <code>l : Loc</code>. Replacing this by <code>constructor</code> costs two extra <code>intro l</code>s and produces goals named <code>left</code> and <code>right</code> instead.'},
       {tac:'· rcases hd l with h | h', h:'Applied the assumption at <code>l</code> and took the disjunction apart. First branch: the combination is silent at <code>l</code>. Second: <code>h₃</code> is.'},
       {tac:'· exact Or.inl (union_eq_none.mp h).1', h:'The combination is silent, so by <code>union_eq_none</code> both its parts are; <code>.1</code> is the part about <code>h₁</code>, which is the left disjunct of this goal. Every step here is a projection of something already proved.'},
       {tac:'· exact Or.inr h', h:'<code>h₃</code> is silent, which is the right disjunct verbatim. This branch does not mention <code>h₁</code>, <code>h₂</code> or the combination at all — which is why the same two lines close the second component with only <code>.1</code> changed to <code>.2</code>.'},
       {tac:'· intro ⟨ha, hb⟩ l', h:'The backward direction. The conjunction is taken apart in the pattern and the address is introduced in the same <code>intro</code>, because the goal after the conjunction is consumed is still a <code>∀</code>.'},
       {tac:'rcases ha l with h | h', h:'<code>ha</code> says <code>h₁</code> is disjoint from <code>h₃</code>; at <code>l</code> that is a disjunction. If <code>h₃</code> is the silent one, the goal is closed by the last line and <code>hb</code> is never consulted.'},
       {tac:'· rcases hb l with h\' | h\'', h:'Only reached when <code>h₁</code> is silent at <code>l</code>. Now ask the same question of <code>h₂</code>.'},
       {tac:'· exact Or.inl (union_eq_none.mpr ⟨h, h\'⟩)', h:'Both parts silent, so the combination is silent: <code>union_eq_none.mpr</code> takes the pair of facts and returns the fact about the combination. This is the only place in the proof where a new fact is built rather than projected.'},
       {tac:'· exact Or.inr h\'', h:'<code>h₃</code> silent, from <code>hb</code> this time.'},
       {tac:'· exact Or.inr h', h:'<code>h₃</code> silent, from <code>ha</code>, in the case where <code>hb</code> was never needed.'},
       {tac:'have h\' := disjoint_union_left.mp (disjoint_symm hd)  (right law)', h:'The whole idea of the mirror theorem. <code>hd : h₁.disjoint (h₂.union h₃)</code> has the combination on the wrong side; <code>disjoint_symm hd</code> puts it on the left, where the theorem just proved can speak about it. <code>h\'</code> is then <code>h₂.disjoint h₁ ∧ h₃.disjoint h₁</code>.'},
       {tac:'exact ⟨disjoint_symm h\'.1, disjoint_symm h\'.2⟩', h:'Both components are the right facts with their heaps the wrong way round, so both are conjugated back. Nothing about unions is used.'},
       {tac:'exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)  (right law, backwards)', h:'The same conjugation as one term: turn the two assumptions round, feed them to the backward direction of the left law, turn the result round.'}
     ],
     deep:[
       {t:'trace', title:'Forwards, into the first component',
        start:'case mp\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\n⊢ h₁.disjoint h₃ ∧ h₂.disjoint h₃',
        steps:[
          {tac:'refine ⟨fun l => ?_, fun l => ?_⟩',
           state:'case mp.refine_1\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₁ l = none ∨ h₃ l = none',
           h:'The first of two goals. Both the pair and the two lambdas were written by hand, so both the conjunction and the two <code>∀</code>s are gone in one step. The definition <code>Heap.disjoint</code> has been unfolded in the display, because the goal is now the body of that definition at a particular address.'},
          {tac:'rcases hd l with h | h  (inl)',
           state:'case mp.refine_1.inl\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\nh : h₁.union h₂ l = none\n⊢ h₁ l = none ∨ h₃ l = none',
           h:'The interesting branch. <code>h</code> is about the combination and the goal is about a part, and <code>union_eq_none</code> is the only bridge between those two.'}
        ],
        done:'exact Or.inl (union_eq_none.mp h).1'},
       {t:'trace', title:'Backwards, where the fact is built rather than projected',
        start:'case mpr\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\n⊢ h₁.union h₂ l = none ∨ h₃ l = none',
        steps:[
          {tac:'rcases ha l with h | h  then  rcases hb l with h\' | h\'',
           state:'case mpr.inl.inl\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\nh : h₁ l = none\nh\' : h₂ l = none\n⊢ h₁.union h₂ l = none ∨ h₃ l = none',
           h:'The one leaf out of three that needs anything. The goal is still the whole disjunction — <code>rcases</code> took the two <i>hypotheses</i> apart and left the goal alone — so the branch has to choose a disjunct as well as prove it, which is what the <code>Or.inl</code> below does. Two silent parts in the context, and the left disjunct says their combination is silent. The other two leaves both have <code>h₃ l = none</code> to hand and choose <code>Or.inr</code>.'}
        ],
        done:'exact Or.inl (union_eq_none.mpr ⟨h, h\'⟩)'},
       {t:'h4', s:'What proving the mirror image again would cost'},
       {t:'p', h:'The direct proof of the right-hand law exists and compiles. It is the left-hand proof with every disjointness statement written the other way round, and with <code>Or.inl</code> and <code>Or.inr</code> exchanged wherever the combination has moved side.'},
       {t:'code', tag:'illustration', cap:'The mirror theorem proved from scratch: fifteen lines of proof against six, and not one new idea in any of them.',
        src:'example {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by\n  constructor\n  · intro hd\n    refine ⟨fun l => ?_, fun l => ?_⟩\n    · rcases hd l with h | h\n      · exact Or.inl h\n      · exact Or.inr (union_eq_none.mp h).1\n    · rcases hd l with h | h\n      · exact Or.inl h\n      · exact Or.inr (union_eq_none.mp h).2\n  · intro ⟨ha, hb⟩ l\n    rcases ha l with h | h\n    · exact Or.inl h\n    · rcases hb l with h\' | h\'\n      · exact Or.inl h\'\n      · exact Or.inr (union_eq_none.mpr ⟨h, h\'⟩)'},
       {t:'p', h:'Nine lines saved on one theorem is not the argument. The argument is that a development which proves both members of every symmetric pair proves each of them twice for the rest of its life: every later lemma about combinations comes in a left and a right form, and each of those has a proof to maintain. A conjugation is one line and cannot drift out of step with the theorem it conjugates.'}
     ],
     pitfall:'Getting <code>.1</code> and <code>.2</code> the wrong way round between the two components. They are the two halves of <code>union_eq_none.mp h</code>, so the first component of the conjunction wants <code>.1</code> and the second wants <code>.2</code>; swapping them gives <code>error: Application type mismatch: The argument (union_eq_none.mp h).right has type h₂ l = none but is expected to have type h₁ l = none</code>. Lean prints the field names rather than the numerals, because <code>.1</code> and <code>.2</code> are shorthand for <code>left</code> and <code>right</code>.',
     variants:'Weaken the forward direction to a single implication and Unit 11 loses the ability to establish a new combination as legitimate. Drop the backward direction of the <i>right</i> law and the same unit loses the last of its three lines. State the left law with the combination on the right of <code>Heap.disjoint</code> and you have written the right law, so there is nothing between them but the argument order. What does <i>not</i> hold is any version with the conjunction weakened to a disjunction, and one address refutes it. Take <code>h₁ = Heap.empty</code>, <code>h₂ = Heap.singleton 0 4</code>, <code>h₃ = Heap.singleton 0 7</code>. The disjunction holds, by its left half: <code>disjoint_empty_left</code> gives <code>Heap.disjoint Heap.empty h₃</code> outright. The combination does not: <code>union_empty_left</code> rewrites <code>Heap.union Heap.empty (Heap.singleton 0 4)</code> to <code>Heap.singleton 0 4</code>, and <code>singleton_disjoint_iff</code> then asks for <code>(0 : Loc) ≠ 0</code>. Both halves compile. The point of failure is exactly that one part can be silent everywhere <code>h₃</code> speaks while the other is not — and the combination speaks wherever either part does.'
    },

    /* ------------------------------------------------------------- naming it --- */

    {t:'sec', s:'What has just been proved'},

    {t:'p', h:'Stand back and count what is now known. <code>Heap.union</code> combines any two heaps; <code>Heap.empty</code> is neutral for it on both sides; its bracketing never matters; and its argument order never matters, provided the two arguments are disjoint. About <code>Heap.disjoint</code> itself: it is symmetric, and the empty heap is disjoint from everything. <code>disjoint_union_left</code> and its mirror are not on that list, and nothing below asks for them — they are the first sign that heaps satisfy more than what follows demands. Take the word <i>heap</i> out of the six that are on it and nothing is left but an operation, a distinguished element, a relation and the laws relating them: the description of a structure, and the structure has a name. The name earns nothing on its own, so here is the thing it generalises first.'},

    {t:'p', h:'A <b>monoid</b> is a set with a binary operation on it and a distinguished element, such that the operation is associative and the distinguished element is neutral on both sides. Three examples you already have:'},

    {t:'tbl', cap:'Three monoids. The operation is total in all three, and the last one shows that commutativity is a genuine extra demand rather than something that comes free with the definition.',
     head:['set', 'operation', 'unit', 'is the order irrelevant?'],
     rows:[
       ['<code>Nat</code>', 'addition', '<code>0</code>', 'yes'],
       ['<code>Nat</code>', 'multiplication', '<code>1</code>', 'yes'],
       ['functions <code>Nat → Nat</code>', 'composition, <code>fun n =&gt; f (g n)</code>', '<code>fun n =&gt; n</code>', '<b>no</b>']
     ]},

    {t:'p', h:'A <b>commutative monoid</b> is a monoid whose operation also satisfies <i>a</i> · <i>b</i> = <i>b</i> · <i>a</i>. The first two rows qualify and the third does not: doubling then adding one is not adding one then doubling. That is the whole content of the adjective — one extra law, which some monoids have and some do not.'},

    {t:'p', h:'Now hold heaps against that definition. Associativity: proved, unconditionally. Neutrality of <code>Heap.empty</code>: proved, on both sides, in Unit 09. Commutativity: refuted, by two one-cell heaps. So heaps under combination are a monoid and not a commutative one, and stopping there would be true and useless, because the whole design of the operation is that the counterexamples are heaps the course promises never to combine. The missing ingredient is not another law. It is a way of saying <i>which pairs are legitimate arguments</i>, and then asking for commutativity only on those.'},

    {t:'defn', term:'Partial commutative monoid',
     h:'A set <i>M</i>, a binary operation on it, a distinguished element <i>e</i>, and a binary relation <i>valid</i> on <i>M</i>, such that: the operation is associative; <i>e</i> is neutral on the left; the operation is commutative <b>on valid pairs</b>; <i>e</i> is valid with everything; and validity is symmetric.',
     cap:'Five requirements, and exactly one of them is qualified. That qualification is the word <i>partial</i>: a law that holds only where the operation is meant to be applied.'},

    {t:'p', h:'Neutrality on the right is missing from that list and is not an oversight. It follows: <i>e</i> is valid with <i>a</i>, so validity is symmetric and <i>a</i> is valid with <i>e</i>, so the operation commutes on that pair, so <i>a</i> · <i>e</i> = <i>e</i> · <i>a</i> = <i>a</i>. Five requirements rather than six, and the sixth is a two-line consequence.'},

    {t:'p', h:'One design decision is buried in that definition, and the standard presentation makes the other choice. Written on paper, a partial commutative monoid usually qualifies <i>every</i> law: associativity holds when both sides are defined, neutrality when the relevant pair is valid, and so on. That is the honest description of an operation which genuinely has no answer on invalid pairs. It is not the description of the operation this course has. <code>Heap.union</code> is total — Unit 09 spent a page on why it had to be — so associativity and left neutrality hold outright, and demanding less of them would throw away theorems that are already proved. The cost of the standard presentation is the same cost Unit 09 measured: every axiom acquires a hypothesis, so every use of every axiom acquires an obligation, and a re-bracketing that is currently one rewrite becomes a rewrite and two side conditions.'},

    /* --------------------------------------------------------- building it --- */

    {t:'sec', s:'Writing the structure down'},

    {t:'p', h:'A definition given in English is a definition you can only check by hand. Lean has a way of packaging data together with the laws it satisfies — the same keyword that packaged a heap with its domain in Unit 05\'s rejected alternative — and the packaging works because a proof is a term, so a law can be a field like any other.'},

    {t:'anat', tag:'verified',
     src:'structure PCM (M : Type) where\n  op         : M → M → M\n  unit       : M\n  valid      : M → M → Prop\n  op_comm    : ∀ a b, valid a b → op a b = op b a\n  op_assoc   : ∀ a b c, op (op a b) c = op a (op b c)\n  unit_left  : ∀ a, op unit a = a\n  valid_unit : ∀ a, valid unit a\n  valid_comm : ∀ a b, valid a b → valid b a',
     parts:[
       {m:'PCM (M : Type)', h:'The carrier is a parameter, not a field: a <code>PCM Heap</code> and a <code>PCM Nat</code> are values of different types, so nothing can accidentally combine a heap with a number. <code>M</code> ranges over <code>Type</code>, which is where <code>Heap</code> lives — not over <code>Prop</code>, where the laws live.'},
       {m:'op         : M → M → M', h:'The operation, as data. Total, because a Lean function is; the intended partiality is expressed by <code>valid</code>, not by the type of <code>op</code>.'},
       {m:'valid      : M → M → Prop', h:'The relation that says which pairs are legitimate arguments. It is a field like <code>op</code> is, so a partial commutative monoid is a carrier <i>with a choice of validity</i>: the same operation with a wider validity is a different structure, and the last section of this unit is a pair of models that differ in that one field and nowhere else.'},
       {m:'op_comm    : ∀ a b, valid a b → op a b = op b a', h:'The one qualified law. Look at where the hypothesis sits — inside the field, as an ordinary argument to the ordinary function type <code>∀ a b, …</code>. A field whose type is a <code>Prop</code> is a proof obligation; filling it in means supplying a proof.'},
       {m:'op_assoc   : ∀ a b c, op (op a b) c = op a (op b c)', h:'Unqualified, and that is the demand the total encoding makes possible. A structure written this way accepts fewer things than the textbook definition does, and everything it accepts satisfies more.'},
       {m:'valid_unit : ∀ a, valid unit a', h:'Without this, <code>unit</code> could be an element the operation is never allowed to be applied to, and left neutrality would be a law about a case that never arises. With it, right neutrality is derivable — which is why the field list stops here.'}
     ]},

    {t:'p', h:'Eight fields: three of data and five of proof. Instantiating it means supplying eight values, and every one of the five proofs is a theorem in this module, in this order:'},

    {t:'tbl', cap:'The structure, field by field, against what heaps supply. The last column is the whole point of the word <i>partial</i>: exactly one law needs the relation, and it is the one that was refuted without it.',
     head:['field', 'what it demands', 'what heaps supply', 'needs disjointness?'],
     rows:[
       ['<code>op</code>', 'a total binary operation', '<code>Heap.union</code>', '—'],
       ['<code>unit</code>', 'an element', '<code>Heap.empty</code>', '—'],
       ['<code>valid</code>', 'a binary relation', '<code>Heap.disjoint</code>', '—'],
       ['<code>op_comm</code>', 'commutativity on valid pairs', '<code>union_comm</code>', '<b>yes</b>'],
       ['<code>op_assoc</code>', 'associativity, unqualified', '<code>union_assoc</code>', 'no'],
       ['<code>unit_left</code>', 'left neutrality, unqualified', '<code>union_empty_left</code>', 'no'],
       ['<code>valid_unit</code>', 'the unit is valid with everything', '<code>disjoint_empty_left</code>', '—'],
       ['<code>valid_comm</code>', 'validity is symmetric', '<code>disjoint_symm</code>', '—']
     ]},

    {t:'ex',
     id:'x23',
     name:'heapPCM',
     hard:false,
     why:'This is where "heaps form a partial commutative monoid" stops being a sentence and becomes a term with a type. Nothing new is proved: the exercise is the table above, typed into Lean, and the value of it is that Lean checks the table. It is also the object Unit 38 generalises over: the central connective of Module 3 is redefined there for an arbitrary <code>PCM</code>, and this is the instance that makes the redefined version cover the case you care about.',
     setup:'The <code>where</code> syntax for building a structure value: one line per field, in any order, each naming a term of that field\'s type. Every field is a definition or a theorem you already have. Two of the eight need more than a bare name, and the reason is the difference between implicit and explicit binders that Unit 09 settled — a field whose type is <code>∀ a b, …</code> demands a function taking <code>a</code> and <code>b</code>, and a theorem whose heaps are implicit is not one.',
     goal:'def heapPCM : PCM Heap where\n  op         :=',
     hints:[
       'Eight fields. Three want data: a function <code>Heap → Heap → Heap</code>, an element of <code>Heap</code>, and a relation <code>Heap → Heap → Prop</code>. Five want proofs, and every one of the five is a theorem proved in Unit 09 or on this page.',
       'Work down the table: the operation, the empty heap, disjointness, then commutativity, associativity, left neutrality, that the empty heap is disjoint from everything, and that disjointness is symmetric.',
       'The five theorems are <code>union_comm</code>, <code>union_assoc</code>, <code>union_empty_left</code>, <code>disjoint_empty_left</code> and <code>disjoint_symm</code>. Three of them can be written as bare names. Two cannot, because their heap arguments are implicit and the field wants them explicit.',
       '<code>op := Heap.union</code>, <code>unit := Heap.empty</code>, <code>valid := Heap.disjoint</code>, and for the two with implicit binders, wrap them: <code>op_comm := fun _ _ hd => union_comm hd</code>. The underscores are the two heaps, which the field supplies and <code>union_comm</code> infers from <code>hd</code>.'
     ],
     sol:'def heapPCM : PCM Heap where\n  op         := Heap.union\n  unit       := Heap.empty\n  valid      := Heap.disjoint\n  op_comm    := fun _ _ hd => union_comm hd\n  op_assoc   := union_assoc\n  unit_left  := union_empty_left\n  valid_unit := disjoint_empty_left\n  valid_comm := fun _ _ hd => disjoint_symm hd',
     solNote:'Six of the eight lines are a bare name and nothing else, three of them theorem names. That is what it looks like when a structure has been designed around theorems that already exist, and it is the reason this exercise is a [D 1] rather than the module\'s hardest.',
     expl:'A structure value is a record, and <code>where</code> is the syntax for filling one in field by field. The three data fields take the definitions from Units 05 and 08 unchanged. The five law fields take proofs, and a proof is a term, so a theorem name is a legitimate thing to write there — provided its type matches the field\'s type <i>exactly</i>. That is where the two wrapped fields come from: <code>op_assoc</code> demands <code>∀ a b c, …</code> and <code>union_assoc</code> takes its three heaps explicitly, so the names line up; <code>op_comm</code> demands <code>∀ a b, valid a b → …</code>, and <code>union_comm</code> takes its two heaps implicitly, so it is not a function of two heaps at all until it is wrapped in one.',
     walk:[
       {tac:'op := Heap.union', h:'The field\'s type is <code>Heap → Heap → Heap</code> and <code>Heap.union</code> has that type. Nothing is being proved yet; this line is data.'},
       {tac:'unit := Heap.empty', h:'An element of the carrier.'},
       {tac:'valid := Heap.disjoint', h:'The relation. Everything qualified in the definition is qualified by this, so this line is the one that decides what the structure means for heaps.'},
       {tac:'op_comm := fun _ _ hd => union_comm hd', h:'The field wants a function of two heaps and a validity proof. <code>union_comm</code> is a function of a validity proof alone, its heaps being implicit, so the lambda supplies the two explicit arguments and discards them — Lean recovers them from the type of <code>hd</code>.'},
       {tac:'op_assoc := union_assoc', h:'A bare name, because <code>union_assoc</code>\'s three heaps are explicit and the field asks for a function of three heaps.'},
       {tac:'unit_left := union_empty_left', h:'Left neutrality only. Right neutrality is not a field, so <code>union_empty_right</code> is not used here at all — although it is true, and the derivation below shows the structure could have re-derived it.'},
       {tac:'valid_unit := disjoint_empty_left', h:'<code>disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h</code>, whose one heap is explicit, matching <code>∀ a, valid unit a</code>.'},
       {tac:'valid_comm := fun _ _ hd => disjoint_symm hd', h:'Wrapped for the same reason as <code>op_comm</code>: <code>disjoint_symm</code>\'s heaps are implicit.'}
     ],
     deep:[
       {t:'trace', title:'What a law field actually asks for',
        start:'⊢ ∀ (a b : Heap), a.disjoint b → a.union b = b.union a',
        steps:[
          {tac:'intro a b hd',
           state:'a b : Heap\nhd : a.disjoint b\n⊢ a.union b = b.union a',
           h:'Written <code>op_comm := by intro a b hd; exact union_comm hd</code> instead of as a term, the field opens as a goal with an empty context — a proof obligation and nothing else in scope. After the <code>intro</code> it is <code>union_comm</code>\'s statement with the implicit binders made explicit, which is exactly what the lambda in the solution supplies.'}
        ],
        done:'exact union_comm hd'},
       {t:'h4', s:'The term you have built'},
       {t:'code', tag:'illustration', cap:'Three queries against the finished definition.',
        src:'#check heapPCM\n#check heapPCM.op\n#check heapPCM.op_comm'},
       {t:'state', cap:'<code>heapPCM</code> is a value of type <code>PCM Heap</code>; its fields are reached by the same dot notation as any other projection, and the law fields come back as statements about <code>heapPCM.op</code> and <code>heapPCM.valid</code> rather than about <code>Heap.union</code> and <code>Heap.disjoint</code>.',
        src:'heapPCM : PCM Heap\nheapPCM.op : Heap → Heap → Heap\nheapPCM.op_comm : ∀ (a b : Heap), heapPCM.valid a b → heapPCM.op a b = heapPCM.op b a'},
       {t:'h4', s:'Right neutrality, derived for every PCM at once'},
       {t:'p', h:'The claim above — that the missing sixth law follows from the five — can now be checked, and checked for an arbitrary structure rather than for heaps. This is the first proof in the course that is about a <code>PCM</code> and not about a heap, and it is one line.'},
       {t:'code', tag:'illustration', cap:'<code>k</code> is any partial commutative monoid whatever. The proof turns the goal round with <code>op_comm</code> and then closes it with <code>unit_left</code>.',
        src:'example {M : Type} (k : PCM M) (a : M) : k.op a k.unit = a := by\n  rw [k.op_comm a k.unit (k.valid_comm k.unit a (k.valid_unit a)), k.unit_left a]'},
       {t:'trace', title:'Two rewrites, no carrier',
        start:'M : Type\nk : PCM M\na : M\n⊢ k.op a k.unit = a',
        steps:[
          {tac:'rw [k.op_comm a k.unit (k.valid_comm k.unit a (k.valid_unit a))]',
           state:'M : Type\nk : PCM M\na : M\n⊢ k.op k.unit a = a',
           h:'The argument to <code>op_comm</code> is the validity proof it demands, and it is built by two more field projections: <code>valid_unit</code> gives validity one way round, <code>valid_comm</code> turns it round. Nothing here knows what <code>M</code> is.'}
        ],
        done:'rw [k.unit_left a]'},
       {t:'p', h:'Read against <code>heapPCM</code>, that one line is a second proof of <code>union_empty_right</code> — the theorem Unit 09 needed a <code>funext</code> and a case split for. It is shorter because it is not allowed to look at heaps, and being unable to look at things is what makes an argument transfer.'}
     ],
     pitfall:'Writing the theorem names bare for all five laws. Two of them are stated with implicit heaps, and Lean reports the mismatch as a type mismatch on the field, naming the metavariables that stand for the arguments it could not fix:<br><br><code>error: Type mismatch<br>&nbsp;&nbsp;union_comm <br>has type<br>&nbsp;&nbsp;Heap.disjoint ?m.2 ?m.3 → Heap.union ?m.2 ?m.3 = Heap.union ?m.3 ?m.2<br>but is expected to have type<br>&nbsp;&nbsp;∀ (a b : Heap), a.disjoint b → a.union b = b.union a</code><br><br>The same message arrives for <code>valid_comm</code>, with <code>disjoint_symm</code>\'s type in place of <code>union_comm</code>\'s and a different pair of metavariable numbers. Both are fixed by <code>fun _ _ hd =&gt; …</code>, and neither is a defect in the theorems: the implicit binders are what make <code>union_comm hd</code> readable at every other call site in the course.',
     variants:'Take <code>valid := fun _ _ => True</code>, so that every pair is legitimate, and exactly one field stops being fillable — <code>op_comm</code>, which now asks for commutativity of <code>Heap.union</code> outright:<br><br><code>error: Application type mismatch: The argument h has type True but is expected to have type a.disjoint b</code><br><br>That is the counterexample of the first half of this unit, arriving as a failed field. Take <code>op := fun h₁ h₂ => Heap.union h₂ h₁</code> instead and every field can still be filled — <code>unit_left</code> becomes <code>union_empty_right</code>, <code>op_assoc</code> becomes <code>fun a b c => (union_assoc c b a).symm</code>, and <code>op_comm</code> picks up a <code>disjoint_symm</code>. Compiled: right-biased combination is the same structure read the other way round, the two instances are different terms of the same type, and nothing in the definition of <code>PCM</code> prefers either. What cannot be varied is <code>op_assoc</code>: it is the only field with no escape hatch, and an operation that fails it fails to be any kind of monoid.'
    },

    {t:'detail', title:'Why this is a structure and not something Lean finds for you', tag:'aside', open:false,
     blocks:[
       {t:'p', h:'Unit 02 met a mechanism for values Lean supplies without being asked: the instance that makes <code>if x = l</code> legal is found by search, not written by the author. <code>PCM</code> deliberately does not use it. If it did, <code>heapPCM</code> would be found automatically wherever a <code>PCM Heap</code> were wanted, and the notation of Module 3 could be written once and read at any carrier.'},
       {t:'p', h:'That is a real convenience and it costs two things this course cannot afford. It hides which structure is in play, at exactly the point where the argument of Unit 38 is <i>that there is a choice of structure</i> — the same carrier with a different validity relation is a different resource model, and a mechanism whose job is to pick one for you makes that invisible. And it makes every proof depend on a search whose failures are reported in terms of the search rather than of the goal, which for a reader learning Lean is the worst diagnostic in the language. Passing the structure explicitly, as an ordinary argument, costs one binder and keeps both.'}
     ]},

    {t:'note', kind:'key', title:'What the name is for, and when it is spent',
     h:'Nothing in the rest of Module 2 or Module 3 uses <code>PCM</code>. Having just met the word "monoid", do not conclude that the course has turned into abstract algebra. It has not: every unit between here and there works with heaps, concretely, naming <code>Heap.union</code> and <code>Heap.disjoint</code> directly. The structure is built here, for one reason, and then put away. The reason is a claim that cannot be proved yet and can now be stated precisely: the connective at the centre of this logic — the one that says <i>memory splits into a part satisfying this and a part satisfying that</i> — is not a fact about heaps. It is induced by any partial commutative monoid whatever. Unit 38 takes this structure out again and makes that precise: it redefines the connective over an arbitrary <code>PCM</code>, proves two of Module 3\'s laws about it from the eight fields alone, and finds the proofs unchanged from the ones you will have written about heaps. Until then, <code>heapPCM</code> sits in the corpus, checked and cited by nothing.'},

    /* ------------------------------------------------------------ cancellation --- */

    {t:'sec', s:'What heaps have that a monoid need not'},

    {t:'p', h:'Unit 07 made ownership exact: an assertion owns a definite part of a heap. The companion of that idea is the part it does <i>not</i> own, and that phrase names something only if a heap determines its complement — only if, holding <code>h₁</code> and knowing that the whole is <code>h₁</code> combined with something disjoint from it, you have fixed that something rather than narrowed it down. For heaps you have. The property is called <b>cancellativity</b>, and it is a theorem.'},

    {t:'ex',
     id:'x24',
     name:'union_cancel_left',
     hard:true,
     why:'The honest boundary of the generalisation announced above. The eight fields of <code>PCM</code> do not imply this theorem — the counterexample is a few blocks below — so Unit 38, which claims that the central connective of Module 3 is induced by any partial commutative monoid whatever, has to say what it is <i>not</i> claiming, and this is it. Closer to hand: it is what turns "the rest of the heap" into a definite description, and every unit from Module 3 onwards reads it that way.',
     setup:'Three heaps, two disjointness assumptions and an equation between whole heaps; the conclusion is another equation between whole heaps. The equation you are given is about heaps, and everything you can do with it is about addresses, so the first move after fixing an address is to bring the assumption down to that address. Unit 03 gave the tactic-free way of doing that.',
     goal:'theorem union_cancel_left {h₁ h₂ h₃ : Heap}\n    (hd₂ : Heap.disjoint h₁ h₂) (hd₃ : Heap.disjoint h₁ h₃)\n    (he : Heap.union h₁ h₂ = Heap.union h₁ h₃) : h₂ = h₃ := by',
     hints:[
       'At a fixed address <code>l</code> the goal is <code>h₂ l = h₃ l</code> and the assumption <code>he</code> is still an equation between two whole heaps. An equation between functions yields an equation at any point you choose.',
       'Two cases, according to whether <code>h₁</code> is silent at <code>l</code>. If it is, both combinations defer, and the instance of <code>he</code> at <code>l</code> <i>is</i> the goal. If it is not, then both <code>h₂</code> and <code>h₃</code> must be silent there, by the two disjointness assumptions — and then the goal is <code>none = none</code> and <code>he</code> is not needed at all.',
       '<code>funext</code> on the goal, and <code>congrFun</code> — the exact converse of <code>funext</code>, from Unit 03 — on <code>he</code>, with a <code>have</code> to put the result in the context. Then <code>cases h1 : h₁ l with</code>. Of the three lookup lemmas only <code>union_of_none</code> is needed, and it is applied <code>at</code> the hypothesis rather than to the goal. In the branch where <code>h₁</code> speaks, take each disjointness assumption apart with <code>rcases</code>; one of the two disjuncts contradicts the branch hypothesis, and <code>absurd</code> disposes of it.',
       '<code>funext l</code>, then <code>have hl := congrFun he l</code>, which puts <code>hl : h₁.union h₂ l = h₁.union h₃ l</code> in the context. Then <code>cases h1 : h₁ l with</code>; the <code>none</code> branch is <code>rw [union_of_none h₂ h1, union_of_none h₃ h1] at hl</code> followed by <code>exact hl</code>.'
     ],
     sol:'theorem union_cancel_left {h₁ h₂ h₃ : Heap}\n    (hd₂ : Heap.disjoint h₁ h₂) (hd₃ : Heap.disjoint h₁ h₃)\n    (he : Heap.union h₁ h₂ = Heap.union h₁ h₃) : h₂ = h₃ := by\n  funext l\n  have hl := congrFun he l\n  cases h1 : h₁ l with\n  | none => rw [union_of_none h₂ h1, union_of_none h₃ h1] at hl; exact hl\n  | some v =>\n      rcases hd₂ l with e | e\n      · rw [h1] at e; exact absurd e (by simp)\n      · rcases hd₃ l with e\' | e\'\n        · rw [h1] at e\'; exact absurd e\' (by simp)\n        · rw [e, e\']',
     solNote:'The hypothesis <code>he</code> is used in one branch out of two, and <code>hl</code> — the whole content of that hypothesis at this address — is never mentioned in the other. Where <code>h₁</code> speaks, disjointness alone forces the answer, and the equation between the combinations is not needed.',
     expl:'Fix an address. Either <code>h₁</code> is silent there or it is not, and the two cases are settled by completely different assumptions. If it is silent, both combinations defer to their right-hand arguments, so the instance of the given equation at that address says <code>h₂ l = h₃ l</code>, which is the goal — the two rewrites turn it into exactly that. If <code>h₁</code> speaks there, then <code>hd₂</code> says one of <code>h₁ l</code> and <code>h₂ l</code> is <code>none</code>, and the branch hypothesis rules out the first, so <code>h₂ l = none</code>; the same argument on <code>hd₃</code> gives <code>h₃ l = none</code>; and <code>none = none</code>. The theorem is therefore true for a reason that has nothing to do with the equation in half of its cases: what does the work there is that a heap cannot be disjoint from something at an address where both are defined.',
     walk:[
       {tac:'funext l', h:'The conclusion is an equation between heaps, so it becomes an equation at an address. Nothing else in the context changes: <code>he</code> is still about whole heaps.'},
       {tac:'have hl := congrFun he l', h:'The converse move on the <i>hypothesis</i>. <code>congrFun</code> takes an equation between functions and an argument and returns the equation at that argument, so <code>hl : h₁.union h₂ l = h₁.union h₃ l</code>. This is the only line that touches <code>he</code>.'},
       {tac:'cases h1 : h₁ l with', h:'Split on what <code>h₁</code> holds at <code>l</code>, saving the equation as <code>h1</code>. Neither the goal nor <code>hl</code> changes shape — <code>h₁ l</code> occurs in neither, being folded inside the combinations — so all the value is in <code>h1</code>.'},
       {tac:'| none => rw [union_of_none h₂ h1, union_of_none h₃ h1] at hl', h:'Both sides of <code>hl</code> are combinations whose left argument is silent here, so both defer. After the two rewrites <code>hl : h₂ l = h₃ l</code>. The rewrites are aimed <code>at hl</code>, not at the goal, because it is the hypothesis that is in the wrong shape.'},
       {tac:'exact hl', h:'The hypothesis is now the goal.'},
       {tac:'| some v => rcases hd₂ l with e | e', h:'The other branch. Disjointness of <code>h₁</code> and <code>h₂</code> at <code>l</code> is a disjunction; the first disjunct says <code>h₁ l = none</code>, which this branch has just assumed is false.'},
       {tac:'· rw [h1] at e; exact absurd e (by simp)', h:'Killing the impossible disjunct. Rewriting <code>e : h₁ l = none</code> with <code>h1 : h₁ l = some v</code> turns it into <code>e : some v = none</code>, and <code>absurd</code> takes that together with a proof of its negation and produces the goal, whatever the goal is.'},
       {tac:'· rcases hd₃ l with e\' | e\'', h:'The surviving disjunct is <code>e : h₂ l = none</code>. Now run the identical argument on <code>hd₃</code> to get <code>e\' : h₃ l = none</code>.'},
       {tac:'· rw [e, e\']', h:'Both sides of the goal rewritten to <code>none</code>, and <code>rw</code>\'s trailing step closes it. Neither <code>hl</code> nor <code>he</code> appears anywhere in this branch.'}
     ],
     deep:[
       {t:'trace', title:'Bringing a heap equation down to one address',
        start:'h₁ h₂ h₃ : Heap\nhd₂ : h₁.disjoint h₂\nhd₃ : h₁.disjoint h₃\nhe : h₁.union h₂ = h₁.union h₃\nl : Loc\n⊢ h₂ l = h₃ l',
        steps:[
          {tac:'have hl := congrFun he l',
           state:'h₁ h₂ h₃ : Heap\nhd₂ : h₁.disjoint h₂\nhd₃ : h₁.disjoint h₃\nhe : h₁.union h₂ = h₁.union h₃\nl : Loc\nhl : h₁.union h₂ l = h₁.union h₃ l\n⊢ h₂ l = h₃ l',
           h:'<code>funext</code> and <code>congrFun</code> are converses, and this proof uses both — one on the goal, one on the hypothesis, in the same direction. Everything from here on is about the single address <code>l</code>.'},
          {tac:'| none => rw [union_of_none h₂ h1, union_of_none h₃ h1] at hl',
           state:'case none\nh₁ h₂ h₃ : Heap\nhd₂ : h₁.disjoint h₂\nhd₃ : h₁.disjoint h₃\nhe : h₁.union h₂ = h₁.union h₃\nl : Loc\nhl : h₂ l = h₃ l\nh1 : h₁ l = none\n⊢ h₂ l = h₃ l',
           h:'The hypothesis has become the goal, letter for letter. That is the whole of the branch where <code>h₁</code> is silent, and it is where the equation is actually spent.'}
        ],
        done:'exact hl'},
       {t:'detail', title:'The dead branch in full', tag:'aside', open:false,
        blocks:[
          {t:'p', h:'Nine lines of context and a goal that is never looked at. The point of the branch is the last line of the context.'},
          {t:'state', cap:'After <code>rcases hd₂ l with e | e</code> and <code>rw [h1] at e</code>, in the first disjunct.',
           src:'case some.inl\nh₁ h₂ h₃ : Heap\nhd₂ : h₁.disjoint h₂\nhd₃ : h₁.disjoint h₃\nhe : h₁.union h₂ = h₁.union h₃\nl : Loc\nhl : h₁.union h₂ l = h₁.union h₃ l\nv : Val\nh1 : h₁ l = some v\ne : some v = none\n⊢ h₂ l = h₃ l'},
          {t:'p', h:'<code>e</code> is now an impossibility, so the goal is irrelevant and <code>absurd e (by simp)</code> produces it. The surviving disjunct carries <code>e : h₂ l = none</code>, and after the same treatment of <code>hd₃</code> the context has <code>e</code> and <code>e\'</code> saying that both complements are silent here.'}
        ]},
       {t:'h4', s:'Why both disjointness assumptions are there'},
       {t:'p', h:'Both disjointness assumptions are needed and neither is decoration. Drop either one and the theorem is false, and one address is enough to see it:'},
       {t:'code', tag:'illustration', cap:'Three one-cell heaps at address 0. The two combinations are equal because the left-biased operation discards whatever the right-hand argument says at an address the left one already claims — and the two right-hand arguments are different heaps.',
        src:'example :\n    Heap.union (Heap.singleton 0 4) (Heap.singleton 0 7)\n      = Heap.union (Heap.singleton 0 4) (Heap.singleton 0 9) := by\n  funext l\n  by_cases hl : l = 0\n  · subst hl\n    rw [union_of_some (Heap.singleton 0 7) (singleton_same 0 4),\n        union_of_some (Heap.singleton 0 9) (singleton_same 0 4)]\n  · rw [union_of_none (Heap.singleton 0 7) (singleton_other 0 l 4 hl),\n        union_of_none (Heap.singleton 0 9) (singleton_other 0 l 4 hl),\n        singleton_other 0 l 7 hl, singleton_other 0 l 9 hl]\n\nexample : Heap.singleton 0 7 ≠ Heap.singleton 0 9 := by\n  intro h\n  have h0 := congrFun h 0\n  rw [singleton_same, singleton_same] at h0\n  exact absurd h0 (by simp)'}
     ],
     pitfall:'Rewriting the branch hypothesis into <code>hl</code> directly. <code>rw [h1] at hl</code> looks right — <code>h1</code> says what <code>h₁ l</code> is, and <code>hl</code> is about combinations involving <code>h₁</code> — but <code>h₁ l</code> does not <i>occur</i> in <code>hl</code>: it is inside <code>Heap.union</code>, which is a folded name. Lean reports <code>Did not find an occurrence of the pattern h₁ l in the target expression h₁.union h₂ l = h₁.union h₃ l</code>. This is Unit 09\'s parked-<code>match</code> lesson arriving in a hypothesis instead of a goal, and the repair is the same: the lookup lemmas, not the definition.',
     variants:'Drop <code>hd₂</code> or <code>hd₃</code> and the theorem is false, witnessed by the two compiled examples above with <code>h₁ = Heap.singleton 0 4</code>. Cancel on the right instead — <code>Heap.union h₂ h₁ = Heap.union h₃ h₁</code> with the disjointness assumptions turned round — and the statement is still true and needs no new proof: <code>rw [union_comm hd₂, union_comm hd₃] at he</code> converts it into this one. Weaken the conclusion to "<code>h₂</code> and <code>h₃</code> agree wherever <code>h₁</code> is silent" — <code>(l : Loc) (h1 : h₁ l = none) : h₂ l = h₃ l</code> — and both disjointness assumptions become unnecessary. That version is the <code>none</code> branch of this proof standing alone: <code>congrFun</code>, the two rewrites, <code>exact hl</code>. Compiled. It is a fair description of what the equation alone gives you, and the two disjointness assumptions buy exactly the other branch.'
    },

    {t:'p', h:'Cancellativity is a theorem about heaps and it is <i>not</i> a consequence of the eight fields. Nothing in the definition of a partial commutative monoid rules out a structure in which two different elements can be combined with the same thing to the same effect. Here is one, and it is not a curiosity: it is the operation of this unit at a single address, with one line changed.'},

    {t:'code', tag:'illustration', cap:'The carrier is one cell — <code>Option Val</code> — and the operation is the same left-biased choice <code>Heap.union</code> makes. The only difference from heaps is the third line: two cells holding the <i>same</i> value are declared valid.',
     src:'def agreePCM : PCM (Option Val) where\n  op         := fun a b => match a with | some v => some v | none => b\n  unit       := none\n  valid      := fun a b => a = none ∨ b = none ∨ a = b\n  op_comm    := by\n    intro a b h\n    rcases h with h | h | h\n    · subst h; cases b <;> rfl\n    · subst h; cases a <;> rfl\n    · subst h; cases a <;> rfl\n  op_assoc   := by intro a b c; cases a <;> rfl\n  unit_left  := fun _ => rfl\n  valid_unit := fun _ => Or.inl rfl\n  valid_comm := by\n    intro a b h\n    rcases h with h | h | h\n    · exact Or.inr (Or.inl h)\n    · exact Or.inl h\n    · exact Or.inr (Or.inr h.symm)'},

    {t:'p', h:'Every field is filled, so this is a partial commutative monoid by the same definition <code>heapPCM</code> satisfies. And cancellation fails in it, at the smallest possible size: combining <code>some 3</code> with itself and combining <code>some 3</code> with the unit give the same answer, both pairs are valid, and the two right-hand arguments are different.'},

    {t:'code', tag:'illustration', cap:'Two validity facts, one equation and one disequality — cancellativity refuted in four lines.',
     src:'example : agreePCM.valid (some 3) (some 3) := Or.inr (Or.inr rfl)\n\nexample : agreePCM.valid (some 3) agreePCM.unit := Or.inr (Or.inl rfl)\n\nexample : agreePCM.op (some 3) (some 3) = agreePCM.op (some 3) agreePCM.unit := rfl\n\nexample : (some 3 : Option Val) ≠ agreePCM.unit := by simp [agreePCM]'},

    {t:'p', h:'What that structure models is a resource two parties may hold at once provided they agree about it — read-only sharing, as against the exclusive ownership heaps encode. The two differ in one field, and the field they differ in is <code>valid</code>. That is the concrete meaning of the remark in the anatomy above: the same carrier and the same operation with a wider validity relation is a different resource model, and this is a pair of models that differ in exactly that way. It is also the reason Unit 38 must state its claim carefully: what generalises is the connective at the centre of Module 3, together with its laws, and what does not generalise is the theorem you have just proved.'},

    /* ---------------------------------------------------------------- closing --- */

    {t:'dod', h:'You can prove <code>union_assoc</code> with no hypothesis, and say why an operation that prefers its left argument is associative on the nose. You can produce two heaps whose combination depends on the order they are written in, and say which hypothesis excludes them and where in the proof it is spent. You can prove <code>union_comm</code>, <code>disjoint_union_left</code> and <code>disjoint_union_right</code>, and you obtained the last of those by conjugating rather than by proving it again. You can use <code>refine</code> to write down the shape of an answer and leave the parts you have not worked out as goals, and you can read <code>case refine_1</code>. You can say what a monoid is, what makes one commutative, and what the word <i>partial</i> adds; you can check <code>(Heap, union, empty, disjoint)</code> against that definition field by field; and you have written the structure in Lean and instantiated it, so <code>heapPCM : PCM Heap</code> is a term. You can prove that a heap determines its complement, and exhibit a partial commutative monoid in which that is false.'},

    {t:'p', h:'You have an algebra of resources. What you do not have is a single fact about the relation that says <i>this heap splits into these two</i> — and its associativity is none of the laws above. It is the first statement whose proof has to manufacture hypotheses nobody handed you.'}

  ]
});
