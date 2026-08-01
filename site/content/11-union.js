registerChapter({
  id: 'union',
  num: '09',
  phase: 'Phase 1 · The resource algebra',
  title: 'Union, and why it must be total',
  blurb: 'Combining two heaps: the operation the mathematics calls partial, written as a total function because a total type theory leaves no usable alternative — and the three lookup lemmas that make it possible to reason about.',

  /* One forward reference, made by name in x21's `why`: the sentence says
     outright that Unit 10 is where the theorem lives and what it needs
     `union_eq_none` for. ERRATA §10's legitimate kind. */
  ledgerForward: ['disjoint_union_left'],

  orient: {
    youWill: [
      'Read <code>Heap.union</code> line by line and say what it answers at an address where <i>both</i> heaps are defined.',
      'Say why an operation whose <i>type</i> demands a disjointness proof makes every later rewrite fail, and see the failure.',
      'Diagnose a goal that has stopped on an unreduced <code>match</code>, and say exactly what a <code>match</code> is waiting for.',
      'Manufacture the thing it is waiting for, either from a hypothesis or with <code>cases hl : h l with</code>, and say why <code>by_cases</code> is the wrong instrument here.',
      'Prove <code>union_of_none</code>, <code>union_of_some</code> and <code>union_eq_none</code>, and reason about unions from then on without ever naming the definition again.',
      'Say why <code>Heap.union Heap.empty h = h</code> is settled by reduction alone and its mirror image is not.'
    ],
    needs: [
      'Unit 08: <code>Heap.disjoint</code>, and the <code>unionOf</code> exhibit — a union carrying its own disjointness proof, whose associativity could not be written down.',
      'Unit 05: <code>Heap.empty</code> is <code>fun _ =&gt; none</code>. Unit 03: <code>funext</code>, and that reduction goes under a binder. Unit 02: <code>cases hl : e with</code>, the saved-equation form, and that a variable in the position being cased on is what blocks reduction.',
      'Unit 01: implicit binders <code>{x : T}</code> and what makes an argument inferable; <code>constructor</code> on an <code>↔</code>. Unit 00: <code>intro</code> with a <code>⟨…⟩</code> pattern.'
    ],
    payoff: 'Every heap equation in the rest of the course is proved by looking up one address in a union, and <code>union_of_none</code> and <code>union_of_some</code> are how that is done — they are cited by name in Units 10, 14, 24, 25 and 30. The unit laws are what let Unit 11 split any heap trivially, and four of Unit 15\'s assertion laws come down to one of them. Unit 10 takes the operation you build here and asks whether it deserves a name.'
  },

  blocks: [

    /* ------------------------------------------------------------- the thread --- */

    {t:'p', h:'The operation that combines two heaps is already on the page. It had to be, because <code>Heap.splits</code> mentions it, and <code>Heap.union</code> arrived with it — text, and not one fact about it. That is not an oversight. The definition as written resists being used: unfold it inside a goal and the goal gets longer without getting closer. Fixing that is most of this unit, and the fix is three small theorems after which the definition is never named again.'},

    {t:'p', h:'There is also a question the definition begs. A mathematician defines the union of two heaps only when they are disjoint — a partial operation, undefined on overlapping arguments. <code>Heap.union</code> takes any two heaps whatever and returns a heap. So it has an answer for arguments that overlap, and that answer is a decision somebody made.'},

    /* --------------------------------------------------------------- the text --- */

    {t:'sec', s:'What the definition says'},

    {t:'anat', tag:'verified',
     src:'def Heap.union (h₁ h₂ : Heap) : Heap :=\n  fun l =>\n    match h₁ l with\n    | some v => some v\n    | none   => h₂ l',
     parts:[
       {m:'(h₁ h₂ : Heap) : Heap', h:'Two heaps in, one heap out. No proof is demanded, nothing is returned wrapped in an <code>Option</code>, and there is no pair of arguments for which this fails to produce an answer. Whatever else is true of the operation, it is a function on all of <code>Heap × Heap</code>.'},
       {m:'fun l =>', h:'The result is a heap and a heap is a function of an address, so the body is a lambda. Everything below this line is the answer at one address, and every proof about <code>Heap.union</code> starts by fixing that address — with <code>funext</code> if the goal is an equation between heaps, or because the goal already mentions one.'},
       {m:'match h₁ l with', h:'The scrutinee: the expression whose shape decides which branch is taken. It is a lookup in the <b>left</b> heap. That single choice is the whole asymmetry of the operation, and it is the reason the two unit laws below have proofs of different lengths.'},
       {m:'| some v => some v', h:'Where the left heap answers, its answer is the answer, and <code>h₂</code> is not consulted at all. What is <i>not</i> said matters as much: nothing requires <code>h₂ l</code> to be <code>none</code> here. The operation is defined on overlapping arguments and this branch is where it decides what to do about them.'},
       {m:'| none   => h₂ l', h:'Where the left heap is silent, defer to the right one, whatever it says — including <code>none</code>, in which case the combination is undefined there too. So the domain of the combination is the union of the two domains, which is the one property the name promises.'}
     ]},

    {t:'p', h:'Left-biased is what that shape is called. At an address where the two heaps disagree you can watch it decide.'},

    {t:'code', tag:'illustration', cap:'Two one-cell heaps that both claim address 4, combined in each order. Both lines are closed by <code>rfl</code>: the addresses are numerals, so the lookups reduce, so the <code>match</code> computes.',
     src:'example : Heap.union (Heap.singleton 4 3) (Heap.singleton 4 7) 4 = some 3 := rfl\n\nexample : Heap.union (Heap.singleton 4 7) (Heap.singleton 4 3) 4 = some 7 := rfl'},

    {t:'p', h:'Swapping the arguments changes the answer. Whether that is a defect depends on what you intend the operation to be used for, and the intention is fixed by the previous unit: combination is only ever applied to heaps already known to be disjoint, and on disjoint arguments the two branches can never disagree, because at most one of them is defined. Left-biasing is a decision about arguments the course promises never to hand it: a convenience with a discipline attached.'},

    /* ---------------------------------------------------------------- totality --- */

    {t:'sec', s:'Why the operation is total'},

    {t:'cmp',
     left: {t:'What the mathematics says',
            h:'The combination of <code>h₁</code> and <code>h₂</code> exists exactly when the two are disjoint. On overlapping arguments the expression denotes nothing, and a sentence containing it is not false but meaningless. Disjointness lives in the <i>well-formedness</i> of the expression, so it never has to be written down as a hypothesis.'},
     right:{t:'What a total type theory offers',
            h:'A function must return something for every argument. The two ways to encode partiality are to widen the result — <code>Heap → Heap → Option Heap</code>, so every use unwraps — or to narrow the input, by demanding a disjointness proof as a third argument. The previous unit showed the second one cannot state its own associativity. The first is worse: the operation and every lemma about it acquire an <code>Option</code> the mathematics does not have.'}},

    {t:'p', h:'The second option fails in a way the previous unit did not show, and the failure is not about associativity specifically. Suppose you have the proof-carrying <code>unionOf</code> from the previous unit and an ordinary equation between heaps, and you want to rewrite with it inside a combination.'},

    {t:'code', tag:'sketch', cap:'A rewrite under an operation whose type mentions its arguments.',
     src:'def unionOf (h₁ h₂ : Heap) (_ : Heap.disjoint h₁ h₂) : Heap :=\n  Heap.union h₁ h₂\n\nexample (h₁ h₂ k : Heap) (d : Heap.disjoint h₁ h₂) (he : h₁ = k) :\n    unionOf h₁ h₂ d = Heap.union k h₂ := by\n  rw [he]'},

    {t:'state', cap:'The line-and-column prefix is dropped here and throughout this page. So is everything Lean prints after this message: an <code>Explanation:</code> paragraph about how a motive is built in general, a <code>Possible solutions:</code> line, and the goal, unchanged.',
     src:'error: Tactic `rewrite` failed: motive is not type correct:\n  fun _a => unionOf _a h₂ d = k.union h₂\nError: Application type mismatch: The argument\n  d\nhas type\n  h₁.disjoint h₂\nbut is expected to have type\n  _a.disjoint h₂\nin the application\n  unionOf _a h₂ d'},

    {t:'p', h:'The proof <code>d</code> is inside the term, and its <i>type</i> names <code>h₁</code>. Replacing <code>h₁</code> by <code>k</code> therefore invalidates <code>d</code>, so the intermediate function <code>rw</code> builds does not typecheck and the rewrite is refused. This is not a corner case. It is every rewrite: any equation you want to use inside a combination has to be accompanied by a proof that the disjointness proof survives it, and that accompanying step is itself a rewrite with the same problem. The same statement with the plain <code>Heap.union</code> in it — <code>Heap.union h₁ h₂ = Heap.union k h₂</code> from <code>he : h₁ = k</code> — is closed by <code>rw [he]</code> and nothing else.'},

    {t:'note', kind:'key', title:'The register shift',
     h:'On paper you write "the two heaps are disjoint, so define their union", and disjointness is discharged by the act of writing the symbol. Lean will not let you. <code>Heap.union</code> has to be defined on every pair, or the disjointness proof becomes part of the term and no later rewrite can get past it. So the operation is total, it is left-biased where the two arguments disagree, and disjointness travels separately — as an ordinary hypothesis, supplied at each point of use. That is why a lemma that genuinely needs the two heaps not to overlap carries an explicit <code>hd : Heap.disjoint h₁ h₂</code> that on paper would be invisible, and why it falls to the caller to produce one. It also makes the requirement visible, so you can ask of any theorem whether it has one: not a single one of the six on <i>this</i> page does, because none of them needs it, and adding a hypothesis a proof does not use is a claim about the theorem that is not true.'},

    /* ------------------------------------------------------- the parked match --- */

    {t:'sec', s:'A definition that does nothing'},

    {t:'p', h:'Now the other problem. Take the simplest imaginable fact about the operation — at an address where the left heap is undefined, the combination answers whatever the right heap answers — and try to prove it the way every heap lookup has been proved so far, by putting the definition in a <code>simp</code> bracket.'},

    {t:'code', tag:'sketch', cap:'The move that settled every lookup law in Unit 05.',
     src:'example {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  simp [Heap.union]'},

    {t:'state', cap:'Not "no progress" — progress, and then a wall.',
     src:'error: unsolved goals\nh₁ h₂ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (match h₁ l with\n    | some v => some v\n    | none => h₂ l) =\n    h₂ l'},

    {t:'p', h:'The definition <i>was</i> unfolded — the <code>match</code> is now printed in the goal, which it was not before — and then everything stopped. <code>simp only [Heap.union]</code>, <code>rw [Heap.union]</code> and <code>unfold Heap.union</code> all leave that same goal. The reason is Unit 02\'s rule about blocked reduction, in the setting where it does the most damage. A <code>match</code> chooses a branch by looking at which constructor its scrutinee is. Here the scrutinee is <code>h₁ l</code>: an application of a variable to a variable. It is not <code>some</code> of anything and it is not <code>none</code>; it is not a constructor application at all, and until it becomes one the <code>match</code> has no branch to take and stands in the goal as a term.'},

    {t:'p', h:'The hypothesis <code>hl : h₁ l = none</code> says exactly what the <code>match</code> is waiting to hear. Aimed at the goal as it stands, it does nothing.'},

    {t:'code', tag:'sketch', cap:'The hypothesis aimed at the folded goal.',
     src:'example {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  rw [hl]'},

    {t:'state', cap:'<code>h₁ l</code> is in the goal, but only after <code>Heap.union</code> has been opened. Before that it is hidden inside the name.',
     src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  h₁ l\nin the target expression\n  h₁.union h₂ l = h₂ l'},

    {t:'p', h:'So the recipe has two moves and their order is forced: expose the <code>match</code>, then put its scrutinee in constructor form. Both moves fit in one <code>simp</code> call, because a <code>simp</code> bracket may hold a definition and a hypothesis together and <code>simp</code> keeps rewriting until nothing changes. That is the first exercise, and after it no proof in this course opens <code>Heap.union</code> again.'},

    {t:'ex',
     id:'x20',
     name:'union_of_none / union_of_some',
     hard:false,
     why:'These two are the most-cited lemmas in the second half of this course. Unit 10 proves associativity, commutativity and cancellation of the operation with them, Unit 14 uses them on one-cell heaps, and the locality proofs of Unit 25 and the capstone of Unit 30 do little else: look this address up in a combination, then look it up in the frame. Proving them is also the last time you will write <code>Heap.union</code> inside a <code>simp</code> bracket.',
     setup:'Two theorems, one per branch of the <code>match</code>: in the first the left heap is silent and the combination defers to the right one, in the second the left heap answers and the combination repeats that answer. The two proofs are the same text. Both heaps appear in each statement but only <code>h₂</code> is written explicitly — the <i>Why it works</i> panel says why, and the answer decides the shape of every later citation.',
     goal:'theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  sorry\n\ntheorem union_of_some {h₁ : Heap} (h₂ : Heap) {l : Loc} {v : Val} (hl : h₁ l = some v) :\n    Heap.union h₁ h₂ l = some v := by',
     hints:[
       'Written out, the first goal is the one printed in <i>A definition that does nothing</i> above: a <code>match</code> that looks at <code>h₁ l</code>, answers with that value where there is one and with <code>h₂ l</code> where there is not, and has to be shown equal to <code>h₂ l</code>. The hypothesis <code>hl</code> is a statement about that scrutinee. The second goal is the same term against <code>some v</code>, with <code>hl</code> naming the other constructor.',
       'Two things have to happen and the order matters: the <code>match</code> has to be visible in the goal, and its scrutinee has to be a constructor. The hypothesis supplies the second. Nothing supplies the first except naming the definition.',
       'The tactic is <code>simp</code>, and its bracket is a list, not a single slot. Both facts you need can go in the same one, and <code>simp</code> keeps applying them, reducing what it can between applications, until nothing changes.',
       'Do the two moves separately first and you have a proof either way. <code>simp only [Heap.union]</code> leaves exactly the goal printed in <i>A definition that does nothing</i>: the definition is open, and the scrutinee <code>h₁ l</code> is now a subterm you can aim a rewrite at. <code>rw [hl]</code> then puts <code>none</code> in the scrutinee position, the <code>match</code> takes its second branch, and <code>rw</code>\'s trailing <code>rfl</code> closes <code>h₂ l = h₂ l</code> without being asked. The corpus proof is those two rules handed to one <code>simp</code> in a single bracket.'
     ],
     sol:'theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  simp [Heap.union, hl]\n\ntheorem union_of_some {h₁ : Heap} (h₂ : Heap) {l : Loc} {v : Val} (hl : h₁ l = some v) :\n    Heap.union h₁ h₂ l = some v := by\n  simp [Heap.union, hl]',
     solNote:'One tactic call, character for character the same, proves both. What differs is only which constructor the hypothesis names, and therefore which branch of the <code>match</code> survives.',
     expl:'A <code>match</code> is a term that is waiting to be told which of its branches applies. It is told by its scrutinee becoming a constructor application. Here the scrutinee is <code>h₁ l</code>, which is opaque, and the hypothesis is precisely the statement that it is a constructor application after all. So the proof is: open the definition so the scrutinee is visible, rewrite it into constructor form, and let reduction finish. That is one <code>simp</code> call because <code>simp</code> applies its rules repeatedly and reduces what it can between applications.',
     walk:[
       {tac:'simp [Heap.union, hl]  (union_of_none)', h:'Three effects in one call. <code>Heap.union</code> in the bracket replaced the folded name by its body, so the goal became the <code>match</code> displayed in the section above. <code>hl</code> in the bracket rewrote the scrutinee <code>h₁ l</code> to <code>none</code>. With a constructor in the scrutinee position the <code>match</code> reduced to its second branch, <code>h₂ l</code>, and the goal became <code>h₂ l = h₂ l</code>, which <code>simp</code> closes.'},
       {tac:'simp [Heap.union, hl]  (union_of_some)', h:'Identical, one branch over. <code>hl</code> now rewrites the scrutinee to <code>some v</code>, the <code>match</code> reduces to its <i>first</i> branch, <code>some v</code>, and the goal is <code>some v = some v</code>. The value <code>v</code> is implicit in the statement because the hypothesis determines it.'}
     ],
     deep:[
       {t:'p', h:'Splitting the single call into its two halves shows where the wall is and where it is not.'},
       {t:'trace', title:'The same proof, one rule at a time',
        start:'h₁ h₂ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ h₁.union h₂ l = h₂ l',
        steps:[
          {tac:'simp only [Heap.union]',
           state:'h₁ h₂ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (match h₁ l with\n    | some v => some v\n    | none => h₂ l) =\n    h₂ l',
           h:'The name is gone and the <code>match</code> is in the open. This goal is strictly worse than the one before it: it is longer, and nothing in it is a heap operation any lemma knows about. A proof that stops here has not gone wrong, it has gone half way.'},
          {tac:'rw [hl]',
           state:'',
           h:'The scrutinee becomes <code>none</code>, the <code>match</code> takes its second branch, and the goal is <code>h₂ l = h₂ l</code> — which <code>rw</code>\'s own trailing <code>rfl</code> closes without being asked. One rewrite turned an inert term into a computation.'}
        ],
        done:'No goals.'},
       {t:'h4', s:'Why h₂ is explicit and h₁ is not'},
       {t:'p', h:'The binders are not decoration; they decide what every citation of these lemmas looks like, and there are forty-two of those ahead. Lean fills an implicit argument by matching the arguments you <i>do</i> supply against the expected type. <code>h₁</code> and <code>l</code> both occur in the type of <code>hl</code>, so supplying <code>hl</code> determines them. <code>h₂</code> occurs only in the conclusion, so nothing you pass determines it.'},
       {t:'code', tag:'sketch', cap:'The same theorem with every heap implicit, cited where the conclusion is not yet known.',
        src:'theorem union_of_none_i {h₁ h₂ : Heap} {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  simp [Heap.union, hl]\n\nexample (h₁ h₂ : Heap) (l : Loc) (hl : h₁ l = none) : h₁ l = none := by\n  have hu := union_of_none_i hl\n  exact hl'},
       {t:'state', cap:'Two further errors follow from this one and are not quoted.',
        src:'error: don\'t know how to synthesize implicit argument `h₂`\n  @union_of_none_i h₁ ?m.8 l hl\ncontext:\nh₁ h₂ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ Heap'},
       {t:'p', h:'Hence <code>union_of_none h₂ hl</code>: the right-hand heap first, because it has to be said, then the hypothesis, which says everything else. The rule generalises — make a binder implicit when some <i>other</i> argument\'s type pins it down, explicit when only the conclusion mentions it.'}
     ],
     pitfall:'Reaching for the hypothesis first. <code>rw [hl]</code> on the untouched goal reports <code>Did not find an occurrence of the pattern h₁ l</code>, because <code>h₁ l</code> is inside <code>Heap.union</code> and the name has not been opened. The mirror mistake is <code>simp only [hl]</code>, which reports <code>`simp` made no progress</code> for the same reason. Both are fixed by putting <code>Heap.union</code> in the bracket, and the bracket is order-insensitive — <code>simp [hl, Heap.union]</code> works too.',
     variants:'Drop <code>hl</code> from the bracket and the proof fails with <code>unsolved goals</code> and the parked <code>match</code> in front of you, which is the diagnosis this whole section is about. Drop <code>Heap.union</code> instead and <code>simp</code> reports no progress. State <code>union_of_some</code> with <code>h₂ l</code> on the right instead of <code>some v</code> and the statement becomes false, at exactly the address where the two heaps disagree. The witness is the pair already on this page: <code>h₁ = Heap.singleton 4 3</code>, <code>h₂ = Heap.singleton 4 7</code>, <code>l = 4</code>. The hypothesis holds with <code>v = 3</code>, the true conclusion gives <code>some 3</code>, and the altered one would demand <code>some 7</code>. That is left-biasing, and it is why the <code>some</code> case cannot be stated symmetrically with the <code>none</code> case — where both heaps are silent there is nothing to disagree about.'
    },

    /* -------------------------------------------------------- splitting a value --- */

    {t:'sec', s:'When nobody gives you the hypothesis'},

    {t:'p', h:'<code>union_of_none</code> and <code>union_of_some</code> both need to be told which case they are in. Most goals do not come with that. In <code>Heap.union h Heap.empty = h</code> there is no hypothesis about <code>h</code> at all, and there cannot be: the theorem is about every heap. When you do not have the fact, you make it, by splitting on the value the <code>match</code> is waiting for.'},

    {t:'p', h:'That is <code>cases hl : h l with</code>, Unit 02\'s saved-equation form. Its job here is not to case on a proposition; it is to replace the opaque term <code>h l</code> by each of the two constructor shapes it could have, and — this is the part that matters — to record in a named hypothesis which shape this branch assumed. That hypothesis is what <code>union_of_none</code> and <code>union_of_some</code> take as their argument.'},

    {t:'cmp',
     left: {t:'cases hl : h l with', kind:'good',
            h:'Splits on the <i>value</i> <code>h l</code>. Two branches, <code>case none</code> and <code>case some</code>; the second binds a name <code>v</code> for the stored value; and both leave <code>hl</code> in the context, saying <code>h l = none</code> or <code>h l = some v</code>. Every occurrence of <code>h l</code> that Lean can see is replaced accordingly — after <code>funext l</code> on <code>Heap.union h Heap.empty = h</code>, the <code>none</code> branch reads <code>⊢ h.union Heap.empty l = none</code>, the right-hand side already rewritten.'},
     right:{t:'by_cases hl : h l = none',
            h:'Splits on the <i>proposition</i>. Two branches, <code>case pos</code> with <code>hl : h l = none</code> and <code>case neg</code> with <code>hl : ¬h l = none</code>; the goal is untouched in both. The positive branch is fine. The negative one gives you a negation, and no lookup lemma takes a negation: to reach <code>union_of_some</code> you must first turn <code>¬h l = none</code> into a value, with Unit 02\'s <code>defined_of_ne_none</code> and an <code>obtain</code>. That is one extra line in every such proof, on top of the goal-rewriting the other split does for free, for a case analysis that had the value in its hand a moment earlier.'}},

    {t:'code', tag:'illustration', cap:'The same theorem by the second route. It compiles; the <code>obtain</code> line and the two trailing rewrite entries — <code>, hl</code> and <code>, hv</code> — are all spent recovering what the other split never lost.',
     src:'example (h : Heap) : Heap.union h Heap.empty = h := by\n  funext l\n  by_cases hl : h l = none\n  · rw [union_of_none Heap.empty hl, hl]\n    rfl\n  · obtain ⟨v, hv⟩ := defined_of_ne_none h l hl\n    rw [union_of_some Heap.empty hv, hv]'},

    {t:'p', h:'So: <code>by_cases</code> when what you are unsure of is a proposition, <code>cases hl : e with</code> when what you are unsure of is a value and you will need to know which one. Every remaining proof in this unit uses the second.'},

    {t:'p', h:'One more piece of syntax before the next exercise, and it saves one line rather than teaching anything. <code>rw [e] at h</code> followed immediately by <code>exact h</code> is common enough to have a contraction: <code>rwa [e] at h</code> rewrites in the hypothesis and then tries to close the goal with it. The <code>a</code> is for <i>assumption</i>.'},

    {t:'code', tag:'illustration', cap:'The same proof twice. <code>rwa</code> occurs exactly once in the whole verified corpus of this course, and it is in the next exercise.',
     src:'example {h₁ h₂ : Heap} {l : Loc} (hl : h₁ l = none) (h : Heap.union h₁ h₂ l = none) :\n    h₂ l = none := by\n  rw [union_of_none h₂ hl] at h\n  exact h\n\nexample {h₁ h₂ : Heap} {l : Loc} (hl : h₁ l = none) (h : Heap.union h₁ h₂ l = none) :\n    h₂ l = none := by\n  rwa [union_of_none h₂ hl] at h'},

    {t:'ex',
     id:'x21',
     name:'union_eq_none',
     hard:false,
     why:'The third lookup lemma, and the only one of the three with content: it says the combination is undefined at an address exactly when <i>both</i> parts are. That is the only way to reason about a union being undefined somewhere, and Unit 10 needs it in two theorems: in the branch of associativity where both left-hand heaps are silent, and three times over in <code>disjoint_union_left</code>, where disjointness against a combination has to be taken apart into disjointness against each piece and put back together again. The forward direction is also where the <code>match</code> analysis of this unit gets its hardest workout.',
     setup:'An <code>↔</code>, so <code>constructor</code> splits it into <code>case mp</code> and <code>case mpr</code>. The two directions are not mirror images: one has to discover which case it is in, the other is told. All three binders are implicit. Unlike the lookup lemmas, this one has no hypothesis to read them off — but every one of them appears in the statement itself, so whatever goal or hypothesis you cite it at determines all three.',
     goal:'theorem union_eq_none {h₁ h₂ : Heap} {l : Loc} :\n    Heap.union h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by',
     hints:[
       'Forwards: from <code>Heap.union h₁ h₂ l = none</code> produce both <code>h₁ l = none</code> and <code>h₂ l = none</code>. Backwards: from those two produce the first. Nothing about disjointness is involved and no hypothesis relates the two heaps.',
       'Backwards is direct — the left heap is silent, so the combination defers, and what it defers to is the second assumption. Forwards you are not told which branch the <code>match</code> took, so find out: if the left heap held a value at <code>l</code>, the combination would hold that value there, and it does not.',
       'Everything you need is named. <code>constructor</code> splits the <code>↔</code>. <code>cases hl : e with</code> splits on <code>h₁ l</code> and keeps the equation. <code>union_of_none</code> and <code>union_of_some</code> from the previous exercise are the two branch lemmas, and <code>rw … at h</code> is how you push one of them through an assumption rather than through a goal. <code>absurd</code> closes a branch in which two distinct constructors have been equated. Backwards needs none of the case analysis: one rewrite, and <code>intro</code> accepts a pattern in place of a name.',
       '<code>constructor</code>, then <code>· intro h</code> and <code>cases hl : h₁ l with</code>. In the <code>none</code> branch the goal has already become <code>⊢ none = none ∧ h₂ l = none</code>, so its first component is <code>rfl</code> and only the second needs work.'
     ],
     sol:'theorem union_eq_none {h₁ h₂ : Heap} {l : Loc} :\n    Heap.union h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by\n  constructor\n  · intro h\n    cases hl : h₁ l with\n    | none   => exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩\n    | some v => rw [union_of_some h₂ hl] at h; exact absurd h (by simp)\n  · intro ⟨ha, hb⟩\n    rw [union_of_none h₂ ha]; exact hb',
     solNote:'Two tactic blocks stand where terms are expected: <code>by rwa […] at h</code> inside the anonymous constructor, and <code>by simp</code> as the second argument of <code>absurd</code>. Both are the same construct — <code>by</code> opens a tactic proof anywhere a proof is wanted, and it earns its place when the proof is one tactic and giving it a name would cost a line.',
     expl:'The backward direction is the operation\'s definition read out loud: the left heap is silent, so the answer is the right heap\'s, which is <code>none</code> by assumption. The forward direction has to discover which branch was taken, and the discovery is by elimination. If the left heap held a value at <code>l</code>, then by <code>union_of_some</code> the combination would hold that same value there — but the assumption says the combination is <code>none</code>, and <code>some v = none</code> is impossible. So the left heap is silent, and then <code>union_of_none</code> transfers the assumption to the right heap.',
     walk:[
       {tac:'constructor', h:'Split the <code>↔</code> into its two implications, <code>case mp</code> and <code>case mpr</code>. They are the two fields of <code>Iff</code>, which is why those are the names.'},
       {tac:'intro h', h:'Named the assumption <code>h : h₁.union h₂ l = none</code> in the forward direction. The goal is the conjunction, and neither conjunct can be proved yet, because nothing has been decided about <code>h₁ l</code>.'},
       {tac:'cases hl : h₁ l with', h:'Manufactured the decision. Two branches; in each, <code>hl</code> records the assumption and every visible occurrence of <code>h₁ l</code> is replaced. The first conjunct of the goal was <code>h₁ l = none</code>, so it becomes <code>none = none</code> in one branch and <code>some v = none</code> in the other — the goal itself now says which branch is the impossible one.'},
       {tac:'| none   => exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩', h:'The whole branch as one term. <code>rfl</code> proves <code>none = none</code>. The second slot needs <code>h₂ l = none</code>: <code>union_of_none h₂ hl</code> rewrites <code>h</code> from a statement about the combination into a statement about <code>h₂</code>, and <code>rwa</code>\'s trailing assumption step hands it over.'},
       {tac:'| some v => rw [union_of_some h₂ hl] at h', h:'This is where the branch is killed. Rewriting <code>h</code> with <code>union_of_some</code> turns <code>h₁.union h₂ l = none</code> into <code>some v = none</code>. The goal is untouched and irrelevant now.'},
       {tac:'exact absurd h (by simp)', h:'<code>absurd</code> takes a proof of <code>P</code> and a proof of <code>¬P</code> and produces anything, which is what a dead branch needs. <code>P</code> here is <code>some v = none</code>, and <code>by simp</code> proves its negation from constructor distinctness.'},
       {tac:'intro ⟨ha, hb⟩', h:'The backward direction, with the conjunction taken apart in the <code>intro</code> rather than after it. <code>ha : h₁ l = none</code>, <code>hb : h₂ l = none</code>.'},
       {tac:'rw [union_of_none h₂ ha]; exact hb', h:'One rewrite turns the goal <code>h₁.union h₂ l = none</code> into <code>h₂ l = none</code>, which is <code>hb</code>. This half of the proof never mentions the <code>match</code> at all — the lemma from the previous exercise has absorbed it.'}
     ],
     deep:[
       {t:'trace', title:'Forwards: finding out which branch you are in',
        start:'h₁ h₂ : Heap\nl : Loc\n⊢ h₁.union h₂ l = none ↔ h₁ l = none ∧ h₂ l = none',
        steps:[
          {tac:'constructor',
           state:'case mp\nh₁ h₂ : Heap\nl : Loc\n⊢ h₁.union h₂ l = none → h₁ l = none ∧ h₂ l = none',
           h:'Two goals; only the first is shown, and it is the one the next tactic sees.'},
          {tac:'intro h',
           state:'case mp\nh₁ h₂ : Heap\nl : Loc\nh : h₁.union h₂ l = none\n⊢ h₁ l = none ∧ h₂ l = none',
           h:'Nothing here can be attacked. The assumption is about the combination and the goal is about the parts, and only the definition connects them.'},
          {tac:'cases hl : h₁ l with  (none branch)',
           state:'case mp.none\nh₁ h₂ : Heap\nl : Loc\nh : h₁.union h₂ l = none\nhl : h₁ l = none\n⊢ none = none ∧ h₂ l = none',
           h:'The first conjunct has already collapsed to <code>none = none</code>, because the split rewrote the goal as well as recording <code>hl</code>. That is what makes <code>rfl</code> the right first slot.'},
          {tac:'cases hl : h₁ l with  (some branch)',
           state:'case mp.some\nh₁ h₂ : Heap\nl : Loc\nh : h₁.union h₂ l = none\nv : Val\nhl : h₁ l = some v\n⊢ some v = none ∧ h₂ l = none',
           h:'The goal is now visibly unprovable, which is correct — the branch is impossible and the work is to show that. The evidence is <code>h</code> together with <code>hl</code>, not the goal.'},
          {tac:'rw [union_of_some h₂ hl] at h',
           state:'case mp.some\nh₁ h₂ : Heap\nl : Loc\nv : Val\nh : some v = none\nhl : h₁ l = some v\n⊢ some v = none ∧ h₂ l = none',
           h:'The assumption has become an impossibility. Everything after this is bookkeeping.'}
        ],
        done:'The branch closes with absurd h (by simp).'},
       {t:'trace', title:'Backwards: two lines, and no match anywhere',
        start:'case mpr\nh₁ h₂ : Heap\nl : Loc\nha : h₁ l = none\nhb : h₂ l = none\n⊢ h₁.union h₂ l = none',
        steps:[
          {tac:'rw [union_of_none h₂ ha]',
           state:'case mpr\nh₁ h₂ : Heap\nl : Loc\nha : h₁ l = none\nhb : h₂ l = none\n⊢ h₂ l = none',
           h:'The combination has been replaced by the right heap. This is the whole content of the direction, and it is what every later proof about unions will look like once the three lookup lemmas exist.'},
          {tac:'exact hb', state:'', h:'The goal is a hypothesis.'}
        ],
        done:'No goals.'}
     ],
     pitfall:'Using <code>by_cases hl : h₁ l = none</code> in the forward direction. The positive branch works; the negative one leaves <code>hl : ¬h₁ l = none</code> and the untouched goal <code>⊢ h₁ l = none ∧ h₂ l = none</code>, with no value to hand to <code>union_of_some</code> and no rewrite available. The other frequent slip is the argument to the lookup lemmas: <code>union_of_none h₂ hb</code> in the backward direction reads <code>h₁</code> off <code>hb</code> and so looks for the pattern <code>h₂.union h₂ l</code>, reporting <code>Did not find an occurrence</code> against a goal that plainly contains a union. The explicit argument is the <i>right</i> heap; the left one comes from the hypothesis.',
     variants:'<code>exact absurd h (by simp)</code> can be written <code>exact absurd h (some_ne_none v)</code>, citing Unit 02\'s theorem instead of asking <code>simp</code> to rediscover it, or shortened to <code>cases h</code>, which observes that a hypothesis equating two distinct constructors leaves no cases to prove. All three compile. Stated as an implication in the forward direction only, the theorem would still be provable but Unit 10 would be stuck: its associativity proof needs <code>.mpr</code>, to build a proof that a union is undefined somewhere out of two facts about the parts. Reverse the conjunction to <code>h₂ l = none ∧ h₁ l = none</code> and everything still holds, with the two slots swapped — the operation is biased but this particular statement is not, because being undefined is symmetric.'
    },

    /* ------------------------------------------------------------- the unit --- */

    {t:'sec', s:'The empty heap on either side'},

    {t:'p', h:'An operation with a neutral element is a stronger thing than a bare operation, so the next question is whether combining with <code>Heap.empty</code> changes anything. It does not, on either side, and the two proofs are of visibly different lengths. That asymmetry is not an accident of how they were written; it is the <code>match</code>, scrutinising its left argument, showing through.'},

    {t:'ex',
     id:'m2-4',
     name:'union_empty_left / union_empty_right',
     hard:false,
     why:'The two unit laws, and the sharpest demonstration in the course of what a <code>match</code> will and will not do on its own. They are also worked hard downstream: Unit 11 uses them to split any heap trivially into itself and nothing, and Units 15, 17, 23, 29, 32, 33 and 34 all reach for one or the other when an assertion has to be presented as a combination with an empty piece.',
     setup:'Two theorems about equations between whole heaps, so both begin with <code>funext</code>. Write the left one first; then write the same proof for the right one and watch it fail, because the failure is the lesson.',
     goal:'theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by\n  sorry\n\ntheorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by',
     hints:[
       'Both goals are equations between heaps, so both are equations between functions: after <code>funext l</code> the first is <code>Heap.empty.union h l = h l</code> and the second is <code>h.union Heap.empty l = h l</code>. In each, ask what the <code>match</code> is scrutinising and whether that expression is already a constructor.',
       'In the first, the <code>match</code> looks at <code>Heap.empty l</code>, and <code>Heap.empty</code> is the function sending everything to <code>none</code> — so the scrutinee reduces without help and the whole equation is settled by computation. In the second, the <code>match</code> looks at <code>h l</code>, about which nothing at all is known, so a case split is unavoidable.',
       'The first needs <code>rfl</code> after <code>funext l</code> and nothing else. The second needs <code>cases hl : h l with</code>, and then <code>union_of_none</code> and <code>union_of_some</code>, one per branch, each applied with <code>Heap.empty</code> as its explicit heap. One of the two branches then wants a closing tactic that <code>rw</code> will not supply for itself.',
       'The first is <code>funext l; rfl</code>. For the second, <code>funext l</code> then <code>cases hl : h l with</code>; the <code>none</code> branch is <code>rw [union_of_none Heap.empty hl]</code>, which leaves <code>⊢ Heap.empty l = none</code> — one more tactic — and the <code>some</code> branch is <code>rw [union_of_some Heap.empty hl]</code>, which needs nothing further.'
     ],
     sol:'theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by\n  funext l; rfl\n\ntheorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by\n  funext l\n  cases hl : h l with\n  | none   => rw [union_of_none Heap.empty hl]; rfl\n  | some v => rw [union_of_some Heap.empty hl]',
     solNote:'One line against four, for two statements that look like reflections of each other. If you wrote <code>funext l; rfl</code> for the second and were told the two sides are not definitionally equal, that message is the whole point of this exercise; the <i>Why it works</i> panel prints it.',
     expl:'The left law is settled by reduction. <code>Heap.empty l</code> is <code>none</code> — not equal to it, but the same term after unfolding a definition with no case analysis in it — so the <code>match</code> takes its second branch and both sides of the equation are <code>h l</code>. The right law cannot be reduced at all, because the scrutinee is <code>h l</code> and <code>h</code> is a variable. Nothing is known about it, so both branches have to be considered, and each is then closed by the lookup lemma for that branch. The <code>none</code> branch needs one extra step because after the rewrite the goal is <code>Heap.empty l = none</code>, which is true by reduction but is not what <code>rw</code>\'s built-in closing step is willing to try.',
     walk:[
       {tac:'funext l  (left law)', h:'Turned an equation between heaps into an equation at an arbitrary address, and gave a name to that address. Standard for any heap equation since Unit 03.'},
       {tac:'rfl', h:'Closed it. Lean unfolds <code>Heap.union</code> and <code>Heap.empty</code>, finds the scrutinee is the constructor <code>none</code>, takes the second branch, and both sides are the term <code>h l</code>. No lemma about heaps was used and no case was split.'},
       {tac:'funext l  (right law)', h:'The same opening, and now the goal is <code>h.union Heap.empty l = h l</code>, in which the scrutinee is <code>h l</code>.'},
       {tac:'cases hl : h l with', h:'Two branches, each with <code>hl</code> saying which one it is. The right-hand side <code>h l</code> is rewritten by the split, so the branches read <code>⊢ h.union Heap.empty l = none</code> and <code>⊢ h.union Heap.empty l = some v</code>. The left-hand side is not, because the <code>h l</code> inside it is still buried in the folded <code>Heap.union</code>.'},
       {tac:'| none   => rw [union_of_none Heap.empty hl]; rfl', h:'The lookup lemma replaced the combination by <code>Heap.empty l</code>, leaving <code>⊢ Heap.empty l = none</code>. <code>rw</code>\'s trailing closing step does not unfold an ordinary definition, so it declines; <code>rfl</code>, which does, closes it.'},
       {tac:'| some v => rw [union_of_some Heap.empty hl]', h:'The lookup lemma replaced the combination by <code>some v</code>, and the goal was already <code>some v</code> on the right, so <code>rw</code> closed it on its own. One line, no follow-up.'}
     ],
     deep:[
       {t:'trace', title:'The right law, branch by branch',
        start:'h : Heap\n⊢ h.union Heap.empty = h',
        steps:[
          {tac:'funext l',
           state:'h : Heap\nl : Loc\n⊢ h.union Heap.empty l = h l',
           h:'This is the goal on which <code>rfl</code> fails, and the failure message is printed below.'},
          {tac:'cases hl : h l with  (none branch)',
           state:'case none\nh : Heap\nl : Loc\nhl : h l = none\n⊢ h.union Heap.empty l = none',
           h:'The split has decided the right-hand side and recorded why.'},
          {tac:'rw [union_of_none Heap.empty hl]',
           state:'case none\nh : Heap\nl : Loc\nhl : h l = none\n⊢ Heap.empty l = none',
           h:'The combination is gone. What is left is a fact about the empty heap alone, and it is definitional.'},
          {tac:'cases hl : h l with  (some branch)',
           state:'case some\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\n⊢ h.union Heap.empty l = some v',
           h:'One rewrite with <code>union_of_some Heap.empty hl</code> makes both sides <code>some v</code>, and <code>rw</code> finishes.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The left law\'s proof, offered for the right law.',
        src:'theorem uer_bad (h : Heap) : Heap.union h Heap.empty = h := by\n  funext l\n  rfl'},
       {t:'state', cap:'A definitional claim, refused. Nothing is wrong with the statement; it is not true <i>by computation</i>.',
        src:'error: Tactic `rfl` failed: The left-hand side\n  h.union Heap.empty l\nis not definitionally equal to the right-hand side\n  h l'}
     ],
     pitfall:'Splitting with <code>cases h l with</code> instead of <code>cases hl : h l with</code>. It looks right, the branches appear, and the right-hand side of the goal is even rewritten — but nothing is recorded, so the branch has no hypothesis to feed the lookup lemma and the error arrives one line later as <code>Unknown identifier `hl`</code>, pointing at a name you never bound rather than at the tactic that failed to bind it.',
     variants:'The left law does not in fact need <code>funext</code> at all: <code>Heap.union Heap.empty h = h := rfl</code> compiles as a term, for the reason the fold below this exercise gives. The corpus proof keeps <code>funext l</code> because the two laws are then visibly the same proof up to the point where one of them stops working. Swap the empty heap for any other known heap and the left law fails immediately — with <code>Heap.singleton 0 1</code> on the left, the combination holds <code>1</code> at address 0 whatever <code>h</code> says, and the equation is false for every <code>h</code> defined differently there.'
    },

    {t:'detail', title:'Why the right unit law is not settled by reduction', open:false,
     blocks:[
       {t:'p', h:'The <code>funext l</code> in both proofs hides how far the left law gets without it. Take the equation between whole heaps, undisturbed: the <code>match</code> scrutinises <code>Heap.empty l</code>, which is <code>none</code> whatever <code>l</code> is, so the body becomes <code>h l</code>. Reduction goes under the <code>fun l =&gt;</code>, so the whole term becomes <code>fun l =&gt; h l</code>, and Lean identifies that with <code>h</code>. Every step is computation, no fact about <code>h</code> is used — and no <code>funext</code> is needed either, which is why the term-mode <code>rfl</code> in the exercise\'s <i>variants</i> compiles.'},
       {t:'p', h:'In <code>Heap.union h Heap.empty</code> the <code>match</code> scrutinises <code>h l</code>, and <code>h</code> is a variable. There is no computation to do. It is not that Lean is being conservative — there is genuinely no single term the expression reduces to, because the answer depends on a value nobody has supplied. The only way forward is to supply one, in each of the two shapes it could take, which is what the case split does.'},
       {t:'p', h:'The rule to carry forward is short: a <code>match</code> in this course scrutinises the <b>left</b> heap, so a goal about a combination reduces on its own exactly when the left argument answers without a case analysis. <code>Heap.empty</code> does, at every address. <code>Heap.singleton</code> does only once the address being looked up is a numeral as well, because its body is a conditional. A variable heap never does. When it does not, split — and split on the value, not on a proposition about it.'}
     ]},

    /* ------------------------------------------------------------ idempotence --- */

    {t:'p', h:'One theorem left, and it is the one nothing in the definition prepares you for. Combine a heap with <i>itself</i>. The two arguments agree everywhere, so left-biasing has nothing to resolve, and the answer is the heap you started with — the operation is idempotent. That is a perfectly ordinary fact about a total function and a distinctly awkward one about a resource, because a resource you can combine with itself is a resource you have twice over. Unit 14 is where that becomes a problem; this is where the fact gets proved.'},

    {t:'ex',
     id:'x22',
     name:'union_self',
     hard:false,
     why:'Idempotence, which the mathematics of resources does <i>not</i> want. Unit 14 needs this theorem to build the operation that does let one heap satisfy two claims at once, in order to show that separating conjunction is not that operation and that a resource cannot be duplicated. Proving it here means the duplication there is a single <code>exact</code>. It is also the shortest complete demonstration of the shape this unit installs: split on the value, apply the matching lookup lemma, close.',
     setup:'The same opening as the right unit law, and the same two branches. Substitute <code>h</code> for <code>Heap.empty</code> throughout and one of the two branches stops closing; finding out which, and why, is the exercise.',
     goal:'theorem union_self (h : Heap) : Heap.union h h = h := by',
     hints:[
       'After <code>funext l</code> the goal is <code>h.union h l = h l</code>, with the <i>same</i> heap in both positions. The <code>match</code> still scrutinises the left one, and it is still a variable.',
       'Nothing is known about <code>h</code>, so the two cases have to be manufactured. In each case both heaps answer the same thing, so whichever branch the <code>match</code> takes, the answer is what <code>h</code> holds at that address.',
       'The same four tactics as <code>union_empty_right</code> — <code>funext</code>, <code>cases hl : h l with</code>, and <code>rw</code> with <code>union_of_none</code> and <code>union_of_some</code> — with <code>h</code> in place of <code>Heap.empty</code> as the explicit argument to both lemmas. That one substitution changes what the <code>none</code> branch is left holding, so its final step is not the one that closed the unit law.',
       '<code>funext l</code>, then <code>cases hl : h l with</code>. The <code>none</code> branch is <code>rw [union_of_none h hl]</code>, leaving <code>⊢ h l = none</code> — and that is <code>hl</code>, not <code>rfl</code>.'
     ],
     sol:'theorem union_self (h : Heap) : Heap.union h h = h := by\n  funext l\n  cases hl : h l with\n  | none   => rw [union_of_none h hl]; exact hl\n  | some v => rw [union_of_some h hl]',
     solNote:'The only difference from <code>union_empty_right</code> is the explicit argument to the two lookup lemmas — <code>h</code> where that proof had <code>Heap.empty</code> — and that one substitution changes the last tactic of the <code>none</code> branch from <code>rfl</code> to <code>exact hl</code>. That is a fair summary of what those lemmas do: they take a goal about a combination and hand back a goal about whichever part is answering.',
     expl:'Split on what the heap holds at the address. Where it holds nothing, the left argument is silent, so the combination defers to the right argument — which is the same heap, so the goal becomes a restatement of the hypothesis. Where it holds a value, the left argument answers with that value, and the goal becomes an identity. Neither branch uses the fact that the two arguments are equal until the very last step, which is exactly why the theorem is true: left-biasing has nothing to resolve when the two sides agree.',
     walk:[
       {tac:'funext l', h:'An equation between heaps becomes an equation at an address.'},
       {tac:'cases hl : h l with', h:'Two branches with <code>hl</code> recording each. The right-hand side <code>h l</code> is rewritten to <code>none</code> and to <code>some v</code> respectively; the occurrence inside <code>Heap.union</code> is not, since it is still folded.'},
       {tac:'| none   => rw [union_of_none h hl]; exact hl', h:'The explicit heap is now <code>h</code> itself, so the rewrite leaves <code>⊢ h l = none</code>. That is not an identity and <code>rfl</code> will not close it; it is the hypothesis, so <code>exact hl</code> does.'},
       {tac:'| some v => rw [union_of_some h hl]', h:'The rewrite makes the left-hand side <code>some v</code>, matching the right-hand side, and <code>rw</code>\'s trailing step closes the goal.'}
     ],
     deep:[
       {t:'trace', title:'Where this differs from the unit law',
        start:'h : Heap\nl : Loc\n⊢ h.union h l = h l',
        steps:[
          {tac:'cases hl : h l with  (none branch)',
           state:'case none\nh : Heap\nl : Loc\nhl : h l = none\n⊢ h.union h l = none',
           h:'Identical in shape to the unit law\'s <code>none</code> branch.'},
          {tac:'rw [union_of_none h hl]',
           state:'case none\nh : Heap\nl : Loc\nhl : h l = none\n⊢ h l = none',
           h:'And here they part. The unit law left <code>⊢ Heap.empty l = none</code>, which computes. This leaves <code>⊢ h l = none</code>, which does not compute and does not have to: it is <code>hl</code>, written out.'},
          {tac:'cases hl : h l with  (some branch)',
           state:'case some\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\n⊢ h.union h l = some v',
           h:'One rewrite with <code>union_of_some h hl</code> makes both sides <code>some v</code>.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'Ending the <code>none</code> branch the way the unit law ends it.',
        src:'example (h : Heap) : Heap.union h h = h := by\n  funext l\n  cases hl : h l with\n  | none   => rw [union_of_none h hl]; rfl\n  | some v => rw [union_of_some h hl]'},
       {t:'state', cap:'The two sides are equal, and not by computation — which is what a hypothesis is for.',
        src:'error: Tactic `rfl` failed: The left-hand side\n  h l\nis not definitionally equal to the right-hand side\n  none'}
     ],
     pitfall:'Trying <code>funext l; rfl</code>, on the grounds that combining a heap with itself cannot change it. It fails with <code>h.union h l is not definitionally equal to h l</code>, and the reason is the same as for the right unit law: the scrutinee is a variable, so there is no computation to perform. Being <i>equal</i> and being <i>the same term after reduction</i> are different claims, and only the second is <code>rfl</code>\'s business.',
     variants:'Replace the right-hand heap by an unrelated <code>h\'</code> and <code>Heap.union h h\' = h\'</code> is false; the pair already on this page is the counterexample, since with <code>h = Heap.singleton 4 3</code> and <code>h\' = Heap.singleton 4 7</code> the combination answers <code>some 3</code> at address 4 and <code>h\'</code> answers <code>some 7</code>. Weaken the conclusion to <code>Heap.union h h l = h l</code> at a fixed <code>l</code> and the proof is the same minus the <code>funext</code>. What the theorem does <i>not</i> say is as informative: nothing about disjointness appears in it, and <code>h</code> is disjoint from itself only when it is empty, so a course that only ever combined disjoint heaps would never encounter this statement — which is precisely why Unit 14 has to reach for it deliberately.'
    },

    /* ---------------------------------------------------------------- closing --- */

    {t:'note', kind:'tip', title:'The discipline',
     h:'From here on, <code>Heap.union</code> does not appear in a <code>simp</code> bracket, in an <code>unfold</code>, or anywhere else that opens it. Every fact about a combination at an address comes from <code>union_of_none</code>, <code>union_of_some</code> or <code>union_eq_none</code>, and every equation between whole heaps comes from those three under a <code>funext</code> and a <code>cases hl :</code>. This is the same interface rule Unit 06 imposed on <code>Heap.write</code>, <code>Heap.erase</code> and <code>Heap.singleton</code>, and it is imposed for the same reason: a proof that names the definition is a proof that breaks if the definition changes, and it is a proof that ends up staring at an unreduced <code>match</code>.'},

    {t:'dod', h:'You can read <code>Heap.union</code> and say what it answers where both heaps are defined, and why that decision is safe given how the operation is used. You can say why the operation is total rather than partial, and show what a rewrite does when the disjointness proof is inside the term. You can recognise a goal that has stopped on an unreduced <code>match</code>, and name what the <code>match</code> is waiting for. You can supply that thing from a hypothesis, or manufacture it with <code>cases hl : h l with</code>, and you can say what <code>by_cases</code> costs in every proof that uses it here. You have <code>union_of_none</code>, <code>union_of_some</code>, <code>union_eq_none</code>, both unit laws and idempotence, and you can say which of the two unit laws is settled by reduction alone and why its mirror image is not.'},

    {t:'p', h:'We have an operation and a unit. Whether they form anything worth a name depends on associativity and commutativity — and those two behave <i>completely differently</i>, one needing no hypothesis and the other false outright without one. That asymmetry has a name.'}

  ]
});
