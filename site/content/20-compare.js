registerChapter({
  id: 'compare',
  num: '§',
  phase: 'Phase 2 · The logic of ownership',
  title: 'The same proof, several ways',
  blurb: 'Four theorems you have already proved, proved again two or three ways each, with an explicit verdict on which version to write and what the other versions cost.',

  orient: {
    youWill: [
      'Say what a <code>simp</code> bracket depends on, and what a lemma name depends on, and why only one of them survives an edit to a definition.',
      'Read the two ways <code>simp [update]</code> fails on <code>update_shadow</code> — no progress, then a residue — as statements about what <code>simp</code> is and is not willing to do.',
      'Prefer a three-token term to a three-line tactic script, and give the reason in terms of the goal states the script prints.',
      'Prove <code>write_singleton</code> without naming <code>Heap.write</code> or <code>Heap.singleton</code>, and watch the two proofs that do name them break when the definition is re-spelled.',
      'Say, in one sentence, why every rearrangement of a precondition after Unit 17 is a composition of named entailments rather than an argument about heaps.'
    ],
    needs: [
      'Units 04, 06, 08 and 17 for the four theorems, and Unit 05 for the six lookup laws one of the proofs is built from. Every version below compiles against the course as it stands at the end of Module 3.'
    ],
    payoff: 'This is the page to open when you have a proof that works and want to know whether it is the one to keep.'
  },

  blocks: [

    /* ---------------------------------------------------------- framing --- */

    {t:'p', h:'This is a reference page and the course does not pass through it: Unit 18 follows Unit 17 whether or not you stop here. Every theorem on it is one you have already proved. What is new is that each is proved two or three ways, and the versions are set beside each other.'},

    {t:'p', h:'Three of the four verdicts have been stated before and none of them was tested. Unit 04 gave the rule for choosing between <code>simp</code> and <code>rw</code>; Unit 06 named three routes to <code>write_singleton</code> and preferred the third; Unit 17 said to stop before typing <code>intro σ h ⟨…⟩</code>. Each stated a preference and moved on. Here every rejected version goes through Lean, and where a verdict predicts a failure the failure is produced on the page — so what you have been taking on trust becomes something you can check. The argument is the part to keep; the theorems are the vehicles.'},

    {t:'p', h:'Length settles none of the four. Twice the version to prefer is the shortest of its group, once it is the middle one, and once the shortest thing anyone tries does not compile at all. What separates them is three questions, and they are the same three every time.'},

    {t:'dl', items:[
      {k:'Does the proof name a definition, or a lemma?',
       h:'A proof that puts <code>Heap.write</code> in a <code>simp</code> bracket depends on the <i>text</i> of <code>Heap.write</code>. A proof that names <code>write_same</code> depends on the <i>statement</i> of <code>write_same</code>. Definitions get re-spelled; a statement is the thing an interface promises will not change.'},
      {k:'Where is each hypothesis spent?',
       h:'A proof ending in one <code>simp</code> call claims that something in the bracket closed the goal. A proof ending in <code>rw [if_neg hx]</code> says which conditional was decided and by which fact. When a theorem is later found to need a hypothesis it does not have, the second kind tells you where to look.'},
      {k:'How long is the goal state you have to read?',
       h:'Every tactic line is written by looking at a display. A proof whose displays are four lines long costs less to write than one whose displays are fourteen. Long displays are sometimes unavoidable; that is exactly why it matters when they are not.'}
    ]},

    {t:'note', kind:'key', title:'What the verdicts are about',
     h:'None of the four verdicts below is about taste. Each is a prediction about what happens to the proof when something underneath it moves — a definition re-spelled, a hypothesis dropped, a lemma generalised. The version that survives the move is the one to write, even when it is longer.'},

    /* ============================================================ one ===== */

    {t:'sec', s:'One · <code>update_shadow</code>'},

    {t:'p', h:'Writing <code>b</code> at <code>x</code> over a function that already had <code>a</code> written at <code>x</code> is the same as writing <code>b</code> at <code>x</code>. Unit 04 proves it in two tactic lines, and the second of them runs one call over both branches, because after <code>by_cases</code> the two goals differ only in the sign of <code>h</code>.'},

    {t:'code', cap:'Unit 04, exercise <code>m0-3</code>.',
     src:'theorem update_shadow (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  by_cases h : y = x <;> simp [update, h]'},

    {t:'h4', s:'Every conditional decided by hand'},

    {t:'p', h:'That <code>simp</code> call does three jobs at once: it replaces <code>update</code> by its body, it decides the conditionals using <code>h</code>, and it closes the equation that is left. Give each job to a step with a name, and the proof stops hiding the one number that tells its two branches apart.'},

    {t:'code', tag:'illustration', cap:'Compiled against the course through Unit 17. Same statement, same opening <code>funext</code>, and nothing hidden after it.',
     src:'theorem update_shadow_explicit (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  unfold update\n  by_cases h : y = x\n  · rw [if_pos h, if_pos h]\n  · rw [if_neg h, if_neg h, if_neg h]'},

    {t:'state', cap:'After <code>unfold update</code>, before the split. Three conditionals, all on the same condition.',
     src:'f : Nat → Nat\nx a b y : Nat\n⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y'},

    {t:'trace', title:'The <code>neg</code> branch, one rewrite at a time',
     start:'case neg\nf : Nat → Nat\nx a b y : Nat\nh : ¬y = x\n⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y',
     steps:[
       {tac:'rw [if_neg h]',
        state:'case neg\nf : Nat → Nat\nx a b y : Nat\nh : ¬y = x\n⊢ (if y = x then a else f y) = if y = x then b else f y',
        h:'The outer conditional on the left is decided false, so the whole left-hand side collapses to its <code>else</code> branch — which is the second write, now exposed.'},
       {tac:'rw [if_neg h]',
        state:'case neg\nf : Nat → Nat\nx a b y : Nat\nh : ¬y = x\n⊢ f y = if y = x then b else f y',
        h:'The same rewrite again, on what is now the leftmost conditional. Off <code>x</code>, both writes are invisible and the original function shows through.'},
       {tac:'rw [if_neg h]',
        h:'The right-hand side collapses the same way, and the trailing <code>rfl</code> that <code>rw</code> attempts closes <code>f y = f y</code>.'}
     ],
     done:'No goals.'},

    {t:'p', h:'Three rewrites, three conditionals, in the order they appear in the goal. The <code>pos</code> branch needs only two, because deciding the outer conditional on the left throws the inner one away unread. Two against three is the number the one-call version hides: it closes both branches with the same text and never says that one of them had less to do.'},

    {t:'h4', s:'The call that does not work'},

    {t:'code', tag:'sketch', cap:'The shortest thing anyone tries: the bracket on its own, with no <code>funext</code> in front of it. Does not compile, and the error is below.',
     src:'theorem update_shadow_one_call (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  simp [update]'},

    {t:'state', cap:'Two conventions hold for every message on this page: the <code>line:column</code> prefix Lean puts in front of one is dropped, and where a single mistake produced several messages a blank line separates them.',
     src:'error: `simp` made no progress'},

    {t:'p', h:'Nothing in the goal matches anything in the bracket. Both sides are functions; the body of <code>update</code> sits under a <code>fun</code> that has not been applied to anything, so there is no conditional for <code>simp</code> to reach. Supply a point and it can start.'},

    {t:'code', tag:'sketch', cap:'Does not compile either, and this failure is the interesting one.',
     src:'theorem update_shadow_after_funext (f : Nat → Nat) (x a b : Nat) :\n    update (update f x a) x b = update f x b := by\n  funext y\n  simp [update]'},

    {t:'state', cap:'What <code>simp</code> left standing.',
     src:'error: unsolved goals\nf : Nat → Nat\nx a b y : Nat\n⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y'},

    {t:'p', h:'That residue is, line for line, the goal <code>unfold update</code> reaches in the explicit proof above. <code>simp</code> got exactly as far and then stopped: it rewrites, and it does not split a case. The condition <code>y = x</code> is neither true nor false until something decides it, and nothing here has. <code>by_cases</code> is what supplies the decision, which is why it appears in both of the proofs that work.'},

    {t:'note', kind:'key', title:'Verdict · <code>update_shadow</code>',
     h:'Write the explicit version once — here or on <code>write_shadow</code> — and read the three rewrites. After that write the first version. Both branches want the same bracket, the route through them is not the content, and one <code>simp</code> call is a fair way to say so. Reach back for <code>if_pos</code> and <code>if_neg</code> when the branches stop agreeing. <code>update_comm</code> is where that first happens — three regions, one <code>have</code>, and a different rewrite list in each — which is why its corpus proof is hand-driven, and why <code>write_comm</code>\'s is too.'},

    /* ============================================================ two ===== */

    {t:'sec', s:'Two · <code>disjoint_empty_left</code>'},

    {t:'p', h:'The empty heap does not overlap anything. <code>Heap.disjoint h₁ h₂</code> is <code>∀ l, h₁ l = none ∨ h₂ l = none</code>, so with <code>Heap.empty</code> on the left the left disjunct holds at every address. The proof is that sentence written down.'},

    {t:'code', cap:'Unit 08, exercise <code>m2-2</code>. No tactic block at all.',
     src:'theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=\n  fun _ => Or.inl rfl'},

    {t:'p', h:'Read it from the right. <code>rfl</code> proves <code>Heap.empty l = none</code>; <code>Or.inl</code> makes that the left half of the disjunction; <code>fun _ =></code> makes the whole thing hold at every <code>l</code> without ever looking at which <code>l</code> it is. Nothing in the term mentions <code>h</code> and nothing mentions an address: the proof is uniform in both, and three tokens is what that uniformity costs.'},

    {t:'code', tag:'illustration', cap:'The same three steps, one per line.',
     src:'theorem disjoint_empty_left_tac (h : Heap) : Heap.disjoint Heap.empty h := by\n  intro l\n  left\n  rfl'},

    {t:'trace', title:'What the script prints on the way',
     start:'h : Heap\n⊢ Heap.empty.disjoint h',
     steps:[
       {tac:'intro l',
        state:'h : Heap\nl : Loc\n⊢ Heap.empty l = none ∨ h l = none',
        h:'<code>intro</code> reaches through the definition of <code>Heap.disjoint</code> to the <code>∀</code> underneath it and fixes an address.'},
       {tac:'left',
        state:'h : Heap\nl : Loc\n⊢ Heap.empty l = none',
        h:'The choice of disjunct, made as a separate move. In the term it is the <code>inl</code> in <code>Or.inl</code>.'},
       {tac:'rfl',
        h:'<code>Heap.empty</code> is the constantly-<code>none</code> function, so both sides reduce to <code>none</code>.'}
     ],
     done:'No goals.'},

    {t:'cmp',
     left: {t:'The term', kind:'good',
            h:'Three tokens, each naming the step it is, on the line where the theorem is stated.',
            src:'fun _ => Or.inl rfl'},
     right:{t:'The script', tag:'sketch',
            h:'The same three steps, plus three goal displays you have to read in order to be sure the next line is the right one. The body only — the statement is above.',
            src:'intro l\nleft\nrfl'}},

    {t:'p', h:'Every goal in that trace is longer than the entire term proof. That is the case against the script <i>here</i>, and it is not a general rule: a script earns its displays whenever they tell you something you did not already know. These three do not.'},

    {t:'code', tag:'illustration', cap:'The third version. It works.',
     src:'theorem disjoint_empty_left_simp (h : Heap) : Heap.disjoint Heap.empty h := by\n  simp [Heap.disjoint, Heap.empty]'},

    {t:'p', h:'This one hands the whole theorem to <code>simp</code> with both definitions in the bracket. It is the version that will break first: it depends on the text of <code>Heap.disjoint</code> and the text of <code>Heap.empty</code>, and it records nothing about which disjunct was chosen. Take one name out of the bracket and it gets no further than opening the other.'},

    {t:'code', tag:'sketch', cap:'One name short. Does not compile.',
     src:'theorem disjoint_empty_left_half (h : Heap) : Heap.disjoint Heap.empty h := by\n  simp [Heap.disjoint]'},

    {t:'state', cap:'The residue: the theorem, with one definition opened and nothing else done.',
     src:'error: unsolved goals\nh : Heap\n⊢ ∀ (l : Loc), Heap.empty l = none ∨ h l = none'},

    {t:'note', kind:'key', title:'Verdict · <code>disjoint_empty_left</code>',
     h:'The term. It is shorter than any single goal state the script prints, it says which disjunct it chose, and it survives any re-spelling of <code>Heap.empty</code> under which <code>Heap.empty l</code> still reduces to <code>none</code>. Unit 08 makes the same call for <code>disjoint_empty_right</code>, which is the same three tokens with <code>Or.inr</code>. Reach for a script when the disjunct is not the same one at every address: <code>singleton_disjoint</code> chooses <code>right</code> at one address and <code>left</code> everywhere else, and no term does that in three tokens.'},

    /* ========================================================== three ===== */

    {t:'sec', s:'Three · <code>write_singleton</code>'},

    {t:'p', h:'Writing <code>w</code> into the one-cell heap holding <code>v</code> at <code>l</code> gives the one-cell heap holding <code>w</code>. Two of Unit 06\'s eleven equations are ever called again by name and this is one of them: Units 23, 29, 31 and 37 all use it. So the question of which of its three proofs you would rather have inherited is a real one.'},

    {t:'code', cap:'Unit 06, exercise <code>m1-8</code>. Pointwise, one bracket for both branches: the shape of Section One.',
     src:'theorem write_singleton (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]'},

    {t:'code', tag:'illustration', cap:'The same proof with the conditionals decided by hand.',
     src:'theorem write_singleton_rw (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  unfold Heap.write Heap.singleton\n  by_cases hx : x = l\n  · rw [if_pos hx, if_pos hx]\n  · rw [if_neg hx, if_neg hx, if_neg hx]'},

    {t:'state', cap:'After <code>unfold Heap.write Heap.singleton</code>.',
     src:'l : Loc\nv w : Val\nx : Loc\n⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none'},

    {t:'p', h:'That is Section One\'s goal with <code>some w</code>, <code>some v</code> and <code>none</code> standing where <code>b</code>, <code>a</code> and <code>f y</code> stood. The three rewrites are the same three, and so is everything they have to teach. Two proofs down and nothing new has happened.'},

    {t:'h4', s:'The same theorem without opening anything'},

    {t:'p', h:'Unit 05 proved six lookup laws and then made a rule of not unfolding the operations again. Take the rule literally. The two sides are heaps, so compare them at an arbitrary address; and at that address use the laws instead of the definitions.'},

    {t:'code', tag:'illustration', cap:'Four lemma names, no definition, and the same two branches.',
     src:'theorem write_singleton_iface (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  by_cases hx : x = l\n  · rw [hx, write_same, singleton_same]\n  · rw [write_other _ l x w hx, singleton_other l x v hx, singleton_other l x w hx]'},

    {t:'p', h:'The <code>pos</code> branch is Unit 06\'s route three, unchanged: <code>rw [hx]</code> puts both reads literally at <code>l</code>, which is the shape the two <code>_same</code> laws are stated in, and then one law disposes of each side. The <code>neg</code> branch is the longer one, and it is where you can see what a lookup law charges for.'},

    {t:'trace', title:'The <code>neg</code> branch, rewrite by rewrite',
     start:'case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x',
     steps:[
       {tac:'rw [write_other _ l x w hx]',
        state:'case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ Heap.singleton l v x = Heap.singleton l w x',
        h:'The write comes off the front and the heap underneath shows through, whatever it is: <code>write_other</code> holds for every heap, which is why its first argument is left as <code>_</code>. What it does not hold for is an arbitrary read point, and <code>hx</code> is what pays for that.'},
       {tac:'rw [singleton_other l x v hx]',
        state:'case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ none = Heap.singleton l w x',
        h:'Away from <code>l</code> a singleton holds nothing. The two sides differ only in the stored value, so this rewrite fires on the left and leaves the right standing.'},
       {tac:'rw [singleton_other l x w hx]',
        h:'The same law at <code>w</code> instead of <code>v</code> — a separate instance, which is why it is a separate entry. That leaves <code>none = none</code>.'}
     ],
     done:'No goals.'},

    {t:'p', h:'Four lemmas, no definitions, and every one of the four was proved once in Unit 05. Not one goal state along the way contains an <code>if</code> — which is what "the proof mentions no definition" looks like from inside the display.'},

    {t:'p', h:'The difference between this proof and the other two is not length. It is what happens when <code>Heap.singleton</code> is re-spelled. Suppose it had been defined as a write into the empty heap rather than as a conditional — the same function, a different text.'},

    {t:'code', tag:'illustration', cap:'A namespace with the definition changed. The two lookup laws are re-proved; then <code>write_singleton_iface</code>\'s proof is copied in character for character, with only the name of the singleton changed in the statement above it.',
     src:'namespace Retro\n\ndef singleton (l : Loc) (v : Val) : Heap := Heap.write Heap.empty l v\n\ntheorem singleton_same (l : Loc) (v : Val) : singleton l v l = some v :=\n  write_same Heap.empty l v\n\ntheorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) : singleton l v x = none := by\n  rw [singleton, write_other Heap.empty l x v hne]\n  simp [Heap.empty]\n\ntheorem write_singleton_iface (l : Loc) (v w : Val) :\n    Heap.write (singleton l v) l w = singleton l w := by\n  funext x\n  by_cases hx : x = l\n  · rw [hx, write_same, singleton_same]\n  · rw [write_other _ l x w hx, singleton_other l x v hx, singleton_other l x w hx]\n\nend Retro'},

    {t:'p', h:'One line of proof for the first lookup law and two for the second, and that is the whole cost of the change. The proof of <code>write_singleton</code> underneath them is the interface version, unedited, and it compiles: it never mentioned the definition, so it never noticed that the definition moved.'},

    {t:'code', tag:'sketch', cap:'The pointwise proof, copied into the same namespace. The <code>def</code> is repeated so the block stands on its own. Does not compile.',
     src:'namespace Retro\ndef singleton (l : Loc) (v : Val) : Heap := Heap.write Heap.empty l v\n\ntheorem write_singleton_pointwise (l : Loc) (v w : Val) :\n    Heap.write (singleton l v) l w = singleton l w := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]\nend Retro'},

    {t:'state', cap:'Two goals left standing, and a second message naming the dead bracket entry. The linter\'s two further lines — a hint offering to delete the argument, and a note saying which option switches the linter off — are dropped.',
     src:'error: unsolved goals\ncase pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ some w = singleton l w l\n\ncase neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ singleton l v x = singleton l w x\n\nwarning: This simp argument is unused:\n  Heap.singleton'},

    {t:'p', h:'<code>Heap.singleton</code> is not in the goal any more, so one entry of the bracket has nothing to fire on and Lean says so. Both surviving goals are true; neither is closed, because nothing in the proof knows how to look inside the new definition. The explicit <code>rw</code> version stops before the case split and names the culprit outright: it puts <code>Heap.singleton</code> in an <code>unfold</code> rather than in a bracket, and an <code>unfold</code> that finds nothing to unfold is an error, not a silent no-op.'},

    {t:'state', cap:'What <code>write_singleton_rw</code>, copied into <code>Retro</code>, says instead.',
     src:'error: Tactic `unfold` failed to unfold `Heap.singleton` in\n  (if x = l then some w else singleton l v x) = singleton l w x'},

    {t:'detail', title:'The reuse that does not fit: <code>write_of_eq</code>', tag:'aside', open:false, blocks:[
      {t:'p', h:'There is a lemma in Unit 06 that looks made for this: writing into a cell the value it already holds changes nothing.'},
      {t:'code', cap:'Unit 06, exercise <code>x14</code>. Statement only.',
       src:'theorem write_of_eq {h : Heap} {l : Loc} {v : Val} (hl : h l = some v) :\n    Heap.write h l v = h'},
      {t:'p', h:'The instance to try is <code>write_of_eq (singleton_same l v)</code>: the singleton does hold <code>v</code> at <code>l</code>, so its own hypothesis is discharged by a lookup law and nothing else is needed.'},
      {t:'code', tag:'sketch', cap:'Does not compile.',
       src:'theorem write_singleton_of_eq (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  rw [write_of_eq (singleton_same l v)]'},
      {t:'state', cap:'The pattern the instantiation produced, and the goal it was matched against.',
       src:'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  (Heap.singleton l v).write l v\nin the target expression\n  (Heap.singleton l v).write l w = Heap.singleton l w\n\nl : Loc\nv w : Val\n⊢ (Heap.singleton l v).write l w = Heap.singleton l w'},
      {t:'p', h:'The two occurrences of <code>v</code> in <code>write_of_eq</code>\'s statement are the same <code>v</code>: the value written has to be the value already there. Here the cell holds <code>v</code> and <code>w</code> is written, so the pattern Lean builds ends in <code>l v</code> and the goal ends in <code>l w</code>. The lemma covers exactly the case <code>v = w</code>, and in that case the theorem <i>is</i> <code>write_of_eq</code> and needs no separate proof. Reuse is the habit this page recommends and it does not always pay; when it does not, the error names the argument that disagreed, which is the cheapest possible way to find out.'}
    ]},

    {t:'note', kind:'key', title:'Verdict · <code>write_singleton</code>',
     h:'The interface version. Its cost is that you have to know the four lookup laws by name; its return is that the proof text mentions no definition, so nothing underneath it can move without a lemma statement moving too. That is what reuse buys, and it is why the pointwise work is done in the heap layer at all rather than later, inside a proof about a program. The corpus proof is the pointwise one, and that is not an oversight: Unit 06 is the unit that finishes the interface, so it is the last place where opening a heap operation is allowed. From Unit 07 onwards the third version is the only one of the three still available to you.'},

    /* =========================================================== four ===== */

    {t:'sec', s:'Four · <code>star_swap_middle</code>'},

    {t:'p', h:'<code>P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R)</code>: the first two conjuncts change places inside a nest. Unit 17 proves it by composing three entailments built out of four named laws, and no heap appears anywhere in the proof.'},

    {t:'code', cap:'Unit 17, exercise <code>m4-8</code>. A term, not a tactic block.',
     src:'theorem star_swap_middle (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) :=\n  entails_trans (star_assoc_right P Q R)\n    (entails_trans (star_mono_left R (star_comm P Q)) (star_assoc_left Q P R))'},

    {t:'txt', cap:'The chain the two <code>entails_trans</code> compose, one shape per line, with the entailment that produces it on the right.',
     src:'   P ∗ (Q ∗ R)\n ⊢ (P ∗ Q) ∗ R        star_assoc_right P Q R\n ⊢ (Q ∗ P) ∗ R        star_mono_left R (star_comm P Q)\n ⊢ Q ∗ (P ∗ R)        star_assoc_left Q P R'},

    {t:'p', h:'Three entailments, composed by two <code>entails_trans</code>. The middle one carries the work: <code>star_comm</code> swaps <code>P</code> and <code>Q</code> where they sit, and <code>star_mono_left</code> carries that swap into the left operand of the outer <code>∗</code>, leaving <code>R</code> alone. The two re-bracketings on either side of it exist to put <code>P</code> and <code>Q</code> next to each other and then to put the result back.'},

    {t:'h4', s:'The same theorem from the definition'},

    {t:'p', h:'Nothing forces the algebra. <code>∗</code> is an existential over two heaps and four conjuncts — the six slots you unpack it with — and the theorem can be proved by taking the hypothesis apart and building the conclusion out of the pieces.'},

    {t:'code', tag:'illustration', cap:'Seven lines. Compiled against the course through Unit 17.',
     src:'theorem star_swap_middle_sem (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ Q ∗ (P ∗ R) := by\n  intro σ h ⟨h₁, hQR, hd₁, hu₁, hp, ⟨hQ, hR, hd₂, hu₂, hq, hr⟩⟩\n  subst hu₂\n  obtain ⟨hdPQ, hdPR⟩ := disjoint_union_right.mp hd₁\n  refine ⟨hQ, Heap.union h₁ hR, ?_, ?_, hq, ⟨h₁, hR, hdPR, rfl, hp, hr⟩⟩\n  · exact disjoint_union_right.mpr ⟨disjoint_symm hdPQ, hd₂⟩\n  · rw [hu₁, ← union_assoc, union_comm hdPQ, union_assoc]'},

    {t:'p', h:'Four heap names come out of the hypothesis and a fifth is built by hand; one bridge is used in both directions; an associativity rewrite is run backwards before it is run forwards. Every one of those choices is made while looking at a context of twelve, thirteen and then fourteen lines. None of the machinery is new. <code>star_comm</code> is proved from <code>disjoint_symm</code> and <code>union_comm</code>, and <code>star_assoc_left</code> from both disjointness bridges and <code>union_assoc</code> — the same apparatus, spent there once inside a theorem that has a name, and spent here again inside a theorem that will not lend it to anyone.'},

    {t:'detail', title:'The semantic proof, tactic by tactic', tag:'aside', open:false, blocks:[
      {t:'p', h:'Here are those three states. Read them as the working conditions rather than as mathematics: this is the display a tactic line has to be chosen in front of.'},
      {t:'state', cap:'After the <code>intro</code>. Eleven names have come out of one hypothesis.',
       src:'P Q R : Assertion\nσ : Store\nh h₁ hQR : Heap\nhd₁ : h₁.disjoint hQR\nhu₁ : h = h₁.union hQR\nhp : P σ h₁\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhu₂ : hQR = hQ.union hR\nhq : Q σ hQ\nhr : R σ hR\n⊢ (Q ∗ P ∗ R) σ h'},
      {t:'state', cap:'After <code>subst hu₂</code> and the bridge. <code>hQR</code> is gone and the two disjointness facts the conclusion needs are in the context.',
       src:'P Q R : Assertion\nσ : Store\nh h₁ : Heap\nhp : P σ h₁\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : h₁.disjoint (hQ.union hR)\nhu₁ : h = h₁.union (hQ.union hR)\nhdPQ : h₁.disjoint hQ\nhdPR : h₁.disjoint hR\n⊢ (Q ∗ P ∗ R) σ h'},
      {t:'state', cap:'The second hole left by the <code>refine</code>: the union equation for the new cut.',
       src:'case refine_2\nP Q R : Assertion\nσ : Store\nh h₁ : Heap\nhp : P σ h₁\nhQ hR : Heap\nhd₂ : hQ.disjoint hR\nhq : Q σ hQ\nhr : R σ hR\nhd₁ : h₁.disjoint (hQ.union hR)\nhu₁ : h = h₁.union (hQ.union hR)\nhdPQ : h₁.disjoint hQ\nhdPR : h₁.disjoint hR\n⊢ h = hQ.union (h₁.union hR)'},
      {t:'p', h:'The last line of the proof is read off that goal: <code>hu₁</code> replaces <code>h</code>, and then the union is re-associated left, commuted, and re-associated right. <code>union_comm</code> is the only step of the four with a hypothesis, and <code>hdPQ</code> is the one it wants — which is why the bridge was applied before the <code>refine</code>, at a point where no goal was yet asking for it.'}
    ]},

    {t:'cmp',
     left: {t:'What the algebraic proof asks you to know', kind:'good',
            h:'Which of four named entailments carries each shape to the next. No heap appears anywhere in it, there is no goal display at all because the proof is a term, and there is nothing to get wrong except the order.'},
     right:{t:'What the semantic proof asks you to know',
            h:'Which of five heaps goes in which of six slots, which way each disjointness bridge points, and the four-step rewrite that turns <code>h₁ ∪ (hQ ∪ hR)</code> into <code>hQ ∪ (h₁ ∪ hR)</code> — all chosen while reading fourteen lines of context.'}},

    {t:'p', h:'This is why Module 3 has the shape it has. Every law of <code>∗</code> was proved once, from the definition, in Units 14 to 16, and each of those proofs paid the full price in cuts, bridges and union rewrites. What that buys is that no proof after them has to. A rearrangement of a precondition becomes a composition of finished entailments, and the heaps stay inside the theorems that were proved about them. The version above is what such a rearrangement looks like if you decline the algebra; <code>entails_trans</code> is called eleven more times in the fragments after Unit 17, and every one of those calls is a semantic proof not written.'},

    {t:'note', kind:'key', title:'Verdict · <code>star_swap_middle</code>',
     h:'The algebraic one, and the general form of the rule is: when a connective has an algebra, use the algebra. Unfolding a definition that has already been characterised by theorems throws the characterisation away and buys nothing back. The one situation in which the semantic proof is right is the one where no law covers the move you need — and then what to write is the missing law, stated in the algebra, not a proof that reaches under it.'},

    /* ------------------------------------------------------------ close --- */

    {t:'sec', s:'The four verdicts'},

    {t:'tbl', cap:'Same four theorems, same order. The last column is the question from the top of the page that decided each one.',
     head:['theorem', 'the versions', 'preferred', 'decided by'],
     rows:[
       ['<code>update_shadow</code>',
        'one bracket for both branches · every conditional by hand · one <code>simp</code> call and no split',
        'one bracket — after writing the explicit one once',
        'where each hypothesis is spent; the third version does not exist'],
       ['<code>disjoint_empty_left</code>',
        'term · script · <code>simp</code> with both definitions',
        'the term',
        'the length of the goal states, and what the <code>simp</code> bracket depends on'],
       ['<code>write_singleton</code>',
        'pointwise with <code>simp</code> · pointwise with <code>rw</code> · through the lookup laws',
        'through the lookup laws',
        'definition versus lemma — only the third survives a re-spelling'],
       ['<code>star_swap_middle</code>',
        'four names and two <code>entails_trans</code> · destructuring the definition',
        'the four names',
        'all three at once: no definition, no heap, no display']
     ]},

    {t:'p', h:'A fifth comparison waits until Unit 30, where a four-command program is specified twice over — once by composing the rules one command at a time, once by arguing about the program directly. It needs Module 7 in place and cannot be read from here.'},

    {t:'p', h:'Nothing on this page needs remembering. Come back to it when you have a proof that works and want to know whether it is the one to keep. The course resumes at Unit 18, with what Unit 17 said the algebra cannot do: state the frame rule, because the frame rule is about a command leaving a frame alone, and there are no commands yet.'}

  ]
});
