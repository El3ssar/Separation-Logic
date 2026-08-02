registerChapter({
  id: 'assertions',
  num: '12',
  ledgerForward: ['star_or_left', 'star_or_right'],
  phase: 'Phase 2 · The logic of ownership',
  title: 'Assertions and entailment',
  blurb: 'The type of a proposition about memory, the relation that says one such proposition follows from another, and the classical connectives lifted onto it — every one of them a construction you already had, with two arguments threaded through.',

  orient: {
    youWill: [
      'Read <code>Assertion := Store → Heap → Prop</code> and say why there are two arguments rather than one, by naming the point at which the connective of Unit 14 would fail with one.',
      'Prove an entailment whose goal displays as <code>P ⊢ P</code>, with no binder in sight, by <code>intro σ h hp</code> — and say what <code>intro</code> had to unfold to find three binders.',
      'Write <code>entails_refl</code> and <code>entails_trans</code> as terms, and recognise them as the identity function and composition.',
      'Declare an infix notation with a precedence number, and predict how <code>P ⊢ Q ∧ Q ⊢ P</code> parses before you type it.',
      'Lift <code>True</code>, <code>False</code>, <code>∧</code>, <code>∨</code> and <code>∃</code> pointwise, and prove the three <code>aAnd</code> rules as two projections and a pairing.',
      'Turn a proposition about the store into an assertion with <code>fact</code>, and state precisely what it does not claim — with the proof that it does not claim it.'
    ],
    needs: [
      'Unit 01: <code>fun</code> as a proof, application as modus ponens, <code>⟨…⟩</code> and its flattening, <code>.1</code>/<code>.2</code>, <code>Or.inl</code>/<code>Or.inr</code>, <code>rcases</code>, <code>constructor</code>.',
      'Unit 02: definitional equality and what <code>rfl</code> will accept; <code>abbrev</code> as a reducible <code>def</code>; <code>show</code>.',
      'Unit 07: the two readings of “<code>l</code> holds <code>v</code>”, and the fact that both were written at the type <code>Store → Heap → Prop</code>.'
    ],
    payoff: 'Every rule in the rest of this course is stated as an entailment and chained with <code>entails_trans</code>. Everything else on this page exists so that, two units from now, you can see exactly which of these properties the connective that cuts the heap keeps and which it loses.'
  },

  blocks: [

    /* =============================================================== opening === */

    {t:'p', h:'The first step into the logic is shorter than it looks, because two propositions about memory are already written. Unit 07 wrote them to ask how much a specification owns and left that question open. Look past what they say at the type they share.'},

    {t:'code', tag:'verified', cap:'The two candidate readings of “<code>l</code> holds <code>v</code>”.',
     src:'def ptsAtLeast (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h l = some v\ndef ptsExactly (l : Loc) (v : Val) : Store → Heap → Prop := fun _ h => h = Heap.singleton l v'},

    {t:'p', h:'A store, a heap, and a proposition as the answer. That is what a proposition about memory is, and every definition in the rest of this course has that type. It gets a name.'},

    {t:'code', tag:'verified', cap:'The type of an assertion.',
     src:'abbrev Assertion := Store → Heap → Prop'},

    {t:'p', h:'An assertion is not true, and it is not false. <code>ptsExactly 4 3</code> holds of the one-cell heap at address 4 and fails of every other heap; asking whether it is <i>true</i> is like asking whether <code>x &gt; 3</code> is true. It becomes a proposition only when you supply the two arguments, and the pair of them is what this course means by a <b>state</b>.'},

    {t:'p', h:'It is an <code>abbrev</code>, and for the same reason <code>Heap</code> is. The expression <code>P σ h</code> has to elaborate as a function applied to two arguments, and it only does that if the name unfolds to a function type on its own.'},

    {t:'dl', items:[
      {k:'<code>Store</code>', h:'What the program\'s variables hold — a total function from variables to values, from Unit 00. Nobody owns a variable. Two parts of a program that both read <code>x</code> are not in conflict, and no part of this course will ever divide a store between them.'},
      {k:'<code>Heap</code>', h:'What is owned: the partial function Module 1 built and Module 2 learned to cut in two. This is the argument that gets divided, and it is the only one.'},
      {k:'<code>Prop</code>', h:'The answer is a proposition, not a Boolean. Whether an arbitrary heap satisfies an arbitrary assertion is a question about infinitely many addresses; nothing computes it, and nothing needs to.'}
    ]},

    {t:'p', h:'The two arguments could have been one. Nothing stops you bundling a store and a heap into a single object and giving assertions one argument — Module 4 does bundle exactly those two things, because a running program has one state and not two, and this would then be the same type with one layer of packaging. What stops it is the connective this module is being built to support. That connective says: <i>the heap divides into two pieces, the first satisfies P, the second satisfies Q</i>. Divide what? If the argument were a single package, you would have to say how a package divides — and the only honest answer is <i>heap by heap, store shared by both</i>, which is the two-argument type again with extra ceremony on top. Splitting a state and splitting a heap are not the same operation, and one of them does not exist.'},

    {t:'p', h:'Then why carry the store at all? Because a specification has to be able to say something about the program\'s variables, and exactly one of the definitions below does nothing else. Unit 22\'s postconditions have the shape <i>the variable <code>x</code> now holds 10, and the heap is untouched</i>; the first half of that is a statement about <code>σ</code> alone. Between here and there the store binder is written and discarded: Unit 13\'s two definitions both bind it and throw it away. That is not waste. It is one unused binder held open until Module 5 needs it, and adding it later would mean restating every assertion in the course.'},

    /* ============================================================ entailment === */

    {t:'sec', s:'Entailment'},

    {t:'p', h:'Two assertions, and a question: what should it mean for the second to follow from the first? Not implication, because neither of them is a proposition and <code>→</code> has nothing to connect. The judgement that survives the missing arguments is the pointwise one — <i>at every state where the first holds, the second holds too</i> — which, read as a statement about predicates, is containment: the states satisfying <code>P</code> are among the states satisfying <code>Q</code>.'},

    {t:'anat', tag:'verified',
     src:'def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h\ninfix:40 " ⊢ " => Entails',
     parts:[
       {m:'(P Q : Assertion)', h:'Two assertions, both explicit. Every later theorem that takes an entailment as a hypothesis takes its assertions <i>implicitly</i> — you supply the proof and Lean reads the assertions off its type — but the definition itself names them.'},
       {m:'∀ σ h', h:'No types are written and none are needed: two lines down, <code>P σ h</code> forces <code>σ : Store</code> and <code>h : Heap</code>. The quantifier is what makes this a statement about every state rather than about a chosen one, and two of the three arguments you will introduce come from it.'},
       {m:'P σ h → Q σ h', h:'Both sides are now ordinary propositions, so this is an ordinary implication. It is the only implication in the definition. The turnstile declared underneath is not one, and confusing the two is the commonest way to misread a goal on this page.'},
       {m:'infix:40', h:'The first notation this course declares. <code>infix</code> puts the symbol between its two arguments; <code>40</code> is how tightly it binds. Nothing about a precedence number means anything on its own — it means something next to the other numbers in scope.'},
       {m:'" ⊢ "', h:'The token, spaces included. They are part of it: the parser is being told to accept a space, the turnstile and a space. Type it with the abbreviation <code>\\vdash</code>, from Unit 00\'s table; this is the first place in the course where you type the glyph rather than read it.'}
     ]},

    {t:'p', h:'Lean\'s own connectives are declared the same way, with numbers you can look up: <code>∧</code> binds at 35 and <code>∨</code> at 30. Both are below 40, so both bind <i>less</i> tightly than the turnstile, and that is enough to predict what a mixed expression does before you type it. In <code>P ⊢ Q ∧ Q ⊢ P</code> neither turnstile can swallow the <code>∧</code>, so the conjunction is the outermost thing and the expression means <i>P entails Q and Q entails P</i>. That prediction is checkable, and checking it costs one line.'},

    {t:'code', tag:'illustration', cap:'A parse, stated as a theorem. <code>rfl</code> closes it because there is nothing to prove: the notation on the left elaborates to the term on the right, and the two sides are one term.',
     src:'example (P Q : Assertion) : (P ⊢ Q ∧ Q ⊢ P) = (Entails P Q ∧ Entails Q P) := rfl'},

    {t:'p', h:'A smaller number would have changed the meaning rather than the layout. Give the same definition a second notation at level 20 — below <code>∧</code> — and the turnstile becomes greedy: everything to its right is taken as one argument.'},

    {t:'code', tag:'sketch', cap:'A throwaway notation, declared here and used nowhere else, to make the precedence visible. The second line does not compile.',
     src:'infix:20 " ⊩ " => Entails\n\nexample (P Q : Assertion) : Prop := P ⊩ Q ∧ Q ⊩ P'},

    {t:'state', cap:'Two messages from one mistake. The line-and-column prefix is dropped here and everywhere below, and an error quoted inside a sentence has its line breaks removed.',
     src:'error: Application type mismatch: The argument\n  Q\nhas type\n  Assertion\nbut is expected to have type\n  Prop\nin the application\n  And Q\n\nerror: unexpected token \'⊩\'; expected command'},

    {t:'p', h:'Read the first. At level 20 the turnstile reaches past the <code>∧</code>, so Lean tries to build <code>Q ∧ Q</code> out of two assertions, and <code>∧</code> wants propositions. The second message is the parser giving up further along the same line: having committed to a reading that cannot be completed, it meets the second <code>⊩</code> where it expected the expression to have ended. One cause, two complaints, and only the first one is about your mistake.'},

    /* --------------------------------------------------- proving an entailment - */

    {t:'h3', s:'The first entailment'},

    {t:'p', h:'Take the smallest one there is: every assertion entails itself. Read the goal before the proof: it contains two turnstiles, and they are different symbols.'},

    {t:'trace', title:'Reflexivity, tactic by tactic',
     start:'P : Assertion\n⊢ P ⊢ P',
     steps:[
       {tac:'intro σ h hp',
        state:'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ P σ h',
        h:'Three names introduced in one call, and the goal has become a statement about a single state. The leftmost turnstile is the goal display\'s, which every goal state in this course has had since Unit 00. The other one is this unit\'s notation, and it has gone from the goal because it has been taken apart.'},
       {tac:'exact hp',
        state:'',
        h:'The hypothesis is the goal. There was never anything else to do.'}
     ],
     done:'No goals.'},

    {t:'p', h:'The interesting step is the first. Nothing in the goal <code>P ⊢ P</code> displays a binder, and <code>intro</code> took three. It is entitled to: <code>intro</code> reduces the goal until a binder appears, and two layers of naming are in the way. <code>⊢</code> is notation for <code>Entails</code>, so the notation comes off; <code>Entails</code> is a <code>def</code> whose body is <code>∀ σ h, P σ h → Q σ h</code>, so the definition comes off too. Two of the three binders are the quantifier\'s and the third is the arrow\'s. Nothing was hidden — a folded name is a display convention, and <code>intro</code> does not respect it.'},

    {t:'p', h:'That count is checkable rather than asserted: ask for a fourth binder and Lean refuses, and prints the three it did get.'},

    {t:'code', tag:'sketch', cap:'One <code>intro</code> too many.',
     src:'example (P : Assertion) : P ⊢ P := by\n  intro σ h hp hq\n  exact hp'},

    {t:'state', cap:'The error, with the position prefix dropped. The context below it is part of the message.',
     src:'error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce\n\nP : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ P σ h'},

    {t:'p', h:'If you would rather read the binders than infer them, <code>show ∀ σ h, P σ h → P σ h</code> as the first line puts the quantifier on the page and changes nothing about what has to be proved. None of that is needed for the proof itself, which is a term: three binders means a lambda with three arguments, the first two of which the proof never looks at.'},

    {t:'ex',
     id: 'm3-2',
     name: 'entails_refl / entails_trans',
     hard: false,
     why: 'These two are the glue for the entire rest of the course. Every law from Unit 15 on is stated as an entailment, and every chain of reasoning about assertions is a chain of <code>entails_trans</code>: the two names are cited twenty-eight times in the Lean of seven later units. They are also the smallest possible instance of the fact that an entailment is a <i>function</i>, which is the reading you need before Unit 15 asks you to apply one.',
     setup: 'Two theorems in one box. Both are terms — no <code>by</code>, no tactics. In the second, <code>h₁</code> and <code>h₂</code> are proofs and <code>h</code> is a heap; that collision is in the course\'s own Lean and you will meet it again.',
     goal: 'theorem entails_refl (P : Assertion) : P ⊢ P :=\n  sorry\n\ntheorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=',
     hints: [
       'Unfolded, the first goal is <code>∀ σ h, P σ h → P σ h</code> and the second is <code>∀ σ h, P σ h → R σ h</code>. In the second, <code>h₁</code> is <code>∀ σ h, P σ h → Q σ h</code> and <code>h₂</code> is <code>∀ σ h, Q σ h → R σ h</code>. Nothing is hidden; the turnstile is a folded <code>def</code> and this is what it folds.',
       'Fix a state and argue there. Reflexivity: assume <code>P</code> holds at that state, conclude <code>P</code> holds at that state. Transitivity: assume <code>P</code> holds there, push it through the first hypothesis to get <code>Q</code> there, push that through the second to get <code>R</code> there. Both arguments are the two-line proofs you would give on paper, and neither needs a case split.',
       'No tactic and no lemma. Both proofs are lambdas of three arguments. The move you need is that a hypothesis of type <code>P ⊢ Q</code> <i>is</i> a function of three arguments: give it a store, a heap and a proof of <code>P</code> at that state, in that order, and it hands back a proof of <code>Q</code> at that state.',
       'The first is <code>fun _ _ hp => hp</code> in its entirety — the two underscores are the store and the heap, which neither proof reads. For the second, start <code>fun σ h hp =></code>. That leaves you needing something of type <code>R σ h</code>, and <code>h₂ σ h</code> is a function from <code>Q σ h</code> to exactly that.'
     ],
     sol: 'theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp\n\ntheorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=\n  fun σ h hp => h₂ σ h (h₁ σ h hp)',
     solNote: 'The store and the heap are threaded through both applications unchanged. That is the shape of every proof in this unit, and noticing it is most of the point of the unit.',
     expl: 'Reflexivity is the identity function with two arguments in front of it. Transitivity is composition, at a fixed state: <code>h₁ σ h</code> and <code>h₂ σ h</code> are two ordinary implications between two ordinary propositions, and the proof applies the second to the result of the first.',
     walk: [
       {tac:'fun _ _ hp => hp', h:'Three binders, matching the three the goal had: store, heap, premise. The first two are written <code>_</code> because the proof never mentions them. Write <code>fun σ h hp => hp</code> instead and it still compiles, but the linter warns once per name it can see is dead — <code>Variable name `σ` is not explicitly referenced. The binding can be removed (if unused) or named `_` (if used implicitly).</code>, and the same for <code>h</code>. The underscore is how you say the omission was deliberate. What is left is the premise, returned unchanged.'},
       {tac:'fun σ h hp =>', h:'The same three binders, but this time the store and the heap are named, because both have to be handed on to the two hypotheses. After this line the goal is <code>R σ h</code>.'},
       {tac:'h₁ σ h hp', h:'The first entailment applied to the state and the premise. This is where the reading “an entailment is a function” is spent: <code>h₁</code> takes three arguments and returns a proof of <code>Q σ h</code>.'},
       {tac:'h₂ σ h (…)', h:'The second entailment applied to the same state and to the proof the previous line produced. The result has type <code>R σ h</code>, which is the goal. The brackets matter: without them Lean reads <code>h₁</code> as a fourth argument to <code>h₂</code> and says so — <code>the argument h₁ has type P ⊢ Q but is expected to have type Q σ h in the application h₂ σ h h₁</code>.'}
     ],
     deep: [
       {t:'p', h:'The term is short enough to hide its structure. Here is the same proof in tactic mode with the intermediate step named, so the two implications are visible one at a time.'},
       {t:'trace', title:'Transitivity, with the middle step named',
        start:'P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : Q ⊢ R\n⊢ P ⊢ R',
        steps:[
          {tac:'intro σ h hp',
           state:'P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ R σ h',
           h:'The two hypotheses are untouched — they are still entailments, quantified over all states. Only the goal has come down to one state.'},
          {tac:'have hq : Q σ h := h₁ σ h hp',
           state:'P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\nhq : Q σ h\n⊢ R σ h',
           h:'The first entailment instantiated at <code>σ</code> and <code>h</code> and then applied. This is the line the term proof inlines as <code>(h₁ σ h hp)</code>.'},
          {tac:'exact h₂ σ h hq',
           state:'',
           h:'The second entailment at the same state, applied to what the first produced.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Now put the theorem next to the one it is a copy of. Unit 01\'s <code>comp</code> is composition of implications between propositions; <code>entails_trans</code> is the same term with a state threaded through every application.'},
       {t:'cmp',
        left: {t:'Unit 01, <code>x03</code>', src:'theorem comp (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := fun hp => g (f hp)', tag:'verified',
               h:'One binder: the premise. Nothing else to carry.'},
        right:{t:'This unit', src:'theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=\n  fun σ h hp => h₂ σ h (h₁ σ h hp)', tag:'verified',
               h:'Three binders: the state, then the premise. The state is passed to both hypotheses and is otherwise inert.'}}
     ],
     pitfall: 'Applying an entailment to the premise and forgetting the state. <code>h₂ (h₁ hp)</code> looks right and is not: <code>h₁</code>\'s first argument is a store, and <code>hp</code> is a proof. Lean says so, in the words Unit 01 used when a proof was offered where a type was wanted — <code>Application type mismatch: The argument hp has type P σ h of sort `Prop` but is expected to have type Store of sort `Type` in the application h₁ hp</code>. Whenever an application of a hypothesis complains that it wanted a <code>Store</code> or a <code>Heap</code>, you have skipped two arguments.',
     variants: 'Turn the first hypothesis round — <code>h₁ : Q ⊢ P</code> in place of <code>P ⊢ Q</code>, with <code>h₂ : Q ⊢ R</code> unchanged — and the theorem does not become awkward, it becomes false, and it is false at one identifiable point: nothing now leads <i>out</i> of <code>P</code>. The witness uses the two constant assertions defined further down this page: take <code>P</code> to be <code>aTrue</code> and both <code>Q</code> and <code>R</code> to be <code>aFalse</code>. Both hypotheses hold, because <code>aFalse</code> entails anything; the conclusion <code>aTrue ⊢ aFalse</code> is refuted at any state at all. Exchanging the two hypotheses as <i>arguments</i>, by contrast, costs nothing: <code>fun σ h hp => h₁ σ h (h₂ σ h hp)</code> proves the theorem whose hypotheses are listed the other way round, because composition cares which end each entailment starts at and not which one you wrote first. Finally, make the three assertions <i>explicit</i> instead of implicit and the theorem still holds, but every use site downstream has to write three assertions it could have left to Lean — which is why the corpus makes them implicit here and explicit in <code>entails_refl</code>, where there is nothing for Lean to read them off.'
    },

    {t:'note', kind:'key', title:'A preorder, proved rather than assumed',
     h:'<code>⊢</code> is reflexive and transitive. That makes it a preorder on assertions, and the two proofs above are the whole of the evidence — no property of heaps was used, and no property of stores. What it is <b>not</b> is antisymmetric: two assertions can entail each other without being the same term, and <code>aAnd P Q</code> and <code>aAnd Q P</code>, defined below, are the standing example.'},

    /* =========================================================== connectives === */

    {t:'sec', s:'The connectives, lifted'},

    {t:'p', h:'A preorder is not a logic. A logic has connectives — a way to say <i>both</i>, <i>either</i>, <i>some</i> — and there is a mechanical way to get them here. An assertion is a function into <code>Prop</code>. Anything you can do to a proposition, you can do to an assertion one state at a time, by applying it at each state.'},

    {t:'code', tag:'verified', cap:'Four of them. Read each body as its <code>Prop</code>-level counterpart with <code>σ</code> and <code>h</code> threaded through.',
     src:'def aTrue  : Assertion := fun _ _ => True\n\ndef aFalse : Assertion := fun _ _ => False\n\ndef aAnd (P Q : Assertion) : Assertion := fun σ h => P σ h ∧ Q σ h\n\ndef aOr  (P Q : Assertion) : Assertion := fun σ h => P σ h ∨ Q σ h'},

    {t:'defn', term:'Pointwise lifting',
     h:'Given an operation on propositions, the <b>lifted</b> operation on assertions is the one that applies it at every state and does nothing else. <code>aAnd P Q</code> holds at a state exactly when <code>P</code> and <code>Q</code> both do; <code>aTrue</code> holds at every state, and <code>aFalse</code> at none. The two arguments are carried and never inspected, which is why the definitions can be read off their names.',
     cap:'This is not a construction peculiar to memory. It is what you get whenever a logic is indexed by a parameter, and it is available here before a single fact about heaps has been used.'},

    {t:'p', h:'Every counterexample in this unit is built from the two constants, so name their proofs now. <code>True</code> has exactly one, <code>True.intro</code>, and it takes no arguments. <code>False</code> has none — and a hypothesis of that type yields anything at all through <code>.elim</code>, which Unit 01\'s dot-notation rule resolves to <code>False.elim</code>. That is why <code>aFalse</code> entails every assertion there is, in one line.'},

    {t:'code', tag:'illustration', cap:'The bottom of the order, and the top. Neither proof looks at the state.',
     src:'example (P : Assertion) : aFalse ⊢ P := fun _ _ hq => hq.elim\n\nexample (P : Assertion) : P ⊢ aTrue := fun _ _ _ => True.intro'},

    {t:'p', h:'The lifted connectives need new names because the old ones do not typecheck. <code>P ∧ Q</code> for two assertions is not a slightly wrong expression; it is <code>And</code> applied to something that is not a proposition.'},

    {t:'code', tag:'sketch', cap:'Why <code>aAnd</code> exists.',
     src:'example (P Q : Assertion) : Assertion := P ∧ Q'},

    {t:'state', cap:'The message names the culprit: <code>And</code>, applied to an <code>Assertion</code>.',
     src:'error: Application type mismatch: The argument\n  P\nhas type\n  Assertion\nbut is expected to have type\n  Prop\nin the application\n  And P'},

    {t:'p', h:'Three rules govern the lifted conjunction, and they are the three that govern the unlifted one: two projections out of it and one way into it. Their proofs are <code>.1</code>, <code>.2</code> and <code>⟨_, _⟩</code> — with one wrinkle. A hypothesis of type <code>aAnd P Q σ h</code> is not syntactically a conjunction; it is a name applied to four arguments. <code>.1</code> finds a conjunction underneath by unfolding the name — the same move <code>intro</code> made on <code>Entails</code>, asked for by a projection instead of by a tactic.'},

    {t:'ex',
     id: 'm3-3',
     name: 'and_left / and_right / and_intro',
     hard: false,
     why: 'Three one-line proofs, and one sentence to carry away from them: <b>a conjunction has projections.</b> From a proof that <code>P</code> and <code>Q</code> both hold you may keep either one and discard the other, and you may do it at no cost and with no hypothesis. Two units from here you meet a conjunction of assertions for which the corresponding entailment is <i>false</i>, with a compiled refutation of it. These three are the baseline that refutation is measured against. <code>and_intro</code> carries the other half of the baseline: together with <code>entails_refl</code> it makes duplication free — <code>P ⊢ aAnd P P</code>, one line, below — and the theorem Unit 14 proves is that the same statement with the separating connective in place of <code>aAnd</code> has no proof at all.',
     setup: 'Three theorems in one box, all terms. Note which binders are explicit: the first two name their assertions, the third leaves them implicit because they can be read off the two hypotheses.',
     goal: 'theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P :=\n  sorry\n\ntheorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q :=\n  sorry\n\ntheorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=',
     hints: [
       'Unfolded, the first goal is <code>∀ σ h, (P σ h ∧ Q σ h) → P σ h</code> and the second is that same statement with <code>Q σ h</code> as its conclusion. The third is <code>∀ σ h, P σ h → (Q σ h ∧ R σ h)</code>, with <code>h₁</code> and <code>h₂</code> supplying the two conjuncts one at a time.',
       'Fix a state. For the projections: you are handed a proof of a conjunction and asked for one of its halves. For the introduction: you are handed a proof of <code>P</code> at that state and two ways of turning it into something, and you need both results at once.',
       'Nothing new. <code>.1</code> and <code>.2</code> take a conjunction apart; <code>⟨_, _⟩</code> builds one. Both work through the folded name <code>aAnd</code> without being told to unfold it.',
       'The first is <code>fun _ _ h => h.1</code>. In the third, start <code>fun σ h hp =></code> and build a pair whose two components are the two hypotheses applied to <code>σ</code>, <code>h</code> and <code>hp</code>.'
     ],
     sol: 'theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1\n\ntheorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2\n\ntheorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=\n  fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩',
     solNote: 'In the first two theorems <code>h</code> is the proof of the conjunction; in the third it is the heap. That inconsistency is in the course\'s Lean and is left alone here — and it is the type, not the letter, that tells you which one you have.',
     expl: 'Each proof is its <code>Prop</code>-level twin with two inert arguments in front. <code>and_left</code> is <code>And.left</code>, <code>and_right</code> is <code>And.right</code>, and <code>and_intro</code> is <code>And.intro</code> applied at a state.',
     walk: [
       {tac:'fun _ _ h => h.1', h:'Three binders again. The store and the heap are discarded; <code>h</code> is the proof of <code>aAnd P Q σ h</code>, and <code>.1</code> projects out the first conjunct. Lean has to unfold <code>aAnd</code> to know there is a first conjunct, and does.'},
       {tac:'fun _ _ h => h.2', h:'The mirror image, projecting the second. Nothing about the two proofs differs except the digit.'},
       {tac:'fun σ h hp =>', h:'The store and the heap are named this time, because both hypotheses need them. After this line the goal is <code>aAnd Q R σ h</code>.'},
       {tac:'⟨h₁ σ h hp, h₂ σ h hp⟩', h:'A pair. The bracket forces Lean to unfold <code>aAnd</code> to find out how many components the goal wants — two — and then each component is an entailment applied to the same state and the same premise.'}
     ],
     deep: [
       {t:'trace', title:'The projection, tactic by tactic',
        start:'P Q : Assertion\n⊢ aAnd P Q ⊢ P',
        steps:[
          {tac:'intro σ h hpq',
           state:'P Q : Assertion\nσ : Store\nh : Heap\nhpq : aAnd P Q σ h\n⊢ P σ h',
           h:'The hypothesis displays folded, as <code>aAnd P Q σ h</code>. Lean has not unfolded it and will not until something asks.'},
          {tac:'exact hpq.1',
           state:'',
           h:'<code>.1</code> is the request. It resolves by the head constant of <code>hpq</code>\'s type — <code>aAnd</code> — which reduces to <code>And</code>, whose first field is <code>left</code>.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Offering the whole hypothesis where a conjunct is wanted prints the type you have directly above the type that was wanted, and the gap between the two lines is the whole of what <code>.1</code> does:'},
       {t:'state', cap:'From <code>exact hpq</code> in place of <code>exact hpq.1</code>.',
        src:'error: Type mismatch\n  hpq\nhas type\n  aAnd P Q σ h\nbut is expected to have type\n  P σ h'},
       {t:'p', h:'One consequence has to be named here, because it is the one this module later loses. With <code>and_intro</code> and <code>entails_refl</code> you can duplicate an assertion: anything entails itself conjoined with itself.'},
       {t:'code', tag:'illustration', cap:'Duplication, in one line, from the two theorems on this page. It compiles.',
        src:'example (P : Assertion) : P ⊢ aAnd P P := and_intro (entails_refl P) (entails_refl P)'}
     ],
     pitfall: 'Trying to prove <code>and_left</code> by <code>exact hpq</code> after the <code>intro</code>, on the grounds that the hypothesis “contains” the goal. It does not contain it: it is a pair, and the goal is one of the two halves. The error is quoted above. The same slip in reverse — giving <code>⟨_, _⟩</code> only one component in <code>and_intro</code> — reports <code>Insufficient number of fields for `⟨...⟩` constructor: Constructor `And.intro` has 2 explicit field, but only 1 was provided</code>.',
     variants: 'Replace <code>aAnd</code> by <code>aOr</code> in <code>and_left</code> and the statement becomes false — Unit 00\'s distinction, a counterexample and not a gap. It fails at exactly the states where <code>Q</code> holds and <code>P</code> does not, and the cheapest such state is any state whatever once you take <code>P</code> to be <code>aFalse</code> and <code>Q</code> to be <code>aTrue</code>: <code>¬ (∀ P Q : Assertion, aOr P Q ⊢ P)</code> is closed by assuming the statement and applying it to those two assertions, an arbitrary store, <code>Heap.empty</code> and <code>Or.inr True.intro</code>. Three lines, and the last of them is where the disjunction supplies its right-hand half and the goal wants the left. Drop <code>h₂</code> from <code>and_intro</code> and there is nothing to put in the second slot of the pair — the conclusion names an assertion <code>R</code> that then appears in no hypothesis, so no term of that type can exist.'
    },

    {t:'p', h:'Disjunction goes the other way round: two ways in, one way out. The two introductions are <code>Or.inl</code> and <code>Or.inr</code> at a state, and the eliminator is the only proof in this unit that needs a case split, because a disjunction is the one connective here whose proof carries information about <i>which</i> side it came from.'},

    {t:'ex',
     id: 'x27',
     name: 'or_left / or_right / or_elim',
     hard: false,
     why: 'This completes the classical picture, so that when the separating connective arrives in Unit 14 there is a full set of laws to hold it against. It also puts <code>rcases</code> on an assertion-level hypothesis for the first time — the move behind two later theorems you cannot read yet, <code>star_or_left</code> in Unit 15 and <code>star_or_right</code> in Unit 17, which push a disjunction through the new connective in each direction. Neither cites any of these three by name; what they reuse is this proof exactly, with a heap cut carried alongside: <code>rcases</code> to find out which disjunct you were handed, then <code>Or.inl</code> or <code>Or.inr</code> to put it back on the other side.',
     setup: 'Three theorems. The first two are terms; the third wants tactics, because the hypothesis has to be taken apart before either of the two given entailments can be used.',
     goal: 'theorem or_left (P Q : Assertion) : P ⊢ aOr P Q :=\n  sorry\n\ntheorem or_right (P Q : Assertion) : Q ⊢ aOr P Q :=\n  sorry\n\ntheorem or_elim {P Q R : Assertion} (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : aOr P Q ⊢ R := by',
     hints: [
       'Unfolded, the first goal is <code>∀ σ h, P σ h → (P σ h ∨ Q σ h)</code>. The third is <code>∀ σ h, (P σ h ∨ Q σ h) → R σ h</code>, with one entailment covering each disjunct.',
       'Fix a state. For the introductions: you have one of the two halves and must produce the disjunction, so you must also say <i>which</i> half you have. For the elimination: you have a disjunction and two arguments, one per case, and no way to know which case you are in without splitting.',
       'A disjunction cannot be built with <code>⟨…⟩</code> and cannot be projected — Unit 01 gave the reason. The two constructors are <code>Or.inl</code> and <code>Or.inr</code>. To take one apart in tactic mode, <code>rcases … with … | …</code>, and then a focus dot per branch.',
       'The first is <code>fun _ _ hp => Or.inl hp</code>. For the third, <code>intro σ h hpq</code> and then <code>rcases hpq with hp | hq</code>, which leaves two goals with the same conclusion <code>R σ h</code> and different hypotheses.'
     ],
     sol: 'theorem or_left (P Q : Assertion) : P ⊢ aOr P Q := fun _ _ hp => Or.inl hp\ntheorem or_right (P Q : Assertion) : Q ⊢ aOr P Q := fun _ _ hq => Or.inr hq\ntheorem or_elim {P Q R : Assertion} (h₁ : P ⊢ R) (h₂ : Q ⊢ R) : aOr P Q ⊢ R := by\n  intro σ h hpq\n  rcases hpq with hp | hq\n  · exact h₁ σ h hp\n  · exact h₂ σ h hq',
     solNote: 'The two focus dots are optional. Delete them and the two <code>exact</code> lines still close the two goals in order, because a tactic always addresses the first open one. What the dots buy is that a mistake in the second branch is reported inside the second branch, and that you can see there are two branches without counting.',
     expl: 'The introductions are the <code>Or</code> constructors applied at a state; the elimination is a case split followed by the matching hypothesis in each branch. What makes the third longer than <code>and_intro</code> is not the assertions — it is that <code>∨</code> has two constructors and <code>∧</code> has one.',
     walk: [
       {tac:'fun _ _ hp => Or.inl hp', h:'The state is discarded, the premise is injected into the left of the disjunction. Writing <code>hp</code> alone here does not typecheck: <code>P σ h</code> and <code>P σ h ∨ Q σ h</code> are different propositions, and something has to record which side you are on.'},
       {tac:'intro σ h hpq', h:'Three binders as always; the goal comes down to <code>R σ h</code> and the hypothesis is <code>aOr P Q σ h</code>.'},
       {tac:'rcases hpq with hp | hq', h:'Splits the hypothesis into its two cases and replaces the single goal by two, labelled <code>case inl</code> and <code>case inr</code>. Each has the same conclusion and a different premise. As with <code>.1</code>, the folded name <code>aOr</code> is unfolded to find the disjunction.'},
       {tac:'· exact h₁ σ h hp', h:'The first branch: the premise is a proof of <code>P</code> at this state, and <code>h₁</code> is the entailment that takes those to <code>R</code>.'},
       {tac:'· exact h₂ σ h hq', h:'The second branch, with the other hypothesis. The two lines differ only in the digit.'}
     ],
     deep: [
       {t:'trace', title:'The elimination, tactic by tactic',
        start:'P Q R : Assertion\nh₁ : P ⊢ R\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhpq : aOr P Q σ h\n⊢ R σ h',
        steps:[
          {tac:'rcases hpq with hp | hq',
           state:'case inl\nP Q R : Assertion\nh₁ : P ⊢ R\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ R σ h',
           h:'Only the goal Lean will work on next is shown; a second goal <code>case inr</code> sits behind it with <code>hq : Q σ h</code> in place of <code>hp</code> and the same conclusion. The disjunction has left the context: what replaces it is one disjunct per branch.'},
          {tac:'· exact h₁ σ h hp',
           state:'case inr\nP Q R : Assertion\nh₁ : P ⊢ R\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhq : Q σ h\n⊢ R σ h',
           h:'The first branch closes and the second comes forward. From here the two proofs are the same three tokens with different subscripts.'},
          {tac:'· exact h₂ σ h hq',
           state:'',
           h:'The other hypothesis, the other premise.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Leaving out the injection in <code>or_left</code> produces a message that shows what the anonymous binders became:'},
       {t:'state', cap:'From <code>fun _ _ hp => hp</code>. The daggered names are Lean\'s own for the two binders you declined to name; the superscripts count backwards from the most recent, so <code>x✝¹</code> is the store and <code>x✝</code> the heap.',
        src:'error: Type mismatch\n  hp\nhas type\n  P x✝¹ x✝\nbut is expected to have type\n  aOr P Q x✝¹ x✝'}
     ],
     pitfall: 'Skipping the <code>rcases</code> in <code>or_elim</code> and reaching straight for <code>h₁ σ h hpq</code>. The hypothesis is a disjunction, not a proof of <code>P</code>, and Lean says so: <code>Application type mismatch: The argument hpq has type aOr P Q σ h but is expected to have type P σ h in the application h₁ σ h hpq</code>. There is no way round it — half the states satisfying <code>aOr P Q</code> satisfy nothing about <code>P</code> at all, so the split is the content of the proof rather than an obstacle in front of it. The near miss is writing <code>rcases hpq with hp</code>, one name and no bar. That is accepted without complaint and does nothing: there is still one goal, <code>hpq</code> is still the disjunction, and nothing called <code>hp</code> exists — so the failure surfaces on the <i>next</i> line, as <code>Unknown identifier `hp`</code>. The bar is what tells <code>rcases</code> how many branches you are naming.',
     variants: 'Drop <code>h₂</code> and the theorem is false, at exactly the states satisfying <code>Q</code> and not <code>R</code>: take <code>P</code> and <code>R</code> both to be <code>aFalse</code> and <code>Q</code> to be <code>aTrue</code>, so that <code>h₁</code> is available for nothing, and <code>Or.inr True.intro</code> exhibits a state where the premise holds and the conclusion is <code>False</code>. Reverse the conclusion of <code>or_left</code> to <code>aOr P Q ⊢ P</code> and it is false for the same reason, which is <code>m3-3</code>\'s variant with the same witness. The one direction that survives dropping a hypothesis is <code>or_elim</code> with <code>P</code> and <code>Q</code> the same assertion: <code>aOr P P ⊢ R</code> needs only <code>h₁</code>, because <code>rcases</code> still makes two branches and <code>h₁</code> closes both.'
    },

    {t:'p', h:'Existential quantification is the last of the classical connectives, and the only one whose declaration says something you have not seen.'},

    {t:'code', tag:'verified', cap:'A family of assertions indexed by <code>α</code>, collapsed into one assertion.',
     src:'def aExists {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h'},

    {t:'p', h:'<code>Sort u</code> is Lean\'s word for <i>a type at any level</i>: it covers <code>Prop</code>, it covers <code>Type</code>, and it covers everything above. The variable <code>u</code> is bound nowhere — Lean adds the binding itself when it sees a universe variable free in a declaration, which is what <i>universe polymorphic</i> means. You can see the binding it added.'},

    {t:'code', tag:'illustration', cap:'Asking for the full type, with implicit arguments made explicit.',
     src:'#check @aExists'},

    {t:'state', cap:'The <code>u_1</code> is the name Lean chose for the universe variable it bound for you.',
     src:'@aExists : {α : Sort u_1} → (α → Assertion) → Assertion'},

    {t:'p', h:'Writing <code>Type</code> instead would cost nothing that this course spends. Every existential the remaining twenty-six units actually instantiate ranges over a location, a value or a natural number, and all three are types; the two theorems that keep the index general keep it at <code>Sort u</code> only because this declaration does. The generality is taken because it is free, and the one thing it adds is the ability to quantify over a <i>proof</i> — over an <code>α</code> that is itself a proposition — which nothing here does.'},

    {t:'detail', title:'What <code>Type</code> would refuse', tag:'aside', open:false, blocks:[
      {t:'p', h:'A proposition <code>φ</code> lives in <code>Prop</code>, which is <code>Sort 0</code>, and <code>Prop</code> itself lives in <code>Type</code>. So a family indexed by <code>Prop</code> is accepted by both declarations, and only a family indexed by a proposition — one value per proof of <code>φ</code> — tells them apart.'},
      {t:'code', tag:'sketch', cap:'A copy of the definition restricted to <code>Type</code>, and the family it cannot take.',
       src:'def aExistsT {α : Type} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h\n\nexample (φ : Prop) (Q : φ → Assertion) : Assertion := aExistsT Q'},
      {t:'state', cap:'The metavariable in the second type is Lean saying it never found a <code>Type</code> that <code>φ</code> could be.',
       src:'error: Application type mismatch: The argument\n  Q\nhas type\n  φ → Assertion\nbut is expected to have type\n  ?m.1 → Assertion\nin the application\n  aExistsT Q'},
      {t:'p', h:'The same line with <code>aExists</code> in place of <code>aExistsT</code> compiles in silence.'}
    ]},

    /* ======================================================== two-way entail === */

    {t:'sec', s:'When two assertions say the same thing'},

    {t:'p', h:'Entailment is a preorder and not an order, so the natural way to say that two assertions are interchangeable is not equality. <code>aAnd P Q</code> and <code>aAnd Q P</code> are different terms — they are built from different applications — and each entails the other. That relation deserves a name, and it gets one built out of the relation already in hand.'},

    {t:'code', tag:'verified', cap:'Mutual entailment, and its notation. The body spells <code>Entails</code> out rather than using the turnstile; by the precedence rule above, <code>P ⊢ Q ∧ Q ⊢ P</code> would have been the same term.',
     src:'def AssertionEquiv (P Q : Assertion) : Prop := Entails P Q ∧ Entails Q P\ninfix:40 " ⊣⊢ " => AssertionEquiv'},

    {t:'p', h:'Two other definitions were available. One is the pointwise biconditional, <code>∀ σ h, P σ h ↔ Q σ h</code>, which is equivalent to this one and provable from it in a line. The other is equality of assertions, <code>P = Q</code>. The conjunction is chosen because of what the rest of the course does with it: every equivalence proved after this unit is built by proving two entailments separately and then pairing them, and every use of an equivalence begins by taking <code>.1</code> or <code>.2</code> to get an entailment back. A definition that makes both of those a single character is the one that costs nothing. The pointwise biconditional would demand a conversion at each end; equality would demand an axiom.'},

    {t:'detail', title:'Why not equality?', tag:'aside', open:false, blocks:[
      {t:'p', h:'Two assertions that hold at exactly the same states really are equal, and you can prove it — but only by using function extensionality twice, to get down to a single state, and then propositional extensionality, to turn a biconditional between two propositions into an equation between them. Unit 03 audited the first of those; the second appeared in the same audit under the name <code>propext</code>.'},
      {t:'code', tag:'illustration', cap:'Commutativity of the lifted conjunction, stated as an equation.',
       src:'theorem and_comm_eq (P Q : Assertion) : aAnd P Q = aAnd Q P := by\n  funext σ h\n  exact propext ⟨fun hp => ⟨hp.2, hp.1⟩, fun hp => ⟨hp.2, hp.1⟩⟩'},
      {t:'p', h:'It compiles. What it costs is visible in an axiom audit, run on it and on the <code>⊣⊢</code> version of the same fact — which is exercise <code>x29</code> below.'},
      {t:'state', cap:'Two <code>#print axioms</code> queries.',
       src:'\'and_comm_eq\' depends on axioms: [propext, Quot.sound]\n\'and_comm_iff\' does not depend on any axioms'},
      {t:'p', h:'Nothing in this course is harmed by depending on those two axioms; Unit 03\'s own audit found two of its four theorems already depending on them. What the equation costs is not soundness but work at both ends. Proving one means reaching for <code>funext</code> and <code>propext</code> before you can say anything about a single state, and what you want back out of it is almost always one direction — which the pair hands over as <code>.1</code>.'}
    ]},

    {t:'ex',
     id: 'x28',
     name: 'equiv_refl / equiv_symm / equiv_trans',
     hard: false,
     why: 'Thirteen theorems in the rest of the course conclude in <code>⊣⊢</code>, spread over six units, and they are read and combined as though the symbol denoted an equivalence relation. These three theorems are what makes that reading legitimate. None of them is ever cited by name again — what they buy is the right to treat the symbol the way its shape suggests, which is a right the first edition of this course took without proving. The second of them is also the smallest place where the two halves of an equivalence are seen to run in opposite directions, which is a fact that bites in every later chain.',
     setup: 'Three terms, all built out of theorems you already have. No tactics are needed and none of the three is longer than one line.',
     goal: 'theorem equiv_refl (P : Assertion) : P ⊣⊢ P :=\n  sorry\n\ntheorem equiv_symm {P Q : Assertion} (h : P ⊣⊢ Q) : Q ⊣⊢ P :=\n  sorry\n\ntheorem equiv_trans {P Q R : Assertion} (h₁ : P ⊣⊢ Q) (h₂ : Q ⊣⊢ R) : P ⊣⊢ R :=',
     hints: [
       '<code>P ⊣⊢ Q</code> is <code>Entails P Q ∧ Entails Q P</code> — a conjunction of two entailments, in that order. So a hypothesis of that type has a <code>.1</code> pointing forwards and a <code>.2</code> pointing backwards, and a goal of that type wants a pair.',
       'Reflexivity: both components are the same, and you have proved it already. Symmetry: the two components of the answer are the two components of the hypothesis, swapped. Transitivity: compose forwards for the first component and — the point of the exercise — compose <i>backwards</i> for the second, because the second component of <code>P ⊣⊢ R</code> goes from <code>R</code> to <code>P</code>.',
       'No new tactic and no new lemma: <code>⟨_, _⟩</code>, <code>.1</code>, <code>.2</code>, and the two theorems from <code>m3-2</code>.',
       'The first is <code>⟨entails_refl P, entails_refl P⟩</code>. The third begins <code>⟨entails_trans h₁.1 h₂.1, …⟩</code>, and the second component is the same call with both arguments taken from the other halves and given in the other order.'
     ],
     sol: 'theorem equiv_refl (P : Assertion) : P ⊣⊢ P := ⟨entails_refl P, entails_refl P⟩\n\ntheorem equiv_symm {P Q : Assertion} (h : P ⊣⊢ Q) : Q ⊣⊢ P := ⟨h.2, h.1⟩\n\ntheorem equiv_trans {P Q R : Assertion} (h₁ : P ⊣⊢ Q) (h₂ : Q ⊣⊢ R) : P ⊣⊢ R :=\n  ⟨entails_trans h₁.1 h₂.1, entails_trans h₂.2 h₁.2⟩',
     solNote: 'Look at the subscripts in the last component: <code>h₂</code> before <code>h₁</code>. That is not a typo and not a stylistic choice — it is forced, and the trace below shows what forces it.',
     expl: 'An equivalence is a pair of entailments, so a theorem about equivalences is the corresponding theorem about entailments applied twice. The only place any thought is required is the direction of the second application, which runs from right to left and therefore composes in the opposite order.',
     walk: [
       {tac:'⟨entails_refl P, entails_refl P⟩', h:'Two slots, one for each direction, and reflexivity fills both. The bracket unfolds <code>AssertionEquiv</code> to find out that there are two.'},
       {tac:'⟨h.2, h.1⟩', h:'Symmetry is the swap. <code>h.1 : P ⊢ Q</code> is what the goal wants second; <code>h.2 : Q ⊢ P</code> is what it wants first.'},
       {tac:'entails_trans h₁.1 h₂.1', h:'The forward direction: <code>P ⊢ Q</code> composed with <code>Q ⊢ R</code>, giving <code>P ⊢ R</code>. This is <code>m3-2</code> used exactly as it reads.'},
       {tac:'entails_trans h₂.2 h₁.2', h:'The backward direction. Here the pieces are <code>R ⊢ Q</code> and <code>Q ⊢ P</code>, and composition needs them in that order, so the hypothesis that came second supplies the first argument.'}
     ],
     deep: [
       {t:'trace', title:'Transitivity, with the two goals separated',
        start:'P Q R : Assertion\nh₁ : P ⊣⊢ Q\nh₂ : Q ⊣⊢ R\n⊢ P ⊣⊢ R',
        steps:[
          {tac:'constructor',
           state:'case left\nP Q R : Assertion\nh₁ : P ⊣⊢ Q\nh₂ : Q ⊣⊢ R\n⊢ P ⊢ R',
           h:'The tactic version of the anonymous bracket, and it names the two obligations after <code>And</code>\'s two fields. This one is the forward entailment.'},
          {tac:'· exact entails_trans h₁.1 h₂.1',
           state:'case right\nP Q R : Assertion\nh₁ : P ⊣⊢ Q\nh₂ : Q ⊣⊢ R\n⊢ R ⊢ P',
           h:'The second obligation, printed. <code>R ⊢ P</code>, not <code>P ⊢ R</code> — and that is the whole lesson of the exercise. The composition that produces it starts at <code>R</code>, so it starts from <code>h₂</code>.'},
          {tac:'· exact entails_trans h₂.2 h₁.2',
           state:'',
           h:'<code>h₂.2 : R ⊢ Q</code> then <code>h₁.2 : Q ⊢ P</code>. Read left to right, the subscripts descend, which is exactly what a reversed composition looks like.'}
        ],
        done:'No goals.'}
     ],
     pitfall: 'Writing <code>entails_trans h₁.2 h₂.2</code> for the second component, by copying the first and changing the digit. Both parts are entailments and both are about the right assertions, so it looks right; it is the order that is wrong. The message names the assertion that does not fit: <code>Application type mismatch: The argument h₁.right has type Q ⊢ P but is expected to have type R ⊢ ?m.11 in the application entails_trans h₁.right</code>. Whenever a composition reports a metavariable on the right of the expected type, Lean is telling you it has fixed the starting point from your first argument and cannot get there.',
     variants: 'Weaken <code>equiv_symm</code>\'s hypothesis from <code>⊣⊢</code> to <code>⊢</code> — <code>(h : P ⊢ Q) : Q ⊢ P</code> — and it is false, and false at exactly the point the <code>note</code> above named: <code>⊢</code> is not antisymmetric, so half an equivalence does not give you the other half. Take <code>P</code> to be <code>aFalse</code> and <code>Q</code> to be <code>aTrue</code>. The hypothesis holds, by <code>fun _ _ hp => hp.elim</code>; the conclusion is <code>aTrue ⊢ aFalse</code>, refuted at any state by <code>True.intro</code>. That one witness is why the definition pairs two entailments instead of keeping one. Drop <code>equiv_symm</code> itself and nothing is lost that cannot be recovered on the spot, since <code>⟨h.2, h.1⟩</code> is available wherever <code>h</code> is. Drop <code>equiv_trans</code> and every later chain of equivalences has to be unpacked into four entailments by hand. Reverse the definition of <code>AssertionEquiv</code> to put the backward entailment first and all three theorems still hold, with <code>.1</code> and <code>.2</code> exchanged throughout — which is a good reason to fix the order once, in the definition, and never think about it again.'
    },

    {t:'p', h:'Two properties of the lifted conjunction are wanted as equivalences rather than as entailments, because they are the two the connective of Unit 14 keeps.'},

    {t:'ex',
     id: 'x29',
     name: 'and_comm_iff / and_assoc_iff',
     hard: false,
     why: 'A baseline, and the reason for taking it is two units away. The lifted conjunction is commutative, associative, idempotent and projective. The connective that cuts the heap keeps the first two of those, loses the last two, and the loss is what the whole of Module 3 is about. A reader who has proved all four here can feel exactly which ones go. These two also give the anonymous constructor a real workout: the associativity proof nests brackets three deep in one direction and relies on flattening in the other.',
     setup: 'Two theorems, both terms, both equivalences — so each is a pair whose components are entailments. Nothing beyond <code>⟨…⟩</code>, <code>.1</code> and <code>.2</code> is needed, and no earlier theorem on this page has to be cited.',
     goal: 'theorem and_comm_iff (P Q : Assertion) : aAnd P Q ⊣⊢ aAnd Q P :=\n  sorry\n\ntheorem and_assoc_iff (P Q R : Assertion) : aAnd P (aAnd Q R) ⊣⊢ aAnd (aAnd P Q) R :=',
     hints: [
       'Unfolded at a state, the first says <code>(P σ h ∧ Q σ h) → (Q σ h ∧ P σ h)</code> in both directions, and the second says <code>(P σ h ∧ (Q σ h ∧ R σ h)) → ((P σ h ∧ Q σ h) ∧ R σ h)</code> one way and back the other. Every component is a rearrangement of the same three proofs.',
       'Fix a state, take the conjunction apart into its atoms, and put them back together in the other shape. Nothing is proved; things are moved. Commutativity needs the same rearrangement in both directions, which is why the two components of that pair are the same text twice.',
       'Each component is a lambda of three arguments whose body is an anonymous constructor. To reach an atom inside a nested conjunction, chain the projections: <code>hp.2.1</code> is the first half of the second half.',
       'Commutativity is <code>⟨fun _ _ hp => ⟨hp.2, hp.1⟩, fun _ _ hp => ⟨hp.2, hp.1⟩⟩</code>. For associativity, the left-to-right component is <code>fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩</code>; the other direction needs one bracket fewer, because <code>⟨…⟩</code> flattens to the right.'
     ],
     sol: 'theorem and_comm_iff (P Q : Assertion) : aAnd P Q ⊣⊢ aAnd Q P :=\n  ⟨fun _ _ hp => ⟨hp.2, hp.1⟩, fun _ _ hp => ⟨hp.2, hp.1⟩⟩\n\ntheorem and_assoc_iff (P Q R : Assertion) : aAnd P (aAnd Q R) ⊣⊢ aAnd (aAnd P Q) R :=\n  ⟨fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun _ _ hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩',
     solNote: 'The two components of <code>and_assoc_iff</code> do the same job in opposite directions and look nothing alike, and the difference is entirely about where <code>⟨…⟩</code> flattens. Unit 01 stated the rule; this is the first place it changes what you have to type.',
     expl: 'Each half is a lambda that discards the state and rearranges a proof. In the left-to-right direction of associativity the target is <code>(P ∧ Q) ∧ R</code>, whose first component is itself a pair, so an inner bracket has to be written. In the right-to-left direction the target is <code>P ∧ (Q ∧ R)</code>, and flattening supplies the inner bracket for free.',
     walk: [
       {tac:'⟨fun _ _ hp => ⟨hp.2, hp.1⟩, …⟩', h:'The outer bracket is the pair of entailments; the inner one is the swapped conjunction. Both entailments of the commutativity pair have the same body, because swapping is its own inverse.'},
       {tac:'fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩', h:'Left to right. <code>hp</code> proves <code>P ∧ (Q ∧ R)</code> at this state, so <code>hp.1</code> is the <code>P</code>, <code>hp.2.1</code> the <code>Q</code> and <code>hp.2.2</code> the <code>R</code>. The goal wants <code>(P ∧ Q) ∧ R</code>, whose first slot is a pair, so the first slot is written as one.'},
       {tac:'fun _ _ hp => ⟨hp.1.1, hp.1.2, hp.2⟩', h:'Right to left, and three components for a two-slot goal. That is legal because <code>⟨a, b, c⟩</code> means <code>⟨a, ⟨b, c⟩⟩</code> — flattening reassociates to the right, which is the shape the target has.'}
     ],
     deep: [
       {t:'trace', title:'Associativity, one direction at a time',
        start:'P Q R : Assertion\n⊢ aAnd P (aAnd Q R) ⊣⊢ aAnd (aAnd P Q) R',
        steps:[
          {tac:'constructor',
           state:'case left\nP Q R : Assertion\n⊢ aAnd P (aAnd Q R) ⊢ aAnd (aAnd P Q) R',
           h:'The equivalence splits into its two entailments, and this is the first of them; the other waits behind it and is printed below. Read the goal carefully — the two brackets are in different places on the two sides, and everything else is identical.'},
          {tac:'· intro σ h hp',
           state:'case left\nP Q R : Assertion\nσ : Store\nh : Heap\nhp : aAnd P (aAnd Q R) σ h\n⊢ aAnd (aAnd P Q) R σ h',
           h:'Both hypothesis and goal display folded. Neither unfolds until a projection or a bracket asks, and then both do.'},
          {tac:'exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩',
           state:'case right\nP Q R : Assertion\n⊢ aAnd (aAnd P Q) R ⊢ aAnd P (aAnd Q R)',
           h:'The first branch closes and the second comes forward — an entailment again, with the two sides exchanged, and nothing introduced yet.'},
          {tac:'· intro σ h hp',
           state:'case right\nP Q R : Assertion\nσ : Store\nh : Heap\nhp : aAnd (aAnd P Q) R σ h\n⊢ aAnd P (aAnd Q R) σ h',
           h:'The same three binders as in the other branch. This is where flattening starts to pay: the goal\'s second slot is itself a pair.'},
          {tac:'exact ⟨hp.1.1, hp.1.2, hp.2⟩',
           state:'',
           h:'Three components, two slots. The last two are collected into the pair the second slot wants.'}
        ],
        done:'No goals.'},
       {t:'p', h:'Idempotence is the third property, and it costs nothing here: <code>aAnd P P ⊣⊢ P</code> follows from a projection one way and duplication the other, both of which are on this page already.'},
       {t:'code', tag:'illustration', cap:'The lifted conjunction is idempotent. Two units from now, the separating connective is not — and the counterexample there is two one-cell heaps at the same address, which is the disjointness fact Unit 08 proved.',
        src:'example (P : Assertion) : aAnd P P ⊣⊢ P :=\n  ⟨and_left P P, and_intro (entails_refl P) (entails_refl P)⟩'}
     ],
     pitfall: 'Writing the right-to-left direction of associativity as <code>⟨hp.1, hp.2.1, hp.2.2⟩</code>. The flat triple is the right shape — that direction does want three components in two slots — but the projections have been copied from the other component. Here <code>hp</code> proves <code>(P ∧ Q) ∧ R</code>, so <code>hp.1</code> is itself a pair and <code>hp.2</code> is the whole of <code>R</code>, and Lean complains once for each of the three. First: <code>Application type mismatch: The argument hp.left has type aAnd P Q x✝¹ x✝ but is expected to have type P x✝¹ x✝ in the application And.intro hp.left</code> — flattening never breaks the <i>first</i> field of a bracket apart, so the first component you write must be the whole of the goal\'s first slot, and <code>hp.1</code> is one slot too big. Then, twice over, for <code>hp.2.1</code> and <code>hp.2.2</code>: <code>Invalid projection: Projection operates on types of the form `C ...` where C is a constant. The expression hp.right has type `R x✝¹ x✝` which does not have the necessary form.</code> — <code>hp.2</code> is an atom, and an atom has no first half.',
     variants: 'Give <code>and_comm_iff</code> only one component and it stops being a pair: <code>Insufficient number of fields for `⟨...⟩` constructor: Constructor `And.intro` has 2 explicit field, but only 1 was provided</code>. Weaken either theorem from <code>⊣⊢</code> to <code>⊢</code> and it stays true, halving the work — and the two halvings are not worth the same. For commutativity the discarded component was the same text as the one kept; for associativity it was the other bracketing, and only one of the two can be had by flattening. Replace <code>aAnd</code> by <code>aOr</code> throughout and both theorems remain true, with <code>rcases</code> in place of the projections and <code>Or.inl</code>/<code>Or.inr</code> in place of the pairing — associativity costs a nested <code>rcases</code> in each direction and six branches in all, against one line here. That is the version this course never needs and therefore never states.'
    },

    /* ============================================================ fact ======== */

    {t:'sec', s:'Propositions that are not about memory'},

    {t:'p', h:'One definition is left, and it is the one that will look like it does nothing.'},

    {t:'code', tag:'verified', cap:'An ordinary proposition about the store, presented as an assertion.',
     src:'def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ'},

    {t:'p', h:'The heap binder is an underscore. That is the definition\'s entire content: whatever <code>φ</code> says about the store, <code>fact φ</code> says it and says nothing whatever about memory. It is how a statement such as <i>the variable <code>x</code> holds 10</i> is turned into something the logic can hold, and Unit 13\'s first theorem concludes with one: from two claims that the same address holds two different values it derives, not a contradiction about the heap, but <code>fact (fun _ =&gt; v₁ = v₂)</code> — the two values are equal, and nothing whatever is said about memory.'},

    {t:'code', tag:'illustration', cap:'What <code>fact φ</code> does not claim, checked: its truth at a state does not depend on the heap of that state, and the proof of that is the identity function.',
     src:'example (φ : Store → Prop) (σ : Store) (h h\' : Heap) :\n    fact φ σ h → fact φ σ h\' := fun hp => hp'},

    {t:'p', h:'Two different heaps, and the proof carries a hypothesis about one of them over to the other without touching it. No assertion that says anything about ownership can have a proof of that shape, and the contrast can be run: replace <code>fact φ</code> by Unit 07\'s exact reading and the identity function is rejected, because the two sides are then genuinely different propositions.'},

    {t:'detail', title:'The same statement for an assertion that does depend on the heap', tag:'aside', open:false, blocks:[
      {t:'code', tag:'sketch', cap:'The identity function, offered for the exact reading.',
       src:'example (σ : Store) (h h\' : Heap) : ptsExactly 4 3 σ h → ptsExactly 4 3 σ h\' := fun hp => hp'},
      {t:'state', cap:'The heaps are in the types, so the types differ.',
       src:'error: Type mismatch\n  hp\nhas type\n  ptsExactly 4 3 σ h\nbut is expected to have type\n  ptsExactly 4 3 σ h\''},
      {t:'p', h:'Failing to typecheck is not the same as being false, so here is the refutation, using the four-move idiom Unit 07 set out: assume the statement, choose the two heaps, apply, and collide <code>some</code> against <code>none</code>.'},
      {t:'code', tag:'illustration', cap:'One assertion, two heaps, and no way to carry it from one to the other.',
       src:'example : ¬ (∀ (σ : Store) (h h\' : Heap), ptsExactly 4 3 σ h → ptsExactly 4 3 σ h\') := by\n  intro hall\n  have h := hall (fun _ => 0) (Heap.singleton 4 3) Heap.empty rfl\n  have h4 : Heap.singleton 4 3 4 = Heap.empty 4 := by rw [← h]\n  rw [singleton_same] at h4\n  exact some_ne_none 3 h4'}
    ]},

    {t:'p', h:'There is a second way to embed a proposition, and this unit deliberately does not take it: you could ask that <code>φ</code> hold of the store <i>and</i> that the heap be empty, which turns the embedding into a claim about ownership as well as about truth.'},

    {t:'code', tag:'illustration', cap:'The embedding this unit does not define. It compiles; nothing here uses it.',
     src:'def factExact (φ : Store → Prop) : Assertion := fun σ h => φ σ ∧ h = Heap.empty'},

    {t:'p', h:'That is the assertion Unit 17 defines, though it spells it out of pieces it will have by then rather than as one lambda. It waits until Unit 17 because the whole reason to prefer it is that it behaves well when a heap is being divided, which cannot even be stated until the connective that divides one exists. Until then <code>fact</code> is what there is, and its defect is precisely that it holds of every heap, including heaps its user has no right to.'},

    /* =========================================================== the count ==== */

    {t:'sec', s:'What has been lifted, and what has not'},

    {t:'tbl', cap:'The whole unit in one table. Every row of the middle column is something you had before Module 1 started.',
     head:['At the level of assertions', 'One level down', 'Proved here'],
     rows:[
       ['<code>aTrue</code>', '<code>True</code>', '—'],
       ['<code>aFalse</code>', '<code>False</code>', '—'],
       ['<code>aAnd P Q</code>', '<code>P ∧ Q</code>', '<code>and_left</code>, <code>and_right</code>, <code>and_intro</code>'],
       ['<code>aOr P Q</code>', '<code>P ∨ Q</code>', '<code>or_left</code>, <code>or_right</code>, <code>or_elim</code>'],
       ['<code>aExists P</code>', '<code>∃ x, …</code>', '—'],
       ['<code>P ⊢ Q</code>', '<code>P → Q</code>', '<code>entails_refl</code>, <code>entails_trans</code>'],
       ['<code>P ⊣⊢ Q</code>', '<code>P ↔ Q</code>', '<code>equiv_refl</code>, <code>equiv_symm</code>, <code>equiv_trans</code>'],
       ['<code>fact φ</code>', 'a proposition about <code>σ</code>', '—']
     ]},

    {t:'p', h:'Read the third column against the second. <code>entails_refl</code> is the identity function; <code>entails_trans</code> is Unit 01\'s <code>comp</code>; <code>and_left</code> is <code>And.left</code>; <code>or_elim</code> is <code>Or.elim</code> under a different name and with two arguments in front. Not one of the thirteen theorems on this page has a proof that is anything other than its <code>Prop</code>-level counterpart with a store and a heap threaded through it.'},

    {t:'p', h:'Now count the other way. Module 2 built <code>Heap.union</code>, <code>Heap.disjoint</code> and <code>Heap.splits</code>, the laws relating them, the two bridge lemmas and a partial commutative monoid. Look for any of them in this unit. There are none — and it is stronger than that. Nothing here inspects the heap argument at all: every definition binds it and passes it on, every proof carries it and never reads it, and if <code>Heap</code> were replaced throughout by an arbitrary type, every definition and all thirteen theorems of this unit would compile unchanged.'},

    {t:'dod', h:'You can read and write the type <code>Assertion</code> and say why it has two arguments; prove an entailment by <code>intro σ h hp</code> and explain what <code>intro</code> unfolded to find three binders; give <code>entails_refl</code> and <code>entails_trans</code> as terms and name them as the identity and composition; declare an infix notation with a precedence and predict the parse of a mixed expression; lift the classical connectives pointwise and prove the projection, pairing, injection and case-split laws for them; and state, with the proof, what <code>fact</code> does not claim about the heap.'},

    {t:'p', h:'Every definition here has been a lifting, and every proof the corresponding proof one level down. Nothing about <i>memory</i> has entered the logic. It enters with one definition, and there are two candidates for it — the question Unit 07 posed and did not answer.'}

  ]
});
