registerChapter({
  id: 'terms',
  num: '01',
  phase: 'Phase 0 · Getting started',
  title: 'Propositions are types, proofs are terms',
  blurb: 'What a proof is, in Lean: a term whose type is the statement — and the four connectives built and taken apart in both directions.',

  /* `inductive` occurs only inside a compiler message quoted verbatim — the
     `Note:` line that follows the anonymous-constructor error. Lean's word, not
     the page's; ERRATA §7 exempts diagnostic stems but not the lines under
     them. Trimming it would make the quotation a paraphrase. */
  ledgerAllow: ['inductive'],

  /* x05 says what its shape is spent on, thirteen and fifteen units ahead, and
     says so in as many words. A genuine forward reference, waived by name. */
  ledgerForward: ['star_mono_left', 'star_mono_right'],

  orient: {
    youWill: [
      'Say what a proof <i>is</i> in Lean, and why a hypothesis can be written in the same list as an argument.',
      'Write <code>fun h =&gt; …</code> proofs of implications and compositions, and read <code>P → Q → R</code> correctly.',
      'Prove an <code>∃</code> by giving a witness and a proof, and use one by taking it apart.',
      'Build an <code>∧</code> with <code>⟨…⟩</code> and read it with <code>.1</code> and <code>.2</code>; say why <code>∨</code> admits neither.',
      'Write the same proof twice — once as a term, once with tactics — and say what each buys.',
      'Predict which arguments of a theorem you must supply and which Lean will work out, and override it with <code>@</code>.',
      'Pack and unpack a six-component nest with one flat pair of brackets.'
    ],
    needs: [
      'Unit 00: a <code>theorem</code> header and its four parts; the goal display; <code>intro</code> and <code>simp</code>.',
      '<code>∧ ∨ ¬ → ↔ ∀ ∃</code> as ordinary mathematical notation. Nothing about type theory.'
    ],
    payoff: 'Every assertion in this course is a predicate, every entailment between assertions is a function, and about a fifth of the theorems ahead have no tactic block in them at all — they are the terms you learn to write here.'
  },

  blocks: [

    /* ------------------------------------------------- what a proof is --- */

    {t:'p', h:'Unit 00 ended with a theorem whose binder list contained something odd. <code>lookup_of_unallocated (x : Loc) (hx : x ≠ 4)</code> takes two arguments. The first is an address, which you supply. The second is a <i>hypothesis</i> — and it is written in the same list, in the same brackets, differing from the address only in what follows its colon. That is not a notational convenience. In Lean a hypothesis and an argument are the same kind of thing, because a statement is a type and a proof of it is a value of that type.'},

    {t:'defn', term:'Propositions as types',
     h:'A statement — <code>x ≠ 4</code>, <code>2 + 2 = 4</code>, <code>P ∧ Q</code> — is a <i>type</i>, and its type is <code>Prop</code>. A proof of that statement is a <i>term</i> of that type. “<code>hx</code> proves <code>x ≠ 4</code>” and “<code>hx</code> has type <code>x ≠ 4</code>” are the same sentence. Proving is therefore construction: to prove a statement you build an inhabitant of it, and the checker that accepts your proof is the same one that rejects <code>(5 : Option Val)</code>.',
     cap:'This is the whole of Lean\'s answer, and every construction in this unit is a consequence of it.'},

    /* ------------------------------------------- implication = function --- */

    {t:'h3', s:'Implication is a function type'},

    {t:'p', h:'Take the smallest interesting statement: from <code>P</code>, and from <code>P → Q</code>, conclude <code>Q</code>. Under the reading above, <code>P → Q</code> is not a new kind of thing at all — it is the type of functions from <code>P</code> to <code>Q</code>, the same arrow that built <code>Loc → Option Val</code> in Unit 00. A proof of <code>P → Q</code> is a procedure turning any proof of <code>P</code> into a proof of <code>Q</code>. So the proof below is a function, written the way every function in Lean is written.'},

    {t:'anat', tag:'verified',
     src:'theorem implication_example (P Q : Prop) :\n    P → (P → Q) → Q :=\n  fun hp hpq => hpq hp',
     parts:[
       {m:'(P Q : Prop)', h:'Two arguments, both types — <code>Prop</code> is the type of statements, so <code>P</code> and <code>Q</code> range over statements. Nothing is assumed about them: this theorem holds whatever they say, which is what makes it a rule of logic rather than a fact about memory.'},
       {m:'P → (P → Q) → Q', h:'The statement, and the brackets in it are not decoration. <code>→</code> associates to the right, so the unbracketed <code>P → P → Q → Q</code> would read <code>P → (P → (Q → Q))</code> — a different and much duller claim. What is written here is <code>P → ((P → Q) → Q)</code>: given a proof of <code>P</code>, a function from proofs of <code>P → Q</code> to proofs of <code>Q</code>.'},
       {m:':=', h:'No <code>by</code>. Unit 00\'s proofs were all <code>:= by …</code>, which hands the goal to tactics; <code>:=</code> on its own means the proof is written out directly, as a term. Both end in the same place — a tactic block\'s only job is to build a term like this one — and the term is what the kernel actually checks.'},
       {m:'fun hp hpq =>', h:'Two abstractions in one <code>fun</code>: <code>fun hp hpq => e</code> abbreviates <code>fun hp => fun hpq => e</code>, matching the right-associativity of the arrow. <code>hp</code> names a proof of <code>P</code> and <code>hpq</code> names a proof of <code>P → Q</code>. On paper you would open with “assume <code>P</code>, and assume <code>P → Q</code>”; the two are the same move.'},
       {m:'hpq hp', h:'Application. <code>hpq</code> is a function from proofs of <code>P</code> to proofs of <code>Q</code>, <code>hp</code> is a proof of <code>P</code>, so <code>hpq hp</code> is a proof of <code>Q</code> — which is what the goal wanted. Modus ponens is not a rule that has to be added to this system. It is function application, and it was already there.'}
     ]},

    {t:'code', tag:'illustration',
     cap:'A theorem, once proved, is a term with a name, so using a theorem is applying it. The corpus records the same statement a second time under the name it deserves; <code>#check</code> asks for its type, and the <code>example</code> calls it.',
     src:'#check mp\n\nexample (P Q : Prop) (hp : P) (hpq : P → Q) : Q := mp P Q hp hpq'},

    {t:'state', cap:'The reply to <code>#check mp</code>. The <code>example</code> printed nothing, which is success.',
     src:'mp (P Q : Prop) : P → (P → Q) → Q'},

    {t:'p', h:'Four arguments were supplied to a theorem whose statement mentions two hypotheses, because <code>P</code> and <code>Q</code> are arguments too — the binder list does not distinguish them. Leave them out, write <code>mp hp hpq</code>, and Lean does not silently recover; it takes <code>hp</code> as the argument for <code>P</code> and complains about its type.'},

    {t:'state', cap:'The reply to <code>mp hp hpq</code>. Read the last two lines first: a proof was offered where a statement was wanted.',
     src:'error: Application type mismatch: The argument\n  hp\nhas type\n  P\nof sort `Prop` but is expected to have type\n  Prop\nof sort `Type` in the application\n  mp hp'},

    {t:'p', h:'Writing <code>P</code> and <code>Q</code> out at every use is noise, and it is avoidable noise, because Lean can read them off the types of the later arguments: if <code>hp</code> has type <code>P</code> then the first argument was <code>P</code> and there was never a choice. A binder written in braces asks Lean to do exactly that. The alternative — leave every binder explicit — is what the corpus does for <code>mp</code>, and it costs two tokens at every call site for information nobody has to think about. The cost of braces is the opposite one: an argument Lean cannot see anywhere in the later types is one you can no longer supply, and then you need <code>@</code>, which switches every implicit binder back to explicit for one use.'},

    {t:'code', tag:'illustration',
     src:'#check exists_mono\n#check @exists_mono'},

    {t:'state', cap:'The same theorem twice. Braces in the first display are Lean saying “I will work these out”; <code>@</code> in the second says “I will not”.',
     src:'exists_mono {P Q : Nat → Prop} (h : ∀ (n : Nat), P n → Q n) : (∃ n, P n) → ∃ n, Q n\n@exists_mono : ∀ {P Q : Nat → Prop}, (∀ (n : Nat), P n → Q n) → (∃ n, P n) → ∃ n, Q n'},

    {t:'p', h:'The second display also answers a question the first raises. Under <code>@</code> the binders are gone and <code>∀</code> has appeared in their place, twice, with no change of meaning — because <code>∀ (x : T), B</code> <i>is</i> the function type from <code>T</code> to <code>B</code>, in the case where <code>B</code> is allowed to mention <code>x</code>. That is the only difference between <code>∀</code> and <code>→</code>: the arrow is the special case where the conclusion does not depend on the argument. So a binder list, a <code>∀</code>, and a chain of arrows are three spellings of one thing, and <code>h : ∀ (n : Nat), P n → Q n</code> above is used the way any function is used — <code>h n hn</code>, a number and then a proof.'},

    {t:'ex',
     id:'x03',
     name:'comp',
     why:'Composition is the shape of every chain of entailments in this course. Unit 12 defines <code>P ⊢ Q</code> so that a proof of it is a function, and every chain of three assertions you meet after that is this exercise with heaps written into it. Getting it as a term now means the chains later are reading, not translation.',
     setup:'Term mode: your answer starts <code>:=</code>, not <code>:= by</code>. <code>f</code> and <code>g</code> are hypotheses, so they are functions you may apply.',
     goal:'theorem comp (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R :=',
     hints:[
       'The goal is <code>P → R</code>, which is a function type. Above it sit <code>f</code>, a function from <code>P</code> to <code>Q</code>, and <code>g</code>, a function from <code>Q</code> to <code>R</code>. Nothing here is about logic that is not also about functions.',
       'You are being asked for a function from <code>P</code> to <code>R</code> out of a function from <code>P</code> to <code>Q</code> and one from <code>Q</code> to <code>R</code>. There is one such function. Say what it does to an arbitrary argument.',
       'Open with <code>fun</code>, binding one name for the proof of <code>P</code>. The body is an application of an application: no tactic, no bracket notation, nothing but the two hypotheses and the name you bound.',
       'Write <code>fun hp =&gt;</code> and the body must have type <code>R</code>. Only <code>g</code> produces an <code>R</code>, so the body is <code>g _</code>, and the hole must have type <code>Q</code>. Only <code>f</code> produces a <code>Q</code>, and it wants a <code>P</code>, which is <code>hp</code>.'
     ],
     sol:'theorem comp (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := fun hp => g (f hp)',
     solNote:'The order is forced by the types and by nothing else, which is the point: once the statement is written, there is no strategy left to choose.',
     expl:'Read the term from the outside in and it is the proof you would write on paper, with the words removed. “Assume <code>P</code>” is <code>fun hp =&gt;</code>. “By <code>f</code> we have <code>Q</code>” is <code>f hp</code>. “By <code>g</code> we have <code>R</code>” is <code>g</code> applied to that.',
     walk:[
       {tac:'fun hp =>', h:'Turns the obligation <code>P → R</code> into the obligation <code>R</code>, with a name <code>hp</code> for a proof of <code>P</code> available in the body. The arrow in the goal and the <code>fun</code> in the proof are the same arrow.'},
       {tac:'f hp', h:'Applies the hypothesis <code>f : P → Q</code> to <code>hp : P</code>. The result has type <code>Q</code>. This is the only step where <code>hp</code> can be used, because nothing else takes a <code>P</code>.'},
       {tac:'g (f hp)', h:'Applies <code>g : Q → R</code> to that. The result has type <code>R</code>, which is what the body was required to produce, so the term is complete. The brackets are needed: <code>g f hp</code> would apply <code>g</code> to <code>f</code>, and <code>f</code> is not a proof of <code>Q</code>.'}
     ],
     deep:[
       {t:'cmp',
        left:{t:'As a term', kind:'good', tag:'sketch', h:'One line. The proof is the function, and the types leave no choice about which function it is.',
              src:'fun hp => g (f hp)'},
        right:{t:'With tactics', tag:'sketch', h:'Two lines doing the same two things: <code>intro</code> performs the <code>fun</code>, and <code>exact</code> supplies the body. Nothing is gained here, and one line is spent saying that a function is being built.',
               src:'by\n  intro hp\n  exact g (f hp)'}},
       {t:'trace', title:'The tactic version, so you can see the state the lambda passes through',
        start:'P Q R : Prop\nf : P → Q\ng : Q → R\n⊢ P → R',
        steps:[
          {tac:'intro hp',
           state:'P Q R : Prop\nf : P → Q\ng : Q → R\nhp : P\n⊢ R',
           h:'The antecedent moved above the line and the goal became the consequent. That is precisely what <code>fun hp =&gt;</code> does; the term version never displays this state, which is why it is worth printing once.'},
          {tac:'exact g (f hp)', state:'No goals.',
           h:'<code>exact e</code> closes the goal with the term <code>e</code>, provided <code>e</code> has the goal\'s type. It is the bridge between the two styles, and it is how a tactic proof ends whenever the remaining goal is small enough to write out.'}
        ]}
     ],
     pitfall:'Composing the wrong way round — <code>fun hp =&gt; f (g hp)</code>. It reads plausibly if you are thinking of <code>f</code> and <code>g</code> as “first” and “second”, and Lean rejects it at <code>g hp</code>, not at the end, saying that the argument <code>hp</code> has type <code>P</code> but is expected to have type <code>Q</code>. The message names the innermost application because that is where the types first disagree, so read an application-type-mismatch from the bottom line up — Lean tells you which application it was before it tells you anything else.',
     variants:'Drop <code>g</code> and the statement becomes <code>P → R</code> with nothing producing an <code>R</code>; it is unprovable, and it is unprovable for a reason you can state — <code>R</code> is an arbitrary <code>Prop</code>, so a proof of it would prove everything. Reverse <code>g</code> to <code>g : R → Q</code> and the same thing happens, which is the useful case to sit with: the hypothesis is present, it is even about <code>R</code>, and it is still useless, because a function into <code>R</code> is what you need and a function out of <code>R</code> is what you have. Replace <code>Q</code> by <code>P</code> throughout and the theorem is still true and the proof unchanged; nothing in it ever looked at what the three statements said.'
    },

    /* --------------------------------------------- existentials and pairs --- */

    {t:'h3', s:'∃, ∧, and one pair of brackets'},

    {t:'p', h:'An existential is not a function type, and the difference is worth being exact about. To prove <code>∀ n, P n</code> you must handle every <code>n</code>, so a proof is something that takes an <code>n</code> — a function. To prove <code>∃ n, P n</code> you must produce one <code>n</code> and a reason, so a proof is a <i>pair</i>: the witness, and a proof about it. Both components are in the term, which is why an existential proof in Lean can be inspected for its witness, and why the second component\'s type mentions the first.'},

    {t:'code', tag:'verified', cap:'Two existentials over <code>Nat</code> — the witness is on the left of the comma, the proof that it works is on the right — and one equation with no existential over it at all.',
     src:'theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩\n\ntheorem exists_three : ∃ n : Nat, n + 1 = 4 := ⟨3, rfl⟩\n\ntheorem two_add_two : 2 + 2 = 4 := rfl'},

    {t:'p', h:'The brackets are Lean\'s <b>anonymous constructor</b>, and they are anonymous in a precise sense: <code>⟨…⟩</code> means <i>build the expected type from these pieces</i>, and it is legal exactly when the expected type has one way of being built. <code>∃</code> has one, taking a witness and a proof. <code>∧</code> has one, taking a proof of each side. So the same brackets serve both, and the same brackets you met in Unit 00 as an <code>intro</code> pattern serve for taking them apart. The right-hand components here are <code>rfl</code>, a term proving any equation whose two sides are the same after computation — <code>3 = 3</code> in the first, and <code>3 + 1 = 4</code> in the second, which needs Lean to add before it can agree. <code>two_add_two</code> is the same term with no existential wrapped round it, and it is doing the same work.'},

    {t:'code', tag:'verified', cap:'Conjunction, both directions in one line: <code>h.1</code> and <code>h.2</code> take a pair apart, <code>⟨…⟩</code> puts one together.',
     src:'theorem and_comm\' (P Q : Prop) : P ∧ Q → Q ∧ P := fun h => ⟨h.2, h.1⟩'},

    {t:'ex',
     id:'x04',
     name:'and_comm\'',
     why:'This is the first term you write that both destructures and constructs, and the pattern is permanent: from Unit 14 onwards a proof about <code>P ∗ Q</code> arrives as a nest to be taken apart and leaves as a nest to be built, and the only thing that changes is how many components there are. It also fixes what <code>.1</code> and <code>.2</code> mean before there is anything complicated to point them at.',
     setup:'Term mode. <code>h</code> is a proof of <code>P ∧ Q</code>; <code>h.1</code> and <code>h.2</code> are its two components, in that order.',
     goal:'theorem and_comm\' (P Q : Prop) : P ∧ Q → Q ∧ P :=',
     hints:[
       'The goal is a function type: given a proof of <code>P ∧ Q</code>, produce a proof of <code>Q ∧ P</code>. So it begins the way <code>comp</code> began, with <code>fun</code> binding one name.',
       'A proof of a conjunction contains a proof of each side, and a proof of a conjunction is built from a proof of each side. Both sides are already available once you have taken the hypothesis apart; the only content of the exercise is the order they go back in.',
       '<code>.1</code> and <code>.2</code> read the two components off a conjunction. <code>⟨…⟩</code> builds one from two pieces. You need both, in one expression.',
       'Write <code>fun h =&gt;</code>; the body must have type <code>Q ∧ P</code>, so it is <code>⟨_, _⟩</code> with a proof of <code>Q</code> first. <code>h.2</code> is the proof of <code>Q</code>, since <code>h</code> proves <code>P ∧ Q</code> and <code>Q</code> is its second component.'
     ],
     sol:'theorem and_comm\' (P Q : Prop) : P ∧ Q → Q ∧ P := fun h => ⟨h.2, h.1⟩',
     solNote:'Swapping is the whole of it: the components come out in one order and go back in the other.',
     expl:'Two brackets, doing opposite jobs. <code>.1</code> and <code>.2</code> are projections out of the incoming pair; <code>⟨…⟩</code> is construction into the outgoing one. Nothing is proved in between, because a conjunction holds no information beyond its two components.',
     walk:[
       {tac:'fun h =>', h:'Turns the goal <code>P ∧ Q → Q ∧ P</code> into <code>Q ∧ P</code>, with <code>h : P ∧ Q</code> available. Same move as <code>comp</code>: the arrow in the statement becomes a binder in the term.'},
       {tac:'⟨h.2, h.1⟩', h:'Builds a proof of <code>Q ∧ P</code>. The expected type has one constructor, taking a proof of <code>Q</code> then a proof of <code>P</code>, so the first slot must hold <code>h.2</code> — the <code>Q</code> half of <code>h</code> — and the second <code>h.1</code>. Writing them the other way round is not a stylistic error; it is a type error, and Lean reports it as one.'}
     ],
     deep:[
       {t:'cmp',
        left:{t:'As a term', kind:'good', tag:'sketch', h:'The projections happen where they are used. One line, and the reader sees the two components change places.',
              src:'fun h => ⟨h.2, h.1⟩'},
        right:{t:'With tactics', tag:'sketch', h:'Three lines. <code>obtain</code> splits <code>h</code> into two named hypotheses up front instead of projecting twice. This version is on the page below, and it is the one to prefer when there are six components rather than two.',
               src:'by\n  intro h\n  obtain ⟨hp, hq⟩ := h\n  exact ⟨hq, hp⟩'}},
       {t:'trace', title:'The tactic version, tactic by tactic',
        start:'P Q : Prop\n⊢ P ∧ Q → Q ∧ P',
        steps:[
          {tac:'intro h', state:'P Q : Prop\nh : P ∧ Q\n⊢ Q ∧ P',
           h:'The antecedent is now a hypothesis, whole.'},
          {tac:'obtain ⟨hp, hq⟩ := h', state:'P Q : Prop\nhp : P\nhq : Q\n⊢ Q ∧ P',
           h:'<code>obtain</code> takes a hypothesis apart along its constructor and replaces it with its components. <code>h</code> is gone from the context: it has been consumed, and the two halves stand in its place under the names you chose.'},
          {tac:'exact ⟨hq, hp⟩', state:'No goals.',
           h:'The same bracket as in the term proof, closing the same goal.'}
        ]}
     ],
     pitfall:'Writing <code>⟨h.1, h.2⟩</code>, which is the identity and looks right because the components are in the order you read them off. Lean answers that the argument <code>h.left</code> has type <code>P</code> but is expected to have type <code>Q</code> — and it says <code>h.left</code>, not <code>h.1</code>: the numeric projections are shorthand for the constructor\'s field names, and error messages use the names. <code>And</code>\'s fields are <code>left</code> and <code>right</code>, which is also where the daggered <code>right✝</code> in Unit 00 came from.',
     variants:'Replace <code>∧</code> by <code>∨</code> throughout and the statement is still true, and this proof fails at the first character of the body — that is the next section, and it is the sharpest single difference between the two connectives. Weaken the goal to <code>P ∧ Q → Q</code> and the proof shrinks to <code>fun h =&gt; h.2</code>, which is the case to hold on to, because the corresponding statement about <code>∗</code> is <b>false</b> and is refuted in Unit 14: you cannot forget half of a resource the way you can forget half of a conjunction.'
    },

    /* -------------------------------------------------------- disjunction --- */

    {t:'h3', s:'Disjunction cannot be projected'},

    {t:'code', tag:'sketch', cap:'The same proof with <code>∨</code> in place of <code>∧</code> is the obvious thing to try, and it fails before any question of order arises.',
     src:'theorem or_comm_bad (P Q : Prop) : P ∨ Q → Q ∨ P := fun h => ⟨h.2, h.1⟩'},

    {t:'state', cap:'The reply. The second line is the rule the anonymous constructor lives by, stated by Lean.',
     src:'error: Invalid `⟨...⟩` notation: The expected type `Q ∨ P` has more than one constructor\n\nNote: This notation can only be used when the expected type is an inductive type with a single constructor'},

    {t:'p', h:'A disjunction can be built two ways, so <code>⟨…⟩</code> cannot know which you meant: the two ways are <code>Or.inl</code>, which builds <code>a ∨ b</code> from a proof of <code>a</code>, and <code>Or.inr</code>, which builds it from a proof of <code>b</code>. The asymmetry runs the other way too. A proof of <code>P ∧ Q</code> contains a proof of <code>P</code>, so it can be projected; a proof of <code>P ∨ Q</code> contains a proof of one side and does not say in advance which, so there is nothing to project and the only way to use it is to handle both cases. That is what <code>Or.elim</code> does — give it a proof of <code>a ∨ b</code> and two functions, one from <code>a</code> and one from <code>b</code>, both landing in the same place, and it delivers that place.'},

    {t:'code', tag:'verified', cap:'Commuting a disjunction: in the left case produce the right disjunct, and vice versa.',
     src:'theorem or_comm\' (P Q : Prop) : P ∨ Q → Q ∨ P :=\n  fun h => h.elim Or.inr Or.inl'},

    {t:'p', h:'<code>h.elim</code> is <code>Or.elim h</code>, and the abbreviation is worth pausing on because you will read it constantly. Writing <code>h.foo</code> makes Lean look at the <i>type</i> of <code>h</code>, take its head constant, and try the name formed by putting a dot between them — <code>h</code> has type <code>P ∨ Q</code>, whose head is <code>Or</code>, so <code>h.elim</code> means <code>Or.elim h</code>, with <code>h</code> slotted into the first argument that fits. The same three characters therefore denote different theorems after different hypotheses: <code>h.symm</code> is <code>Or.symm h</code> when <code>h</code> proves a disjunction and <code>Eq.symm h</code> when it proves an equation. Nothing about the notation says which, and that is deliberate — dot notation is how a proof about heaps stays readable once its type is four lines long.'},

    {t:'detail', title:'<code>.symm</code>, twice, on two different types', tag:'aside', open:false,
     blocks:[
       {t:'code', tag:'illustration',
        src:'example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := h.symm\nexample (a b : Nat) (h : a = b) : b = a := h.symm\nexample (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := h1.trans h2\n\n#check @Or.symm'},
       {t:'state', src:'@Or.symm : ∀ {a b : Prop}, a ∨ b → b ∨ a'},
       {t:'p', h:'Three lines, three different underlying theorems, one syntax. The braces in <code>@Or.symm</code>\'s type say that <code>a</code> and <code>b</code> are found from the hypothesis, which is why <code>h.symm</code> takes no further arguments. <code>h1.trans h2</code> is <code>Eq.trans h1 h2</code> by the same rule, and it is how two equations are chained until there is a notation for longer ones.'}
     ]},

    /* ------------------------------------------------------- tactic mode --- */

    {t:'h3', s:'The same proofs, driven by tactics'},

    {t:'p', h:'A term proof is complete at every moment, so nothing ever displays a goal, and for a proof of any size that is intolerable: you cannot see what is left. A tactic block builds the same term, from the outside in, showing you the hole at each step. The two corpus proofs below are the two theorems above, rewritten in that style — not because they need it, but because they are small enough that you can check the translation yourself.'},

    {t:'code', tag:'verified',
     src:'theorem and_comm_tac (P Q : Prop) : P ∧ Q → Q ∧ P := by\n  intro h\n  obtain ⟨hp, hq⟩ := h\n  exact ⟨hq, hp⟩'},

    {t:'trace', title:'and_comm_tac, tactic by tactic',
     start:'P Q : Prop\n⊢ P ∧ Q → Q ∧ P',
     steps:[
       {tac:'intro h', state:'P Q : Prop\nh : P ∧ Q\n⊢ Q ∧ P',
        h:'<code>intro</code> is the tactic form of <code>fun</code>. Same effect, visible.'},
       {tac:'obtain ⟨hp, hq⟩ := h', state:'P Q : Prop\nhp : P\nhq : Q\n⊢ Q ∧ P',
        h:'Splits <code>h</code> into its components and removes it. Where the term proof wrote <code>h.1</code> and <code>h.2</code> at the point of use, this names both once, up front. With two components the choice is cosmetic; with six it is not.'},
       {tac:'exact ⟨hq, hp⟩', state:'No goals.',
        h:'Supplies the finished term for what is left. Every tactic proof ends this way or with a tactic that does it for you.'}
     ]},

    {t:'code', tag:'verified',
     src:'theorem or_comm_tac (P Q : Prop) : P ∨ Q → Q ∨ P := by\n  intro h\n  rcases h with hp | hq\n  · right; exact hp\n  · left;  exact hq'},

    {t:'p', h:'Three pieces of syntax arrive at once here. <code>rcases h with hp | hq</code> is case analysis on a disjunction: the bar separates the patterns for the two constructors, and it leaves <b>two goals</b>, each with its own hypothesis and its own case label. <code>·</code> focuses the first remaining goal, so that the tactics indented under it can only see that one; without the dots the branches would run together and a mistake in the first would surface in the second. And <code>;</code> puts two tactics on one line, which is worth exactly as much as it saves — here it keeps each branch to a single line, and nothing else. <code>left</code> and <code>right</code> are the tactic forms of <code>Or.inl</code> and <code>Or.inr</code>: they choose which disjunct of the <i>goal</i> you undertake to prove.'},

    {t:'trace', title:'or_comm_tac, and the moment there are two goals',
     start:'P Q : Prop\nh : P ∨ Q\n⊢ Q ∨ P',
     steps:[
       {tac:'rcases h with hp | hq',
        state:'case inl\nP Q : Prop\nhp : P\n⊢ Q ∨ P\n\ncase inr\nP Q : Prop\nhq : Q\n⊢ Q ∨ P',
        h:'Two goals, separated by a blank line, labelled with the constructor each came from. The goal has not changed; what changed is that there are now two contexts, and neither of them holds a disjunction any more.'},
       {tac:'· right', state:'case inl\nP Q : Prop\nhp : P\n⊢ P',
        h:'Inside the first branch. <code>right</code> commits to the second disjunct of <code>Q ∨ P</code>, which is <code>P</code> — and that is the one the branch can prove, because the branch is the case where <code>P</code> holds. Choosing <code>left</code> here would leave <code>⊢ Q</code> with nothing to prove it from.'},
       {tac:'exact hp', state:'case inr\nP Q : Prop\nhq : Q\n⊢ Q ∨ P',
        h:'The first branch closes and the display moves to what was waiting behind it. The second branch is the mirror image: <code>left</code>, then <code>exact hq</code>.'}
     ]},

    {t:'detail', title:'Splitting a goal instead of a hypothesis: <code>constructor</code>, and what <code>↔</code> is', tag:'aside', open:false,
     blocks:[
       {t:'p', h:'<code>obtain</code> takes a hypothesis apart. <code>constructor</code> does the same to a <i>goal</i>: it applies the single constructor of the goal\'s type and leaves one new goal per field.'},
       {t:'code', tag:'illustration',
        src:'theorem and_comm_ctor (P Q : Prop) : P ∧ Q → Q ∧ P := by\n  intro h\n  constructor\n  · exact h.2\n  · exact h.1'},
       {t:'state', cap:'After <code>constructor</code>. The labels are the field names of <code>And</code> — which is what <code>.1</code> and <code>.2</code> are numbering.',
        src:'case left\nP Q : Prop\nh : P ∧ Q\n⊢ Q\n\ncase right\nP Q : Prop\nh : P ∧ Q\n⊢ P'},
       {t:'p', h:'<code>↔</code> is the same story with different field names. <code>P ↔ Q</code> is a structure called <code>Iff</code> with two fields, a proof of <code>P → Q</code> and a proof of <code>Q → P</code>, and they are named <code>mp</code> and <code>mpr</code>. So <code>constructor</code> on an <code>↔</code> goal leaves <code>case mp</code> and <code>case mpr</code>; and given <code>hiff : P ↔ Q</code>, <code>hiff.mp</code> is the forward function and <code>hiff.mpr</code> the backward one, by the dot-notation rule above. <code>Iff.intro</code> builds one from the two directions, and so does <code>⟨…⟩</code>, since there is only one constructor.'},
       {t:'code', tag:'illustration',
        src:'theorem iff_and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by\n  constructor\n  · exact and_comm\' P Q\n  · exact and_comm\' Q P\n\nexample (P Q : Prop) (h : P ∧ Q) : Q ∧ P := (iff_and_comm P Q).mp h\n\ntheorem iff_and_comm\' (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=\n  Iff.intro (and_comm\' P Q) (and_comm\' Q P)'}
     ]},

    {t:'ex',
     id:'x05',
     name:'exists_mono',
     why:'Witness in, witness out. This is the exact shape of every monotonicity proof in the second half of the course: <code>star_mono_left</code>, <code>star_mono_right</code> and the <code>∃</code> case of the frame rule are all this proof with heaps as the witnesses and a splitting condition carried along untouched. Doing it here, where the witness is a number and nothing is carried, means that later you are only ever adding components.',
     setup:'Tactic mode. <code>P</code> and <code>Q</code> are predicates on <code>Nat</code>, and <code>h</code> converts a proof of <code>P n</code> into a proof of <code>Q n</code> for any <code>n</code> you hand it — it is a function of two arguments, the number first.',
     goal:'theorem exists_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) :\n    (∃ n, P n) → ∃ n, Q n := by',
     hints:[
       'The goal is an implication whose antecedent is an existential and whose consequent is an existential. Above it, <code>h</code> — a proof of a <code>∀</code>, so a function taking a number and a proof.',
       'You are given that some number satisfies <code>P</code> and must show some number satisfies <code>Q</code>. The same number works: there is no search here, and no choice about the witness. The whole content is that you must first get hold of it.',
       'Three tactics, all of them already on the page: one to assume the antecedent, one to take an existential hypothesis apart into a witness and a proof, and one to supply the finished pair.',
       'Write <code>intro hp</code>, leaving <code>hp : ∃ n, P n</code> and the goal <code>∃ n, Q n</code>. Then <code>obtain ⟨n, hn⟩ := hp</code> replaces <code>hp</code> by a number <code>n</code> and a proof <code>hn : P n</code>. The last line is one bracket, whose second component applies <code>h</code> to two things.'
     ],
     sol:'theorem exists_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) :\n    (∃ n, P n) → ∃ n, Q n := by\n  intro hp\n  obtain ⟨n, hn⟩ := hp\n  exact ⟨n, h n hn⟩',
     solNote:'The binders on <code>P</code> and <code>Q</code> are implicit, so at every use of this theorem you supply only <code>h</code> and the existential — Lean reads the predicates off them.',
     expl:'An existential hypothesis is a pair, so it can be opened; an existential goal is a pair, so it must be built. Between the two, <code>h</code> converts the proof component and the witness component travels unchanged. That the witness is unchanged is the reason the proof is three lines instead of a search.',
     walk:[
       {tac:'intro hp', h:'Moves the antecedent <code>∃ n, P n</code> into the context under the name <code>hp</code> and leaves <code>∃ n, Q n</code> as the goal. The existential is still packaged at this point; nothing can be done with it.'},
       {tac:'obtain ⟨n, hn⟩ := hp', h:'Opens the package. <code>n : Nat</code> is the witness and <code>hn : P n</code> is the proof about it, and <code>hn</code>\'s type mentions <code>n</code> — that dependency is what makes an existential a different thing from a conjunction. <code>hp</code> leaves the context.'},
       {tac:'exact ⟨n, h n hn⟩', h:'Builds the goal\'s pair. The witness slot takes the same <code>n</code>. The proof slot needs <code>Q n</code>, and <code>h n</code> is a function from <code>P n</code> to <code>Q n</code>, so applying it to <code>hn</code> produces exactly that. Two applications, because <code>h</code> is a <code>∀</code> and the number is its first argument.'}
     ],
     deep:[
       {t:'trace', title:'exists_mono, tactic by tactic',
        start:'P Q : Nat → Prop\nh : ∀ (n : Nat), P n → Q n\n⊢ (∃ n, P n) → ∃ n, Q n',
        steps:[
          {tac:'intro hp', state:'P Q : Nat → Prop\nh : ∀ (n : Nat), P n → Q n\nhp : ∃ n, P n\n⊢ ∃ n, Q n',
           h:'The antecedent is now a hypothesis. It is opaque: nothing in it is usable while it is still a single existential.'},
          {tac:'obtain ⟨n, hn⟩ := hp', state:'P Q : Nat → Prop\nh : ∀ (n : Nat), P n → Q n\nn : Nat\nhn : P n\n⊢ ∃ n, Q n',
           h:'Two new hypotheses replace one. The <code>n</code> bound in the goal and the <code>n</code> now in the context are different variables that happen to print the same; the goal still quantifies over its own.'},
          {tac:'exact ⟨n, h n hn⟩', state:'No goals.',
           h:'The context <code>n</code> is offered as the goal\'s witness, which is the only step where the two <code>n</code>s meet.'}
        ]},
       {t:'p', h:'Nothing above used that the witnesses are numbers. Replace <code>Nat</code> by heaps and <code>P</code>, <code>Q</code> by assertions and the identical three lines prove that <code>∃</code> is monotone in the logic of Unit 12 — which is why this is a construction exercise and not a drill.'}
     ],
     pitfall:'Trying <code>hp.1</code> and <code>hp.2</code>, by analogy with conjunction. It fails with <code>Invalid projection: Cannot project a value of non-propositional type Nat from the expression hp which has propositional type ∃ n, P n</code>. The reason is the dependency named in the walk: the second component\'s type mentions the first, so a projection would have to hand you a <code>Nat</code> extracted from a proof, and a proof is not allowed to leak data into the rest of the mathematics. <code>obtain</code> is not a convenience over projection here — it is the only way in.',
     variants:'Forget the <code>h</code> and write <code>exact ⟨n, hn⟩</code>: Lean answers that the argument <code>hn</code> has type <code>P n</code> but is expected to have type <code>Q n</code>, which is a precise statement of the one thing the proof has to do. Reverse the hypothesis to <code>h : ∀ n, Q n → P n</code> and the theorem is false — take <code>P</code> always true and <code>Q</code> always false, and the hypothesis holds vacuously while the conclusion fails at every witness. Change the goal to <code>(∀ n, P n) → ∀ n, Q n</code> and the analogous three lines work, with <code>intro n</code> in place of <code>obtain</code>; that is the direction in which <code>∀</code> and <code>∃</code> agree, and Unit 15 is where they stop agreeing, because a heap cut can be pushed under an <code>∃</code> and not under a <code>∀</code>.'
    },

    /* --------------------------------------------------------- flattening --- */

    {t:'h3', s:'Flattening'},

    {t:'p', h:'One more property of <code>⟨…⟩</code>, and it is the one piece of syntax in this unit that you cannot do without later. Nested pairs need not be nested brackets. Because <code>⟨a, b, c⟩</code> is read as <code>⟨a, ⟨b, c⟩⟩</code> whenever the second slot is itself a pair, a tower of existentials over a chain of conjunctions is built with one flat, comma-separated list — and taken apart by <code>obtain</code> with one flat pattern. The statement below has two existentials and three conjunctions, so six components; the proof is six things in one bracket, and there is no bookkeeping in it at all.'},

    {t:'anat', tag:'verified',
     src:'theorem nested_pack {P Q : Nat → Prop} {a b : Nat} (hp : P a) (hq : Q b) :\n    ∃ x y, x = a ∧ y = b ∧ P x ∧ Q y :=\n  ⟨a, b, rfl, rfl, hp, hq⟩',
     parts:[
       {m:'∃ x y,', h:'Two existentials, written with one <code>∃</code>. This abbreviates <code>∃ x, ∃ y,</code>, so the proof owes two witnesses before it owes anything else — and they come first in the bracket, in the order the binders appear.'},
       {m:'x = a ∧ y = b ∧ P x ∧ Q y', h:'Three <code>∧</code>s, and like <code>→</code> they associate to the right: this is <code>x = a ∧ (y = b ∧ (P x ∧ Q y))</code>. Four conjuncts, nested three deep, and the flat bracket is what saves you from writing that nesting out.'},
       {m:'⟨a, b, rfl, rfl, hp, hq⟩', h:'Six slots for a term whose type has, on the face of it, two. Reading left to right: <code>a</code> is the first witness, <code>b</code> the second, and then the four conjuncts. The two <code>rfl</code>s prove <code>a = a</code> and <code>b = b</code> — trivial, because the witnesses were <i>chosen</i> to make those equations true, which is the usual reason an equation appears inside an existential. <code>hp</code> and <code>hq</code> are the hypotheses, unchanged.'}
     ]},

    {t:'note', kind:'key', title:'Why six',
     h:'That shape is not an example chosen for its arity. From Unit 14 the central definition of this course reads <i>the heap splits into two disjoint pieces, one satisfying <code>P</code> and the other satisfying <code>Q</code></i>, and written out it is two existentials over three conjunctions: two heaps, a disjointness proof, an equation saying they recombine to the heap you started with, and one proof for each side. Six components, packed and unpacked exactly as above. You are meeting the shape thirteen units before it has any content, on a statement with no memory in it, so that when it does arrive the only new thing is what the components mean.'},

    {t:'ex',
     id:'x06',
     name:'nested_pack / nested_unpack',
     hard:false,
     why:'The first is the six-slot pack from the page above, done rather than read; the second is the direction that actually gets used, where a nest arrives as a hypothesis and has to be opened in one pattern. Every proof about <code>∗</code> from Unit 14 onwards opens with a line of this shape, and a reader who has to count brackets at that point will lose the argument to the syntax.',
     setup:'Two theorems. The first is term mode and takes one bracket. The second is tactic mode: open the hypothesis with <code>obtain</code>, and its equation is <code>x = y</code>, so one of the two proofs you are holding is about the wrong variable until you do something about it — <code>simp [h] at h\'</code>, from Unit 00, rewrites inside a hypothesis using an equation.',
     goal:'theorem nested_pack {P Q : Nat → Prop} {a b : Nat} (hp : P a) (hq : Q b) :\n    ∃ x y, x = a ∧ y = b ∧ P x ∧ Q y :=',
     hints:[
       'The first goal asks for two numbers and four proofs; you have two numbers named in the binders and two of the four proofs. The second goal gives you a nest containing two numbers and three proofs, and asks for a nest containing one number and two proofs.',
       'For the first, the witnesses are forced: <code>x</code> must be <code>a</code> and <code>y</code> must be <code>b</code>, because the first two conjuncts say so. Once they are chosen, those two conjuncts are trivial. For the second, the hypothesis says two numbers exist that are in fact equal, so the answer is to produce either one of them and repair whichever proof is stated about the other.',
       'The first is one flat bracket with six entries; the equations are closed by <code>rfl</code>. The second is <code>obtain</code> with a five-slot pattern, then a <code>simp … at</code> aimed at one of the two proofs, then <code>exact</code> with a three-slot bracket.',
       'First: <code>⟨a, b, rfl, rfl, hp, hq⟩</code>. Second: <code>obtain ⟨x, y, hpx, hqy, hxy⟩ := h</code> leaves <code>hpx : P x</code>, <code>hqy : Q y</code> and <code>hxy : x = y</code>, with the goal <code>∃ z, P z ∧ Q z</code>. Rewriting <code>hpx</code> with <code>hxy</code> turns it into <code>P y</code>, and then <code>y</code> is a witness both proofs are about.'
     ],
     sol:'theorem nested_pack {P Q : Nat → Prop} {a b : Nat} (hp : P a) (hq : Q b) :\n    ∃ x y, x = a ∧ y = b ∧ P x ∧ Q y :=\n  ⟨a, b, rfl, rfl, hp, hq⟩\n\ntheorem nested_unpack {P Q : Nat → Prop} (h : ∃ x y, P x ∧ Q y ∧ x = y) :\n    ∃ z, P z ∧ Q z := by\n  obtain ⟨x, y, hpx, hqy, hxy⟩ := h\n  simp [hxy] at hpx\n  exact ⟨y, hpx, hqy⟩',
     solNote:'Rewriting <code>hqy</code> backwards to <code>Q x</code> and answering with <code>⟨x, hpx, hqy⟩</code> is equally correct and the editor accepts it. Which variable survives is a free choice; that there is a choice at all is what the equation buys.',
     expl:'Packing and unpacking are one skill counted in two directions. The flat bracket hides the nesting on the way in, and the flat <code>obtain</code> pattern hides it on the way out, so the only thing you have to get right is how many components there are and in what order — which you read straight off the statement, left to right.',
     walk:[
       {tac:'⟨a, b, rfl, rfl, hp, hq⟩', h:'Discharges the whole of <code>nested_pack</code>. Two witnesses, then the four conjuncts in the order they are written. The <code>rfl</code>s work only because the witnesses supplied were <code>a</code> and <code>b</code>: after substitution the first two conjuncts read <code>a = a</code> and <code>b = b</code>.'},
       {tac:'obtain ⟨x, y, hpx, hqy, hxy⟩ := h', h:'Five slots for two existentials and two <code>∧</code>s. It replaces <code>h</code> with two numbers and three proofs, and the goal is untouched: nothing has been proved yet, the hypothesis has only been made usable.'},
       {tac:'simp [hxy] at hpx', h:'Rewrites inside <code>hpx</code> using the equation <code>hxy : x = y</code>, turning <code>P x</code> into <code>P y</code>. This is the only step with any content in it. After it, <code>hpx</code> and <code>hqy</code> are about the same number, which is what the goal needs and what they did not have before.'},
       {tac:'exact ⟨y, hpx, hqy⟩', h:'Three slots for one existential over one <code>∧</code>. <code>y</code> is the witness and the two rewritten proofs are the conjuncts.'}
     ],
     deep:[
       {t:'trace', title:'nested_unpack, tactic by tactic',
        start:'P Q : Nat → Prop\nh : ∃ x y, P x ∧ Q y ∧ x = y\n⊢ ∃ z, P z ∧ Q z',
        steps:[
          {tac:'obtain ⟨x, y, hpx, hqy, hxy⟩ := h',
           state:'P Q : Nat → Prop\nx y : Nat\nhpx : P x\nhqy : Q y\nhxy : x = y\n⊢ ∃ z, P z ∧ Q z',
           h:'One hypothesis became five, and the nesting is gone from the display entirely. Compare the pattern with the statement: <code>∃ x</code>, <code>∃ y</code>, then the three conjuncts, in that order and no other.'},
          {tac:'simp [hxy] at hpx',
           state:'P Q : Nat → Prop\nx y : Nat\nhqy : Q y\nhxy : x = y\nhpx : P y\n⊢ ∃ z, P z ∧ Q z',
           h:'<code>hpx</code> now reads <code>P y</code>. It has also moved to the bottom of the context — a rewritten hypothesis is a new hypothesis, so it is re-added at the end, and a context whose order you were relying on will surprise you.'},
          {tac:'exact ⟨y, hpx, hqy⟩', state:'No goals.',
           h:'Three components: the witness and the two conjuncts. <code>x</code> is still in scope and is now unused, which is the visible sign that the equation did its work.'}
        ]},
       {t:'p', h:'The nesting is optional, not a concession. The fully bracketed form of the first proof compiles too, and it is what the flat form means:'},
       {t:'code', tag:'illustration',
        src:'theorem pack_nested {P Q : Nat → Prop} {a b : Nat} (hp : P a) (hq : Q b) :\n    ∃ x y, x = a ∧ y = b ∧ P x ∧ Q y :=\n  ⟨a, ⟨b, ⟨rfl, ⟨rfl, ⟨hp, hq⟩⟩⟩⟩⟩'},
       {t:'detail', title:'What a wrong witness looks like', tag:'aside', open:false,
        blocks:[
          {t:'p', h:'A witness that does not work produces no message about existentials at all. Lean commits to the witness first, substitutes it, and then finds that the second component does not prove what is left.'},
          {t:'code', tag:'sketch', src:'example : ∃ n : Nat, n + 1 = 4 := ⟨2, rfl⟩'},
          {t:'state', cap:'<code>?m.16</code> is a metavariable — the two sides <code>rfl</code> would have to equate are still undetermined at the moment the check fails.',
           src:'error: Application type mismatch: The argument\n  rfl\nhas type\n  ?m.16 = ?m.16\nbut is expected to have type\n  2 + 1 = 4\nin the application\n  Exists.intro 2 rfl'},
          {t:'p', h:'The last line names <code>Exists.intro</code>, the constructor <code>⟨…⟩</code> stood for. Every anonymous-constructor error does this, and it is the fastest way to find out what Lean thought you were building.'}
        ]}
     ],
     pitfall:'Miscounting the <code>obtain</code> pattern — writing <code>⟨x, hpx, hqy, hxy⟩</code>, four slots for five components. It does not fail on that line. The pattern is matched greedily against the nesting, so <code>hpx</code> silently binds the second <i>witness</i>, a <code>Nat</code>, and everything after it shifts; the error arrives on the next line, saying that the argument <code>hpx</code> has type <code>Nat</code>, of sort <code>Type</code>, but is expected to have type <code>P x</code>, of sort <code>Prop</code>. When an <code>obtain</code> is followed by a type error mentioning <code>Nat</code> where you expected a proof, the fault is in the pattern above it, not in the line that reported it — count the components in the statement and compare.',
     variants:'Drop the equation from <code>nested_unpack</code>\'s hypothesis, leaving <code>∃ x y, P x ∧ Q y</code>, and the theorem is false: <code>P</code> could hold only at 0 and <code>Q</code> only at 1, and then no single <code>z</code> satisfies both. The equation is the entire content, and this is the pattern to remember, because the equation in the definition of <code>∗</code> plays the same role — it is what stops the two halves being about unrelated heaps. Reverse it to <code>y = x</code> and the proof still works with the two names exchanged. In <code>nested_pack</code>, replace the first conjunct <code>x = a</code> by <code>x = b</code> and the statement becomes unprovable unless <code>a</code> and <code>b</code> happen to be equal, which nothing says: the witnesses can no longer be chosen to make every equation true at once, and <code>rfl</code> stops closing the first slot.'
    },

    /* -------------------------------------------------------------- close --- */

    {t:'p', h:'One consequence is worth stating before it is needed. From Unit 12 an assertion is a predicate on a store and a heap, and <code>P ⊢ Q</code> — <code>P</code> entails <code>Q</code> — is defined to be <code>∀ σ h, P σ h → Q σ h</code>. That is a <code>∀</code> over an arrow, which is to say a function type, which is to say that <b>every entailment proof in this course is a lambda</b>: it takes a store, a heap and a proof that <code>P</code> holds there, and returns a proof that <code>Q</code> does. About a fifth of the theorems ahead have no <code>by</code> in them at all, and they are written with the four constructions on this page and nothing else.'},

    {t:'dod', h:'You can say what a proof is: a term whose type is the statement, which is why a hypothesis is written like an argument. You can prove an implication with <code>fun</code> and use one by application; prove a <code>∀</code> the same way and use it by supplying its arguments; build an <code>∃</code> or an <code>∧</code> with <code>⟨…⟩</code> and take one apart with <code>.1</code>, <code>.2</code> or <code>obtain</code>; build a <code>∨</code> with <code>Or.inl</code>, <code>Or.inr</code>, <code>left</code> or <code>right</code>, and use one only by case analysis. You can read <code>h.symm</code> and say which theorem it resolves to. You can tell an implicit binder from an explicit one, predict which arguments you must supply, and force the issue with <code>@</code>. And you can pack and unpack a six-component nest in one flat bracket.'},

    {t:'p', h:'Nothing you have written can compute. <code>2 + 2 = 4</code> was closed by <code>rfl</code>, and so was <code>3 + 1 = 4</code> inside an existential — but why did that work, and when will it stop working? Memory is going to be a function, and the first thing we ask of two heaps is whether they are equal.'}

  ]
});
