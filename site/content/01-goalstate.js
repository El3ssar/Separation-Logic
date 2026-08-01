registerChapter({
  id: 'goalstate',
  num: '§',
  phase: 'Phase 0 · Getting started',
  title: 'Reading what Lean tells you',
  blurb: 'A reference for the goal display: the turnstile, the context, the case labels, the names Lean invents, and what the Check button does with a failure.',

  /* Every display on this page is a real goal from a later unit, and the page
     says so in its second paragraph before showing any of them. */
  ledgerForward: ['write_shadow', 'write_empty', 'Heap.write', 'State'],

  /* A reference page for goal displays cannot be built out of goals the reader
     has already proved: the parts that are hard to read only occur later. Each
     exhibit names the unit it belongs to, and none of them is argued from. */
  ledgerAllow: [
    'funext', 'by_cases', 'case pos / case neg', 'exact', 'rfl',
    'Heap.write', 'Heap.empty', 'Heap.singleton',
    'State', 'structure instance ⟨σ, h⟩ / eta',
    /* both fire on `{ store := σ, heap := h }.store`, which is one exhibit:
       the brace literal reads as an implicit binder, the projection as a
       leading dot. ERRATA §1 false-positive class (e). */
    'implicit binder {x : T}', 'leading-dot name resolution (.ctor)'
  ],

  orient: {
    youWill: [
      'Name every part of a Lean goal display and say which parts you are allowed to use.',
      'Print the goal at any point inside a proof with <code>trace_state</code>.',
      'Say where a <code>case pos</code> label came from and which tactic put it there.',
      'Recognise an inaccessible name — the ones ending in <code>✝</code> — and know why you cannot type one.',
      'Read <code>?m.1</code> as “Lean has not decided this yet”.',
      'Read a display that has not been tidied up, and know that Lean will still accept it.',
      'Read the Check panel: what a green result says, what a red one says, and where <code>trace_state</code> output lands.'
    ],
    needs: [
      'Unit 00: a heap is a function, <code>simp</code> and <code>intro</code>, and one goal display already read.'
    ],
    payoff: 'This is the page you keep open in a second tab. Every <code>trace</code> block in the course links here.'
  },

  blocks: [

    /* ------------------------------------------------------------- framing --- */

    {t:'p', h:'This is a reference page, not a lecture. Nothing on it is yours to prove, nothing on it is assigned, and the argument of the course does not pass through it: Unit 01 picks up where Unit 00 stopped whether or not you read this first. What it is for is the one thing you will do on every page from here on — look at what Lean has printed and work out what it is telling you.'},

    {t:'p', h:'The displays below come from proofs spread across the whole course. That is deliberate. A display of something you have already proved has nothing hard to read in it, and the parts that are hard to read — the branch labels, the daggered names, the projection that will not go away — only turn up in proofs you have not reached. So you will see definitions here that do not exist yet, and you are not meant to follow the mathematics in them. Read the shape. Each exhibit names the unit it belongs to, so you can come back to it when it is yours.'},

    /* --------------------------------------------------------- the display --- */

    {t:'h3', s:'Asking Lean for a goal'},

    {t:'p', h:'A Lean editor normally keeps a goal window open beside the text and refreshes it as the cursor moves. The workbook here does not: it compiles what you wrote and reports the result, so a goal appears only if you ask for one. <code>trace_state</code> is how you ask. Put it on a line of its own inside a proof and Lean prints the goal exactly as it stands at that point; it proves nothing and changes nothing, the proof carries on underneath it, and you can drop one in anywhere, read what it says, and delete it. Every display on this page is something Lean printed — the goals from runs with a <code>trace_state</code> in them, the two blocks of error messages from runs that failed. None of it was typed by hand.'},

    {t:'code', tag:'illustration', cap:'The last theorem of Unit 00, with one line inserted.',
     src:'theorem lookup_of_unallocated (x : Loc) (hx : x ≠ 4) : aliasedAfter x = none := by\n  trace_state\n  simp [aliasedAfter, hx]'},

    {t:'state', cap:'What <code>trace_state</code> printed. The proof still went through; this is output, not a result.',
     src:'x : Loc\nhx : x ≠ 4\n⊢ aliasedAfter x = none'},

    {t:'dl', items:[
      {k:'The context', h:'Every line above the <code>⊢</code>. Each is a name, a colon, and what that name stands for. These are the things you may use — nothing else about this proof is in scope, and if what you need is not in the context, no tactic will find it for you.'},
      {k:'<code>x : Loc</code>', h:'A value you have been handed. It is some location; which one is not known and never will be, which is exactly what makes the theorem hold for all of them.'},
      {k:'<code>hx : x ≠ 4</code>', h:'A <i>proof</i> you have been handed. The name is <code>hx</code>, and its type — the thing to the right of the colon — is a proposition rather than a set of values. Values and proofs sit in the same list because Lean makes no distinction between them; that identification is the subject of Unit 01.'},
      {k:'<code>⊢</code>', h:'The turnstile. Above it, what you have; below it, what you owe. It is Lean\'s output rather than your input, so you will rarely type it; the abbreviation is <code>\\vdash</code> if you do.'},
      {k:'The goal', h:'Exactly one proposition, on the line after the turnstile. A proof is finished when there is no goal left rather than when some tactic announces success — which is why every <code>trace</code> block in this course ends with <code>No goals.</code> in the place where a state would otherwise be.'},
      {k:'What is not shown', h:'Every definition and every theorem proved earlier in the file is still available and none of it appears here. The context is what is local to this proof. A display that looks empty above the turnstile means there are no local assumptions, not that there is nothing to work with.'}
    ]},

    /* ---------------------------------------------------------- case labels --- */

    {t:'h3', s:'Where <code>case pos</code> comes from'},

    {t:'code', tag:'illustration', cap:'The statement of <code>write_shadow</code>, from Unit 06, with the two branches written out separately and a <code>trace_state</code> between the split and them.',
     src:'example (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by\n  funext x\n  by_cases hx : x = l\n  trace_state\n  simp [Heap.write, hx]\n  simp [Heap.write, hx]'},

    {t:'state', cap:'Two goals, not one. The blank line is the separator.',
     src:'case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x\n\ncase neg\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : ¬x = l\n⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x'},

    {t:'dl', items:[
      {k:'Where the label came from', h:'A tactic that splits the proof in two has to give the halves names, or nothing on screen would distinguish them. <code>by_cases hx : x = l</code> calls its branches <code>pos</code> and <code>neg</code> — the case where the condition holds and the case where it does not. The label is the branch\'s name, printed above its context.'},
      {k:'What differs between the two', h:'One line. The goal is the same on both sides and every other hypothesis is the same; only <code>hx</code> changes, from <code>x = l</code> to <code>¬x = l</code>. That is the whole content of a case split, and reading the two blocks side by side is the fastest way to see what a split actually bought you.'},
      {k:'Two goals, in order', h:'From the split onwards, each tactic you write applies to the first goal only. The two <code>simp</code> lines above are not a repetition: the first closes <code>pos</code>, and the second then finds itself facing <code>neg</code>. Get one of them wrong and the error will be reported against the goal that was standing at the time, not the one you had in mind.'}
    ]},

    /* -------------------------------------------------------------- daggers --- */

    {t:'h3', s:'Names you did not choose'},

    {t:'p', h:'Some tactics need a name for something you did not ask to be given. If you decline to supply one — by writing <code>_</code> — Lean makes one up, and marks it with a dagger.'},

    {t:'code', tag:'illustration', cap:'The statement of <code>write_empty</code>, from Unit 06. <code>funext</code> hands you a location to compare the two heaps at; <code>_</code> declines to name it.',
     src:'example (l : Loc) (v : Val) : Heap.write Heap.empty l v = Heap.singleton l v := by\n  funext _\n  trace_state\n  simp [Heap.write, Heap.empty, Heap.singleton]'},

    {t:'state', cap:'The location is in the context under the name <code>x✝</code>, and it is in the goal too.',
     src:'l : Loc\nv : Val\nx✝ : Loc\n⊢ Heap.empty.write l v x✝ = Heap.singleton l v x✝'},

    {t:'p', h:'<code>✝</code> means <b>inaccessible</b>. Lean needs a name for that location internally and prints one so you can follow the goal, but it is not a name you are allowed to use, and the dagger says so. It is output only — it is not an input character at all. Copy it off the screen and paste it back in, and the parser does not get as far as complaining that the name is unknown.'},

    {t:'code', tag:'sketch', cap:'The same proof, mentioning the location by the name on the screen, dagger and all.',
     src:'example (l : Loc) (v : Val) : Heap.write Heap.empty l v = Heap.singleton l v := by\n  funext _\n  simp [Heap.write, Heap.empty, Heap.singleton, x✝]'},

    {t:'state', cap:'Real output, from the command line, where the file being compiled is called <code>snippet</code>: after the name come the line, then the column counted from zero, then — on some errors — Lean\'s own name for the diagnostic. Column 49 is the dagger; column 48 is the <code>x</code> in front of it.',
     src:'snippet:3:49: error: expected token\nsnippet:3:48: error(lean.unknownIdentifier): Unknown identifier `x`'},

    {t:'p', h:'<code>expected token</code> is Lean saying it cannot even read that character in a term. Having stopped there, it went back to what it could read — a bare <code>x</code> — and found no such thing, because there is no such thing. The fix is upstream of both messages: name the location when it arrives. <code>funext x</code> in place of <code>funext _</code> puts <code>x : Loc</code> in the context with no dagger on it, and every line after that may use it. A dagger is a signal that you threw a name away one line earlier, and the repair here is to go back and not throw it away.'},

    {t:'detail', title:'When there are two of them, the numbering counts backwards', tag:'aside', open:false, blocks:[
      {t:'p', h:'Inaccessible names would collide if there were several, so Lean separates them with superscripts. The superscript is not an order of introduction read forwards — it is a distance from the present.'},
      {t:'code', tag:'illustration', cap:'Two locations, neither named. The second <code>funext</code> applies to the two heaps the first one left.',
       src:'example : (fun (_ : Loc) => Heap.empty) = (fun _ => Heap.empty) := by\n  funext _\n  funext _\n  trace_state\n  rfl'},
      {t:'state', src:'x✝¹ x✝ : Loc\n⊢ Heap.empty x✝ = Heap.empty x✝'},
      {t:'p', h:'The unadorned <code>x✝</code> is the one introduced most recently — the one the goal is about. <code>x✝¹</code> is the older one, now shadowed and mentioned nowhere. So a rising superscript means further back in the proof, which is the reverse of what the numbering suggests.'}
    ]},

    /* ---------------------------------------------------------------- holes --- */

    {t:'h3', s:'Holes: <code>?m.1</code>'},

    {t:'code', tag:'illustration', cap:'Two terms whose type Lean cannot work out from what is written.',
     src:'#check fun x => x\n#check (none : Option _)'},

    {t:'state', cap:'Lean answers with a type in each case, and neither type is complete.',
     src:'fun x => x : ?m.1 → ?m.1\nnone : Option ?m.2'},

    {t:'p', h:'A name beginning <code>?</code> is a <b>metavariable</b>: a slot Lean has opened and not yet filled. The identity function has a type only once you say what it is the identity <i>on</i>, and nothing here says; <code>none</code> is the empty <code>Option</code> of some type, and nothing here says which. So Lean makes a placeholder, prints it, and waits for something to determine it.'},

    {t:'p', h:'The digits are an internal counter and carry no meaning at all — <code>?m.1</code> and <code>?m.2</code> are two different unknowns, and that is the only thing the numbers tell you. Where the <i>same</i> name is printed twice, as in <code>?m.1 → ?m.1</code>, the repetition is a real claim: whatever the type turns out to be, the argument and the result must both have it. A metavariable in a goal you are trying to close means Lean is still waiting for you to pin something down, and the usual cause is a lemma applied to fewer arguments than Lean needs in order to work the rest out.'},

    /* ------------------------------------------------ displays not tidied up --- */

    {t:'h3', s:'Two things a display shows that you did not write'},

    {t:'p', h:'In the <code>write_shadow</code> goal above you wrote <code>Heap.write h l v₁</code> and Lean printed <code>h.write l v₁</code>. That is not a different term; it is the same term under a printing convention. When a function is called <code>N.f</code> and its first explicit argument has type <code>N</code>, Lean prints <code>N.f a b</code> as <code>a.f b</code> — so <code>Heap.write</code> applied to something of type <code>Heap</code> comes back as <code>.write</code> hanging off it. The convention runs in both directions: you may type either spelling and Lean will accept it, and the two are indistinguishable to every tactic. What it costs you is a search: looking for <code>Heap.write</code> in a printed goal will not find it.'},

    {t:'p', h:'The second is uglier: a structure built in place is not evaluated away in the display.'},

    {t:'code', tag:'illustration', cap:'A state is a store paired with a heap, from Unit 18. <code>P</code> stands for any property of stores.',
     src:'example (σ : Store) (h : Heap) (P : Store → Prop) (hp : P σ) :\n    P ({ store := σ, heap := h } : State).store := by\n  trace_state\n  exact hp'},

    {t:'state', cap:'The projection is still sitting there, unreduced, in the goal.',
     src:'σ : Store\nh : Heap\nP : Store → Prop\nhp : P σ\n⊢ P { store := σ, heap := h }.store'},

    {t:'p', h:'Read the goal: it says <code>P</code> holds of the store field of the record whose store field is <code>σ</code>. Which is to say, <code>P σ</code>, which is <code>hp</code>. Lean agrees — <code>exact hp</code> closes it — and yet the display never simplified. That is the gap between the two notions of equality this course spends Unit 02 on: <code>{ store := σ, heap := h }.store</code> and <code>σ</code> are the same thing <i>by computation</i>, so anything that checks types accepts one for the other, but the pretty-printer prints the term you built rather than the term it reduces to. So an unreduced projection in a goal is not an obstacle and is not evidence that something has gone wrong. Read through it and carry on.'},

    /* ------------------------------------------------------------- failures --- */

    {t:'h3', s:'When Check says no'},

    {t:'code', tag:'sketch', cap:'One typo — <code>wrte</code> for <code>write</code> — and two error messages.',
     src:'example (h : Heap) (l : Loc) (v : Val) : Heap.write h l v l = some v := by\n  simp [Heap.wrte]'},

    {t:'state', cap:'Real output. The workbook shows the same two messages as two red boxes, labelled <code>line 2, col 9</code> and <code>line 2, col 3</code>, with the text underneath.',
     src:'snippet:2:8: error(lean.unknownIdentifier): Unknown constant `Heap.wrte`\nsnippet:2:2: error: `simp` made no progress'},

    {t:'p', h:'Two messages, one mistake. The second is a consequence of the first: <code>simp</code> was handed a list containing a name that does not resolve, so it was left with nothing to unfold and reported that it had made no progress. Read errors in the order Lean produced them and fix the first one; the rest are frequently its shadow, and a proof that produces four messages is not usually four mistakes.'},

    {t:'dl', items:[
      {k:'A green result', h:'<b>Lean accepts this proof.</b> No errors, no <code>sorry</code>. That is the only wording that counts as proved, and it is the one that records the exercise as solved.'},
      {k:'An amber one', h:'<b>It compiles, but there is still a <code>sorry</code> in it.</b> Lean is taking your word for the part you left out, so the proof is not finished and does not count as solved.'},
      {k:'A red one', h:'One box per error message, each with its own location label, and a count — <code>2 errors</code> — beside the button. There is no summary sentence for a failure: the messages are the verdict. There may well be more of them than you made mistakes.'},
      {k:'line 2, col 9', h:'The label above a message. Lines are counted from the first line of <b>your</b> text, not from the top of the file Lean actually compiled — your work is spliced onto everything the course has established so far, and the numbers are shifted back for you before you see them. Columns are counted from one, which is why the command-line output above says column 8 where the box says <code>col 9</code>.'},
      {k:'in the chapter prelude', h:'The label you get instead when the error is not in your text at all. It means what you wrote has broken something that was already established — usually by redefining a name that already exists.'},
      {k:'A box with no colour on it', h:'Neither a success nor a failure: information. This is where the output of <code>trace_state</code>, <code>#check</code> and <code>#eval</code> arrives, so a proof can be perfectly correct and still print three boxes.'},
      {k:'“Starting Lean…”', h:'The first check of a session loads Lean\'s core library, which takes about ten seconds. It happens once. Every check after that is quick, and you can keep reading while it runs.'},
      {k:'“The Lean runtime failed”', h:'Not a verdict on your proof — the machinery itself fell over. Try again before you doubt what you wrote.'}
    ]},

    {t:'p', h:'Nothing here needs remembering. Come back to it when a display does something you did not expect; the argument itself resumes at Unit 01, with the question Unit 00 left standing — what, in Lean, a proof actually is.'}

  ]
});
