registerChapter({
  id: 'disjoint',
  num: '08',
  phase: 'Phase 1 · The resource algebra',
  title: 'Disjointness',
  blurb: 'What it means for two heaps not to overlap, said at one address at a time — and the first theorem in the course in which a disequality between two pointers is derived instead of assumed.',

  orient: {
    youWill: [
      'Read <code>Heap.disjoint h₁ h₂ := ∀ l, h₁ l = none ∨ h₂ l = none</code> and say why it is stated with <code>none</code> at each address rather than with domains as sets.',
      'Open a folded <code>def</code> returning a <code>Prop</code> with <code>intro</code>, and use a disjointness hypothesis by applying it at an address — <code>hd l</code> is already a proof.',
      'Write a proof with no tactics in it at all, and say why <code>rfl</code> is enough to show <code>Heap.empty l = none</code>.',
      'Prove that owning two cells separately <i>proves</i> that their addresses differ — the converse nobody hands you in a program.',
      'Use <code>subst</code> to make two equal variables into one, and <code>&lt;;&gt;</code> with a bullet block to close two branches that need more than one tactic each.',
      'Prove that the only heap disjoint from itself is the empty one.'
    ],
    needs: [
      'Unit 07: exact ownership — a claim about memory pins down the whole heap it is made about, so combining two claims means dividing memory.',
      'Unit 05: <code>Heap.empty</code>, <code>Heap.singleton</code>, and the lookup laws <code>singleton_same</code> and <code>singleton_other</code>, whose disequality is written with the address being looked up on the left.',
      'Unit 01: <code>∨</code>, <code>Or.inl</code>/<code>Or.inr</code>, <code>rcases</code>, <code>left</code>/<code>right</code>, <code>constructor</code> on an <code>↔</code>, and that <code>h.symm</code> means <code>Head.symm h</code> where <code>Head</code> is the head of <code>h</code>\'s type. Unit 02: <code>cases</code> on an equation between distinct constructors, and <code>rw … at</code>.'
    ],
    payoff: 'Unit 09 combines two disjoint heaps and Unit 11 proves that the resulting splitting relation is associative; both take a disjointness hypothesis at every use site, and this page is where that hypothesis acquires its meaning. <code>singleton_disjoint_iff</code> is where every disequality in every later program proof comes from: Unit 17 lifts it to assertions, and Unit 28 spends it to close the question Unit 00 opened.'
  },

  blocks: [

    /* ------------------------------------------------------------- the thread --- */

    {t:'p', h:'Cutting a heap in two is two statements, not one: the pieces do not overlap, and the pieces are together the whole thing. Only the first can be asked with what you have. Overlapping is a question about two heaps taken one address at a time, and answering at an address is the one thing a heap does. Putting two pieces together is an operation on heaps, and you have no such operation. So this unit settles overlap and leaves the assembling to the next one.'},

    {t:'p', h:'There is a second debt to collect here. <code>update_comm</code> and <code>write_comm</code> both carry a hypothesis saying that two addresses differ, and both proofs spend it in exactly one line. Neither unit says where such a hypothesis comes from. In a program it is not given: a routine handed two pointers has no way to tell whether they are the same pointer, which was Unit 00\'s complaint. The third of the four theorems below derives one instead of assuming it. Holding two cells <i>separately</i> turns out to be a proof that their addresses are different.'},

    /* --------------------------------------------------------- the definition --- */

    {t:'sec', s:'What "does not overlap" says'},

    {t:'p', h:'On paper you would say it about domains: two partial functions do not overlap when the set of addresses where the first is defined and the set where the second is defined meet nowhere. Written out in Lean, that is a statement about two objects you would first have to build. A heap is <code>Loc → Option Val</code> and nothing else; a domain is not part of a heap but something computed from one, and there is no set type in this course to compute it into. You would be carrying a second representation of every heap alongside the heap, plus the lemmas keeping the two in step. And the fact you actually want is never about the two sets at once. It is about one address — the one the proof you are writing is currently looking at. So state it there.'},

    {t:'code', tag:'verified', cap:'Disjointness, at one address at a time.',
     src:'def Heap.disjoint (h₁ h₂ : Heap) : Prop :=\n  ∀ l, h₁ l = none ∨ h₂ l = none'},

    {t:'defn', term:'Disjointness',
     h:'Two heaps are <b>disjoint</b> when at every address at least one of them is undefined. So every cell in memory belongs to at most one of the two, and a cell belonging to neither is allowed. The definition is a <code>∀</code> whose body is a disjunction, which means a proof of <code>Heap.disjoint h₁ h₂</code> is a <i>function</i> from an address to a proof about that address.',
     cap:'Neither heap is required to be defined anywhere, so this is a condition on how the two fit together and not a condition on either alone.'},

    {t:'p', h:'The disjunction is inclusive. At an address where neither heap is defined, both sides hold and nothing asks you to say which one you meant; the definition is a bound on overlap, not a partition of memory. It is also stated positively — an equation on one side or an equation on the other — rather than as the negation of an overlap. That is what makes it usable. Apply it at an address and you are handed a disjunction whose two branches each contain an equation that <code>rw</code> can fire. A negation has to be turned into something before it says anything at all.'},

    {t:'svg', cap:'Filled boxes are the domain. <code>h₁</code> and <code>h₂</code> are disjoint: read down any column and at most one box is filled. <code>h₁</code> and <code>h₃</code> are not, and address 4 is the whole of the reason — everywhere else they behave impeccably.',
     src:'<svg viewBox="0 0 600 232" role="img" aria-label="Two disjoint heaps and a third that overlaps the first at address 4">\n  <g class="dg">\n    <text x="176" y="16" class="dg-lab">addresses</text>\n    <g class="dg-t sm">\n      <text x="202" y="34" text-anchor="middle" class="dg-note">0</text>\n      <text x="262" y="34" text-anchor="middle" class="dg-note">1</text>\n      <text x="322" y="34" text-anchor="middle" class="dg-note">2</text>\n      <text x="382" y="34" text-anchor="middle" class="dg-note">3</text>\n      <text x="442" y="34" text-anchor="middle" class="dg-note">4</text>\n      <text x="502" y="34" text-anchor="middle" class="dg-note">5</text>\n    </g>\n    <g class="dg-cells">\n      <text x="8" y="66" class="dg-t">h₁</text>\n      <rect class="dg-box" x="176" y="44" width="52" height="34" rx="5"/>\n      <rect class="a"      x="236" y="44" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="44" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="356" y="44" width="52" height="34" rx="5"/>\n      <rect class="a"      x="416" y="44" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="44" width="52" height="34" rx="5"/>\n      <text x="262" y="66" text-anchor="middle" class="dg-t">7</text>\n      <text x="442" y="66" text-anchor="middle" class="dg-t">3</text>\n\n      <text x="8" y="118" class="dg-t">h₂</text>\n      <rect class="dg-box" x="176" y="96" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="236" y="96" width="52" height="34" rx="5"/>\n      <rect class="a"      x="296" y="96" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="356" y="96" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="416" y="96" width="52" height="34" rx="5"/>\n      <rect class="a"      x="476" y="96" width="52" height="34" rx="5"/>\n      <text x="322" y="118" text-anchor="middle" class="dg-t">5</text>\n      <text x="502" y="118" text-anchor="middle" class="dg-t">1</text>\n    </g>\n    <text x="176" y="150" class="dg-lab">and a heap that is not disjoint from h₁</text>\n    <g class="dg-cells">\n      <text x="8" y="188" class="dg-t">h₃</text>\n      <rect class="a"      x="176" y="166" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="236" y="166" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="166" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="356" y="166" width="52" height="34" rx="5"/>\n      <rect class="b"      x="416" y="166" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="166" width="52" height="34" rx="5"/>\n      <text x="202" y="188" text-anchor="middle" class="dg-t">2</text>\n      <text x="442" y="188" text-anchor="middle" class="dg-t">8</text>\n      <text x="176" y="220" class="dg-note">one address is enough to destroy it</text>\n    </g>\n  </g>\n</svg>'},

    {t:'detail', title:'Could the domains be written down after all?', open:false,
     blocks:[
       {t:'p', h:'They can, without a set type: a subset of <code>Loc</code> is a predicate on <code>Loc</code>. So the domain of a heap is the addresses at which it does not answer <code>none</code>, and two heaps overlap nowhere when no address is in both domains.'},
       {t:'code', tag:'illustration', cap:'The set-flavoured statement, and the proof that it is the same condition.',
        src:'def dom (h : Heap) (l : Loc) : Prop := h l ≠ none\n\nexample (h₁ h₂ : Heap) :\n    (∀ l, ¬ (dom h₁ l ∧ dom h₂ l)) ↔ Heap.disjoint h₁ h₂ := by\n  constructor\n  · intro hn l\n    by_cases h1 : h₁ l = none\n    · left\n      exact h1\n    · right\n      by_cases h2 : h₂ l = none\n      · exact h2\n      · exact absurd ⟨h1, h2⟩ (hn l)\n  · intro hd l hcon\n    rcases hd l with h | h\n    · exact hcon.1 h\n    · exact hcon.2 h'},
       {t:'p', h:'The two statements are equivalent, and the proof shows what the equivalence costs. Going right to left is three lines, because <code>Heap.disjoint</code> hands you an equation and an equation is what contradicts a <code>≠</code>. Going left to right is nine, and the two <code>by_cases</code> calls in it are doing De Morgan by hand: from "not both are defined" nothing follows until you have decided, for each side separately, whether it is defined. The <code>none</code> form does that deciding once, in the statement. Every later proof instantiates disjointness at an address and immediately splits on the result, so the <code>none</code> form is the one that arrives ready to use.'}
     ]},

    /* ---------------------------------------------------- using the definition --- */

    {t:'sec', s:'Two structural facts'},

    {t:'p', h:'<code>Heap.disjoint h₁ h₂</code> is a <code>def</code> returning a <code>Prop</code>, so the goal displays as <code>h₁.disjoint h₂</code> with the <code>∀</code> hidden inside it. Nothing has to be unfolded by hand. <code>intro</code> looks through the definition to find a binder, and finds one.'},

    {t:'code', tag:'illustration', cap:'A proof that says nothing, to show the two moves everything else on this page is built from.',
     src:'example (h₁ h₂ : Heap) (hd : Heap.disjoint h₁ h₂) : Heap.disjoint h₁ h₂ := by\n  intro l\n  exact hd l'},

    {t:'trace', title:'The definition opens by itself',
     start:'h₁ h₂ : Heap\nhd : h₁.disjoint h₂\n⊢ h₁.disjoint h₂',
     steps:[
       {tac:'intro l',
        state:'h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\n⊢ h₁ l = none ∨ h₂ l = none',
        h:'The goal was a name; it is now the disjunction that name abbreviates, at the address now in scope. Lean did not report having unfolded anything, because to it there was nothing to unfold: <code>Heap.disjoint h₁ h₂</code> and the <code>∀</code> are the same term.'},
       {tac:'exact hd l',
        state:'',
        h:'And the hypothesis is used the same way. <code>hd</code> is a function from addresses to proofs, so <code>hd l</code> is already a proof of that disjunction — no tactic stands between the hypothesis and the fact you want out of it. Every proof in this unit begins by choosing which address to apply <code>hd</code> at.'}
     ],
     done:'No goals.'},

    {t:'ex',
     id:'m2-1',
     name:'disjoint_symm',
     hard:false,
     why:'Two lines, and they are the method of the whole unit: name an address, then apply the hypothesis at it. Every later proof about disjointness starts that way, including the union laws of Unit 09 and the splitting laws of Unit 11. The theorem itself is what lets every later statement be made in whichever argument order is convenient, instead of being proved twice.',
     setup:'The disjointness is a hypothesis of an implication rather than a binder, so the goal you start from is an arrow. Both heaps are implicit: Lean reads them off the hypothesis when you apply the theorem.',
     goal:'theorem disjoint_symm {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by',
     hints:[
       'Unfolded on both sides, the goal is: given a function taking every address <code>l</code> to a proof of <code>h₁ l = none ∨ h₂ l = none</code>, produce a function taking every address to a proof of <code>h₂ l = none ∨ h₁ l = none</code>. No fact about heaps is involved beyond that.',
       'At each address the two disjunctions are the same two statements with the sides exchanged. So fix an address, take what the hypothesis says there, and swap it.',
       'One <code>intro</code> can take more than one name, and it will go through the definition to find the second binder. For the swap, Unit 01 gave you <code>Or.symm</code>, and dot notation writes it on the right of the proof it applies to.',
       '<code>intro hd l</code> leaves <code>hd : h₁.disjoint h₂</code>, <code>l : Loc</code> and the goal <code>⊢ h₂ l = none ∨ h₁ l = none</code>. A single term closes it.'
     ],
     sol:'theorem disjoint_symm {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by\n  intro hd l\n  exact (hd l).symm',
     solNote:'Two names in one <code>intro</code>: the first is the hypothesis, the second is the address the goal is about. The second name is available only because Lean unfolded <code>Heap.disjoint h₂ h₁</code> to look for a binder, and it does not announce having done so.',
     expl:'A disjointness hypothesis is a function, and the goal is a function of the same kind with the two disjuncts swapped. Applying the hypothesis at the address produces the disjunction one way round; <code>Or.symm</code> turns it round the other way. There is nothing about <code>none</code>, about heaps, or about memory in the proof — the theorem is true of <code>∀ l, P l ∨ Q l</code> for any <code>P</code> and <code>Q</code>. That tells you the price of symmetry here: none, and no hypothesis.',
     walk:[
       {tac:'intro hd l', h:'Named the hypothesis and the address in one move. The first name is the antecedent of the arrow that was visible in the goal; the second is the binder inside <code>Heap.disjoint h₂ h₁</code>, which was not visible and did not need to be. The goal is now the disjunction at <code>l</code>, in the order the <i>conclusion</i> wants it.'},
       {tac:'exact (hd l).symm', h:'Spent the hypothesis at the address, then swapped. <code>hd l</code> has type <code>h₁ l = none ∨ h₂ l = none</code>; the brackets are needed because <code>.symm</code> attaches to the result of the application, not to <code>hd</code>. <code>Or.symm</code> is resolved by the head of that type, and its result is the goal.'}
     ],
     deep:[
       {t:'trace', title:'Two lines, two states',
        start:'h₁ h₂ : Heap\n⊢ h₁.disjoint h₂ → h₂.disjoint h₁',
        steps:[
          {tac:'intro hd l',
           state:'h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\n⊢ h₂ l = none ∨ h₁ l = none',
           h:'The hypothesis is still folded — it prints as <code>h₁.disjoint h₂</code> — while the goal has opened, because that is the side <code>intro</code> was working on. Both are usable in their own way regardless of how they print.'},
          {tac:'exact (hd l).symm', state:'', h:'The term has the type displayed on the last line, so there is nothing left to do.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The swap attempted on the hypothesis itself, before any address has been chosen.',
        src:'theorem ds_a {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by\n  intro hd\n  exact hd.symm'},
       {t:'state', cap:'The line-and-column prefix is dropped here and throughout this page.',
        src:'error(lean.invalidField): Invalid field `symm`: The environment does not contain `Function.symm`, so it is not possible to project the field `symm` from an expression\n  hd\nof type\n  ∀ (l : Loc), h₁ l = none ∨ h₂ l = none'},
       {t:'p', h:'Unit 01\'s resolution rule, biting. <code>h.foo</code> means <code>Head.foo h</code> where <code>Head</code> is the head constant of <code>h</code>\'s <i>type</i>, and here that type is a function type, whose head Lean calls <code>Function</code>. <code>.symm</code> becomes available only after <code>hd</code> has been applied to an address, at which point the type is an <code>Or</code> and the head is <code>Or</code>. The error message is also the clearest possible display of what a disjointness hypothesis is.'}
     ],
     pitfall:'Reaching for <code>.symm</code> before the address is chosen, as above. The fix is the brackets in <code>(hd l).symm</code>, and dropping them does not undo the fix — it moves it. Dot notation binds tighter than application, so <code>hd l.symm</code> is read as <code>hd (l.symm)</code> and the same complaint lands on the address instead: <code>The environment does not contain `Nat.symm`, so it is not possible to project the field `symm` from an expression l of type `Nat`</code>. One rule, applied twice, to two different types.',
     variants:'There is no hypothesis to drop: the theorem has none, and it holds of <code>∀ l, P l ∨ Q l</code> for any <code>P</code> and <code>Q</code> at all. What can be got wrong is the order. Drop the <code>.symm</code> and <code>exact hd l</code> reports <code>Type mismatch: hd l has type h₁ l = none ∨ h₂ l = none but is expected to have type h₂ l = none ∨ h₁ l = none</code> — the two heaps are the wrong way round and nothing else is wrong, which is the whole content of the theorem. Make the two heaps explicit, <code>(h₁ h₂ : Heap)</code>, and the proof does not change by a character while every use site does: <code>disjoint_symm hd</code> then reports <code>The argument hd has type a.disjoint b of sort `Prop` but is expected to have type Heap of sort `Type`</code>, because the first thing the theorem now asks for is a heap. <code>disjoint_symm a b hd</code> compiles, and having to write those two heaps out at every call is what the braces buy. Stated as an <code>↔</code> the theorem would be no stronger — <code>⟨disjoint_symm, disjoint_symm⟩</code> proves it, from the implication used twice — and it would cost a <code>.mp</code> at every use site.'
    },

    {t:'p', h:'The other structural fact is about the smallest heap there is. <code>Heap.empty</code> answers <code>none</code> everywhere, so it overlaps nothing, and the proof of that needs no tactics whatever.'},

    {t:'ex',
     id:'m2-2',
     name:'disjoint_empty_left / disjoint_empty_right',
     hard:false,
     why:'Your first proof with no <code>by</code> in it: a proof of a <code>∀</code> is a function, and here the function is short enough to write out. The fact matters as well as the proof. The empty heap is disjoint from everything including itself, which is what will let Unit 09 make it the neutral element of combination and Unit 11 split any heap trivially into itself and nothing.',
     setup:'Two theorems, mirror images. Write the first and the second is one letter different. Neither needs a tactic block, though both can be done with one — the <i>Why it works</i> panel shows the tactic version and what it costs.',
     goal:'theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=\n  sorry\n\ntheorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=',
     hints:[
       'Unfolded at an arbitrary address <code>l</code>, the first goal is <code>Heap.empty l = none ∨ h l = none</code>. Nothing at all is known about <code>h</code>, so only one of the two disjuncts can possibly be proved.',
       'Choose the left side, and then look at what is left to prove. <code>Heap.empty</code> is the function sending every address to <code>none</code>, so <code>Heap.empty l</code> and <code>none</code> are not two things that happen to be equal — they are one term written two ways.',
       'A proof of <code>∀ l, …</code> is a function, so it can be written <code>fun l => …</code> with no <code>by</code> at all. Unit 01 gave the two injections into a disjunction; Unit 02 gave the term that proves an equation whose two sides reduce to the same thing.',
       'The proof begins <code>fun _ => …</code>, with no <code>by</code> above it: the address is never looked at, so its binder is <code>_</code>. What fills the body is one of the two injections applied to <code>rfl</code>, and the injection is forced — take the disjunct that names <code>Heap.empty</code>, since the other names a heap nothing is known about. The second theorem is the same term with the other injection.'
     ],
     sol:'theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=\n  fun _ => Or.inl rfl\n\ntheorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=\n  fun _ => Or.inr rfl',
     solNote:'No <code>by</code>, no tactic, no goal state to read. The type <code>Heap.disjoint Heap.empty h</code> is a function type as far as Lean is concerned, so a lambda is an acceptable proof of it, and Lean unfolds the definition to see that.',
     expl:'The proof is a function of an address that ignores its argument. At any address the left disjunct is <code>Heap.empty l = none</code>; <code>Heap.empty</code> is <code>fun _ => none</code>, so <code>Heap.empty l</code> reduces to <code>none</code> and both sides of the equation are the same term. That is the condition Unit 02 gave for <code>rfl</code>: nothing here is blocked, because nothing is being cased on. The mirror theorem needs the right injection instead, and the two are genuinely different terms even though the statements are mirror images — which is why the second one exists rather than being derived. Once <code>disjoint_symm</code> is available, it could be: <code>disjoint_symm (disjoint_empty_left h)</code> proves it too.',
     walk:[
       {tac:'fun _ =>', h:'Introduced the address that the <code>∀</code> in <code>Heap.disjoint</code> binds, and threw it away. This is what <code>intro l</code> would have done, written as a term. Naming it <code>_</code> is a statement that the address plays no part; if you name it and never use it, Lean warns.'},
       {tac:'Or.inl', h:'Chose which disjunct to prove. This fixes the remaining obligation to <code>Heap.empty l = none</code> and discards the other one, which was unprovable — nothing whatever is known about <code>h</code>.'},
       {tac:'rfl', h:'Discharged that obligation by reduction. <code>Heap.empty l</code> unfolds to <code>(fun _ => none) l</code> and then to <code>none</code>; both sides are <code>none</code>, so the equation holds by definition and needs no proof beyond saying so.'},
       {tac:'Or.inr rfl', h:'The second theorem. The heaps have swapped places, so the disjunct that reduces is now the right one, and the injection changes to match. Nothing else moves.'}
     ],
     deep:[
       {t:'trace', title:'The same proof driven by tactics, for comparison',
        start:'h : Heap\n⊢ Heap.empty.disjoint h',
        steps:[
          {tac:'intro l',
           state:'h : Heap\nl : Loc\n⊢ Heap.empty l = none ∨ h l = none',
           h:'The definition opens and the address appears, exactly as <code>fun _ =></code> did.'},
          {tac:'left',
           state:'h : Heap\nl : Loc\n⊢ Heap.empty l = none',
           h:'<code>left</code> is <code>Or.inl</code> as a tactic: it commits to the first disjunct and deletes the second from the goal. There is no going back — if you pick the wrong side the failure arrives later, on whatever you try next.'},
          {tac:'rfl', state:'', h:'Three lines where the term was one. The tactic version is not wrong, and on a harder goal it would be the right choice; here every step is forced, so writing the term is shorter and says the same thing.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The left theorem with the right injection.',
        src:'theorem de_bad (h : Heap) : Heap.disjoint Heap.empty h :=\n  fun _ => Or.inr rfl'},
       {t:'state', cap:'The argument Lean names is <code>rfl</code>. <code>Or.inr</code> appears only as the application it sits inside.',
        src:'error: Application type mismatch: The argument\n  rfl\nhas type\n  ?m.5 = ?m.5\nbut is expected to have type\n  h x✝ = none\nin the application\n  Or.inr rfl'},
       {t:'p', h:'The injection is never the thing that is wrong. <code>Or.inr</code> is available for any disjunction whatever; all it does is decide which of the two obligations you have taken on. What fails is the proof of that obligation, and <code>h x✝ = none</code> is unprovable because <code>h</code> is an arbitrary heap. The dagger on <code>x✝</code> is there because the binder was written <code>_</code>, so the address has no name you could type.'}
     ],
     pitfall:'Picking the wrong injection, and then reading the error as a complaint about <code>Or.inr</code>. It is not: the error lands on <code>rfl</code>, and it tells you which equation you have promised to prove. Read the "expected to have type" line and ask whether it is true; if it names the arbitrary heap, you are on the wrong side.',
     variants:'<code>Heap.disjoint Heap.empty Heap.empty</code> is proved by either theorem, and by either injection — the empty heap is disjoint from itself, which is a special case of the final exercise below. Replace <code>Heap.empty</code> by <code>Heap.singleton l v</code> and the statement is not merely harder to prove, it is false, at exactly one point: take the arbitrary <code>h</code> to be <code>Heap.singleton l v</code> itself and read the definition at the address <code>l</code>. Both disjuncts are then <code>some v = none</code>, an equation between two distinct constructors of <code>Option</code>, and there is no such proof. Nothing survives the substitution except the shape of the argument: it is <code>rfl</code> that carries all the weight here, so the theorem is really a statement about how <code>Heap.empty</code> was defined, and every other heap has to be argued about instead of reduced.'
    },

    /* ------------------------------------------------ separation and aliasing --- */

    {t:'sec', s:'Where a disequality comes from'},

    {t:'p', h:'Now the theorem with content. Unit 06 proved that two writes to different addresses commute, and the hypothesis that the addresses differ was handed to it. A verification of a real routine never gets such a gift: two pointer arguments are two numbers, and nothing in the type of a pointer says they are different numbers. What a specification <i>can</i> say is that the routine holds the cell at one address and, separately, holds the cell at the other. Two one-cell heaps, disjoint. The claim to prove is that this is enough.'},

    {t:'code', tag:'sketch', cap:'The two statements this section is about; their proofs are the exercise below.',
     src:'theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂)\n\ntheorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂'},

    {t:'p', h:'The first is the direction you would expect: different addresses, therefore no overlap. The second packages it with its converse, and the converse is the one that pays. Read the <code>mp</code> direction as a statement about ownership. If you hold the cell at <code>l₁</code>, and separately you hold the cell at <code>l₂</code>, then <code>l₁</code> and <code>l₂</code> are different addresses — because if they were the same address you would be holding one cell twice, and holding it twice is exactly what disjointness forbids. Nothing was assumed about the two pointers. The disequality is a consequence of the separation.'},

    {t:'note', kind:'key', title:'Separation implies non-aliasing',
     h:'This is the exchange the whole subject is built on. You give up the right to say "this heap contains the cell <code>l</code>" and say instead "this heap <i>is</i> the cell <code>l</code>" — Unit 07\'s choice — and in return, writing two claims side by side <i>generates</i> the disequalities that a program logic otherwise has to assume. Unit 17 proves the same statement one level up, about assertions rather than heaps, and Unit 28 spends it on the rule Unit 00 refuted.'},

    {t:'p', h:'The argument for the <code>mp</code> direction is three sentences. Suppose the two addresses are equal. Then both heaps are the one-cell heap at that address, and disjointness applied there says that one of the two answers <code>none</code>. But a one-cell heap answers <code>some</code> at its own address, which is <code>singleton_same</code>. Two of the moves in that argument have no name yet in your vocabulary, so take them separately before proving anything.'},

    {t:'h4', s:'Making two variables one: <code>subst</code>'},

    {t:'p', h:'"Suppose the two addresses are equal" gives you a hypothesis <code>heq : l₁ = l₂</code> with two variables still standing. You can rewrite with it, and everything works; but the two names remain, and every subsequent step has to be aimed at the right one. <code>subst</code> does something stronger: it eliminates one of the variables altogether.'},

    {t:'code', tag:'illustration', cap:'A hypothesis, and a fact stated about the wrong one of two equal addresses.',
     src:'example (h : Heap) (l₁ l₂ : Loc) (heq : l₁ = l₂) (hn : h l₁ = none) : h l₂ = none := by\n  subst heq\n  exact hn'},

    {t:'trace', title:'What <code>subst</code> removes',
     start:'h : Heap\nl₁ l₂ : Loc\nheq : l₁ = l₂\nhn : h l₁ = none\n⊢ h l₂ = none',
     steps:[
       {tac:'subst heq',
        state:'h : Heap\nl₁ : Loc\nhn : h l₁ = none\n⊢ h l₁ = none',
        h:'<code>l₂</code> is gone from the context, and so is <code>heq</code> — there is nothing left for the equation to say. Every occurrence of <code>l₂</code> was replaced by <code>l₁</code>, in the goal and in every hypothesis at once. Which variable survives is not yours to choose: <code>subst</code> eliminates the one it can, and here that is <code>l₂</code>.'},
       {tac:'exact hn', state:'', h:'The hypothesis and the goal are now literally the same statement.'}
     ],
     done:'No goals.'},

    {t:'p', h:'<code>subst heq</code> needs one side of <code>heq</code> to be a local variable that does not occur on the other side; it cannot be used on <code>h l = some v</code>, where neither side is a bare variable. <code>rw [heq] at hd</code> would also have worked above, and in the exercise below it works too. The difference is bookkeeping: after <code>rw</code> you still have two address variables and a hypothesis relating them, and you must remember which of them your next tactic should mention. After <code>subst</code> there is one address and no choice to get wrong.'},

    {t:'h4', s:'Two branches that each need two tactics: <code>&lt;;&gt; ·</code>'},

    {t:'p', h:'The other move is "disjointness applied there says one of the two answers <code>none</code>" — a disjunction, split by <code>rcases</code>, whose two branches are the same argument with a different value in it. Here is the concrete case, with the two addresses already equal.'},

    {t:'code', tag:'illustration', cap:'Two one-cell heaps at the same address, holding different values, are not disjoint.',
     src:'example : ¬ Heap.disjoint (Heap.singleton 4 3) (Heap.singleton 4 7) := by\n  intro hd\n  rcases hd 4 with h | h <;>\n    · rw [singleton_same] at h\n      cases h'},

    {t:'p', h:'After <code>rcases</code> there are two goals. In the first, <code>h : Heap.singleton 4 3 4 = none</code>; in the second, <code>h : Heap.singleton 4 7 4 = none</code>. Both are closed by rewriting with <code>singleton_same</code> — a one-cell heap read at its own address — and then by <code>cases h</code>, which asks how an equation between <code>some</code> and <code>none</code> could have been proved and finds no way, leaving no goals. The two branches differ only in the value that ends up on the left, and the <i>text</i> that closes them is identical. That is precisely when <code>&lt;;&gt;</code> applies. What is new is the dot.'},

    {t:'code', tag:'sketch', cap:'The same proof with the bullet removed and the two tactics joined by a semicolon.',
     src:'example : ¬ Heap.disjoint (Heap.singleton 4 3) (Heap.singleton 4 7) := by\n  intro hd\n  rcases hd 4 with h | h <;>\n    rw [singleton_same] at h; cases h'},

    {t:'state', cap:'One branch closed, one branch standing.',
     src:'error: unsolved goals\ncase inr\nhd : (Heap.singleton 4 3).disjoint (Heap.singleton 4 7)\nh : some 7 = none\n⊢ False'},

    {t:'p', h:'<code>&lt;;&gt;</code> takes <i>one</i> tactic and runs it on every goal its left-hand side produced. The semicolon is not part of that tactic; it sequences what comes after the combinator has finished, and by then only the first goal is left over from the <code>rw</code>s. So the <code>rw</code> ran twice and <code>cases</code> ran once. The focus dot fixes it by making the two tactics into a single block: <code>· rw [singleton_same] at h</code> followed by <code>cases h</code>, indented under the dot, is one tactic as far as <code>&lt;;&gt;</code> is concerned, and it runs whole on each branch.'},

    {t:'ex',
     id:'m2-3',
     name:'singleton_disjoint and singleton_disjoint_iff',
     hard:false,
     why:'<b>Separation proves non-aliasing.</b> The <code>mp</code> direction of the second theorem produces a disequality between two addresses out of nothing but the claim that the two cells are held separately. Unit 00 asked where such a disequality could come from and had no answer; Units 04 and 06 both assumed one. From here on, every disequality in every program proof in this course traces back to this line, and Unit 17 proves the same thing about assertions.',
     setup:'Two theorems. The first needs a case split on the address and a decision about which side of the disjunction to prove; watch the orientation that <code>singleton_other</code> wants its disequality in. The second needs <code>constructor</code>, then the two moves from the section above; its <code>mpr</code> direction is the first theorem, applied.',
     goal:'theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) := by\n  sorry\n\ntheorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂ := by',
     hints:[
       'The first goal, once an address <code>x</code> has been named, is <code>Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none</code>. The second is an <code>↔</code>; its <code>mp</code> half is <code>disjointness → l₁ ≠ l₂</code>, and <code>l₁ ≠ l₂</code> is <code>l₁ = l₂ → False</code>, so that half takes two hypotheses and has to produce <code>False</code>.',
       'For the first: an address either is <code>l₁</code> or it is not. If it is not, the first heap is undefined there. If it is, then it is not <code>l₂</code> — because <code>l₁</code> and <code>l₂</code> differ — so the second heap is undefined there. For the <code>mp</code> half of the second: assume the two addresses are equal, make them one address, and look at what disjointness says there. Both heaps are defined there and disjointness says one of them is not.',
       'The tools, in the order they are wanted. First theorem: <code>intro</code>, <code>by_cases</code> on <code>x = l₁</code>, <code>left</code> and <code>right</code>, and <code>singleton_other</code> — whose disequality argument is written with the address being <i>looked up</i> first, so in one of the two branches you will have to build it with a <code>have</code> rather than find it. Second theorem: <code>constructor</code>, then <code>subst</code>, <code>rcases</code>, <code>singleton_same</code>, <code>cases</code> on an equation between distinct constructors, and the bullet form of <code>&lt;;&gt;</code>; the <code>mpr</code> half is a single <code>exact</code> naming the first theorem.',
       'First theorem: <code>intro x</code> then <code>by_cases hx : x = l₁</code> leaves two goals with the same statement, one carrying <code>hx : x = l₁</code> and one carrying <code>hx : ¬x = l₁</code>. The second of them is <code>left</code> followed by <code>exact singleton_other l₁ x v₁ hx</code>. Second theorem: <code>constructor</code> leaves <code>case mp</code> and <code>case mpr</code>, and <code>intro hd heq</code> on the first leaves <code>⊢ False</code>.'
     ],
     sol:'theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) := by\n  intro x\n  by_cases hx : x = l₁\n  · right\n    have : x ≠ l₂ := by rw [hx]; exact hne\n    exact singleton_other l₂ x v₂ this\n  · left\n    exact singleton_other l₁ x v₁ hx\n\ntheorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂ := by\n  constructor\n  · intro hd heq\n    subst heq\n    rcases hd l₁ with h | h <;>\n      · rw [singleton_same] at h; cases h\n  · exact singleton_disjoint v₁ v₂',
     solNote:'This is the longest proof you have written, and it has four separate decisions in it: which address to split on, which disjunct to take in each branch, which orientation the disequality needs, and where to spend <code>hne</code>. If you have climbed all four hints and it still will not come, open this and read the walkthrough — the shapes here recur for the rest of the course and there is nothing to be gained by grinding.',
     expl:'The first proof is Unit 05\'s pattern with a disjunction on top. Split on whether the address under consideration is <code>l₁</code>. If it is not, the first heap is undefined there and the left disjunct holds. If it is, the first heap <i>is</i> defined there, so the left disjunct is hopeless — but then the address is <code>l₁</code>, which is not <code>l₂</code>, so the second heap is undefined and the right disjunct holds. That is the only line in the proof that uses <code>hne</code>, and it is the reason the theorem needs it. The second proof\'s <code>mp</code> half is the refutation: assume the addresses are the same, collapse them to one with <code>subst</code>, and read disjointness at that address. Whichever disjunct disjointness offers, it says a one-cell heap is undefined at its own address, and <code>singleton_same</code> plus constructor distinctness kill both. The <code>mpr</code> half is the first theorem with its arguments supplied.',
     walk:[
       {tac:'intro x', h:'Opened the folded definition and named the address the rest of the proof is about. The goal is now a disjunction of two lookups.'},
       {tac:'by_cases hx : x = l₁', h:'Split on the only question that matters: is this the address the first heap is defined at? Two goals with identical statements, distinguished only by <code>hx</code>.'},
       {tac:'· right', h:'The <code>pos</code> branch, where <code>hx : x = l₁</code>. The first heap answers <code>some v₁</code> here, so the left disjunct cannot be proved; committing to the right one is forced, not chosen. The goal shrinks to <code>Heap.singleton l₂ v₂ x = none</code>.'},
       {tac:'have : x ≠ l₂ := by rw [hx]; exact hne', h:'<b>The line that spends the hypothesis.</b> <code>rw [hx]</code> turns the goal of the sub-proof from <code>x ≠ l₂</code> into <code>l₁ ≠ l₂</code>, which is exactly <code>hne</code>. This is where non-aliasing enters the proof, and it enters once. The result has no name, so it is <code>this</code>.'},
       {tac:'exact singleton_other l₂ x v₂ this', h:'The lookup law: a one-cell heap at <code>l₂</code>, read at an address that is not <code>l₂</code>, answers <code>none</code>. Its last argument is the disequality, written with the address being looked up on the left — which is why the <code>have</code> above proves <code>x ≠ l₂</code> and not <code>l₂ ≠ x</code>.'},
       {tac:'· left', h:'The <code>neg</code> branch, where <code>hx : ¬x = l₁</code>. Now it is the first heap that is undefined here, so the left disjunct is the provable one.'},
       {tac:'exact singleton_other l₁ x v₁ hx', h:'The same law on the other heap, and this time the disequality is already in the context in the orientation the law wants. No <code>have</code> is needed and <code>hne</code> is not touched: this branch is true whether or not the two addresses differ.'},
       {tac:'constructor', h:'Second theorem. Split the <code>↔</code> into its two implications, printed as <code>case mp</code> and <code>case mpr</code> after the field names of <code>Iff</code>.'},
       {tac:'· intro hd heq', h:'The <code>mp</code> half. Two hypotheses, because the conclusion <code>l₁ ≠ l₂</code> is itself an implication into <code>False</code>: <code>hd</code> is the disjointness and <code>heq : l₁ = l₂</code> is the assumption to be refuted. The goal is <code>False</code>.'},
       {tac:'subst heq', h:'Made the two addresses one. <code>l₂</code> disappears from the context and both heaps become one-cell heaps at <code>l₁</code>, differing only in the value they hold.'},
       {tac:'rcases hd l₁ with h | h <;>', h:'Spent the disjointness at the address it is about, and split the disjunction it yields. Two goals, both <code>False</code>, carrying <code>h : Heap.singleton l₁ v₁ l₁ = none</code> and <code>h : Heap.singleton l₁ v₂ l₁ = none</code>. The combinator says the next tactic runs on both.'},
       {tac:'· rw [singleton_same] at h; cases h', h:'One tactic block, run twice. <code>rw</code> reduces the left side of <code>h</code> to <code>some v₁</code> in one branch and <code>some v₂</code> in the other, and <code>cases h</code> observes that no constructor of <code>Option</code> can produce an equation between <code>some</code> and <code>none</code>, so there is no case to handle and the goal is closed. The dot is what makes the two tactics one.'},
       {tac:'· exact singleton_disjoint v₁ v₂', h:'The <code>mpr</code> half is the first theorem. Its two value arguments are explicit and its disequality argument is the implication\'s own hypothesis, which Lean supplies from the goal.'}
     ],
     deep:[
       {t:'trace', title:'The mp direction, address by address',
        start:'l₁ l₂ : Loc\nv₁ v₂ : Val\n⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂',
        steps:[
          {tac:'constructor',
           state:'case mp\nl₁ l₂ : Loc\nv₁ v₂ : Val\n⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂) → l₁ ≠ l₂',
           h:'Only the first of the two goals is shown; <code>case mpr</code> is waiting behind it.'},
          {tac:'intro hd heq',
           state:'case mp\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nheq : l₁ = l₂\n⊢ False',
           h:'Both antecedents named. The second is the one to be refuted, which is why the goal is <code>False</code>.'},
          {tac:'subst heq',
           state:'case mp\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\n⊢ False',
           h:'<code>l₂</code> and <code>heq</code> are both gone. The two heaps are now visibly the same heap with different contents, which is what makes the contradiction available.'},
          {tac:'rcases hd l₁ with h | h',
           state:'case mp.inl\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\nh : Heap.singleton l₁ v₁ l₁ = none\n⊢ False',
           h:'The first branch. Disjointness has been applied at <code>l₁</code> and one side of its disjunction taken; the other branch is the same statement with <code>v₂</code>.'},
          {tac:'rw [singleton_same] at h',
           state:'case mp.inl\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\nh : some v₁ = none\n⊢ False',
           h:'The hypothesis is now an equation between two distinct constructors. <code>cases h</code> closes it, and the same two lines close the other branch with <code>v₂</code> in place of <code>v₁</code>.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'The first theorem with the disequality in its <code>pos</code> branch proved the other way round. Everything else is unchanged.',
        src:'theorem sd_wrongorient {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) := by\n  intro x\n  by_cases hx : x = l₁\n  · right\n    have : l₂ ≠ x := by rw [hx]; exact hne.symm\n    exact singleton_other l₂ x v₂ this\n  · left\n    exact singleton_other l₁ x v₁ hx'},
       {t:'state', cap:'The <code>have</code> itself succeeds; the failure is one line later.',
        src:'error: Application type mismatch: The argument\n  this\nhas type\n  l₂ ≠ x\nbut is expected to have type\n  x ≠ l₂\nin the application\n  singleton_other l₂ x v₂ this'},
       {t:'p', h:'<code>Ne</code> records which side is which, so <code>l₂ ≠ x</code> and <code>x ≠ l₂</code> are different terms and only one of them fits. <code>Ne.symm</code> converts between them: <code>exact singleton_other l₂ x v₂ this.symm</code> would rescue this version. The habit to form is to read the lemma\'s statement before writing the <code>have</code>, since <code>singleton_other</code> fixes the orientation once and for all.'}
     ],
     pitfall:'Choosing <code>left</code> in the branch where <code>x = l₁</code>. The goal becomes <code>Heap.singleton l₁ v₁ x = none</code>, and the only law that could close it is <code>singleton_other</code>, which reports <code>Application type mismatch: The argument hx has type x = l₁ but is expected to have type x ≠ l₁</code>. The message is telling you that you have the case hypothesis pointing the wrong way — not that it is malformed, but that in <i>this</i> branch the first heap is exactly the one that is defined.',
     variants:'Drop <code>hne</code> from the first theorem and it is false, and the witness is the refutation already compiled above: <code>l₁ = l₂ = 4</code>, <code>v₁ = 3</code>, <code>v₂ = 7</code>. Replacing <code>hne</code> by <code>v₁ ≠ v₂</code> does not rescue it, because that same pair of heaps satisfies the new hypothesis — <code>3 ≠ 7</code> — and disjointness never looks at values. In the other direction nothing is lost by taking <code>v₁ = v₂</code>: the <code>↔</code> holds for any values whatever, which is what makes it a statement about addresses. Replacing <code>subst heq</code> by <code>rw [heq] at hd</code> compiles too, but only with the instantiation moved: <code>rw … at hd</code> changes <code>hd</code> and leaves both address variables standing, so it is <code>rcases hd l₂</code> that works and <code>rcases hd l₁</code> that fails — the hypothesis you get is <code>h : Heap.singleton l₂ v₁ l₁ = none</code>, whose two addresses are now different terms, and the next line reports <code>Did not find an occurrence of the pattern Heap.singleton ?l ?v ?l</code>. That one error is the whole case for <code>subst</code>: with the variable eliminated there is no wrong address left to name.'
    },

    {t:'p', h:'One statement is left, and it is the sharpest thing that can be said about the definition. A heap that does not overlap itself has nothing in it, because at every address the two disjuncts of the definition are the same statement, so disjointness with itself says directly that the heap is undefined everywhere.'},

    {t:'ex',
     id:'x19',
     name:'self_disjoint_iff_empty',
     hard:false,
     why:'The one-line characterisation of what disjointness means, and the engine of Unit 14. Separating conjunction will let you write "<code>P</code>, and separately <code>P</code>", and the reason that is not the same as <code>P</code> — the reason this logic has no contraction rule — is that the two copies would have to be disjoint from each other. This theorem says only the empty heap manages that, so the two copies collapse to nothing, and the rule fails.',
     setup:'An <code>↔</code>, so <code>constructor</code> first. The forward half is an equation between two functions; the backward half is a disjunction with the same statement on both sides.',
     goal:'theorem self_disjoint_iff_empty (h : Heap) : Heap.disjoint h h ↔ h = Heap.empty := by',
     hints:[
       'Forward: given that <code>h</code> does not overlap itself, prove <code>h = Heap.empty</code> — an equation between two functions, not between two lookups. Backward: given <code>h = Heap.empty</code>, prove <code>∀ l, h l = none ∨ h l = none</code>.',
       'Forward: two functions are equal when they agree at every address, so fix an address; disjointness there offers <code>h l = none</code> or <code>h l = none</code>, and whichever one you land on is the fact you want. Backward: replace <code>h</code> by the empty heap and both disjuncts are settled by reduction.',
       '<code>funext</code> turns the equation between functions into an equation at an arbitrary address. <code>rcases</code> splits the disjunction, and since the two branches now close with the same single tactic, a bare <code>&lt;;&gt;</code> is enough and no bullet is needed. The backward half is <code>subst</code> and one injection.',
       'Forward: <code>intro hd</code> then <code>funext l</code> leaves <code>hd</code> in the context and the goal <code>⊢ h l = Heap.empty l</code>. Backward: <code>intro he l</code> leaves <code>he : h = Heap.empty</code>, <code>l : Loc</code> and the goal <code>⊢ h l = none ∨ h l = none</code>.'
     ],
     sol:'theorem self_disjoint_iff_empty (h : Heap) : Heap.disjoint h h ↔ h = Heap.empty := by\n  constructor\n  · intro hd\n    funext l\n    rcases hd l with h1 | h1 <;> exact h1\n  · intro he l\n    subst he\n    exact Or.inl rfl',
     solNote:'The forward half closes with <code>exact h1</code> on a goal reading <code>h l = Heap.empty l</code> while <code>h1</code> reads <code>h l = none</code>. Those are the same statement: <code>Heap.empty l</code> reduces to <code>none</code>, and <code>exact</code> checks types up to reduction.',
     expl:'The definition of disjointness, read with both arguments the same, is <code>∀ l, h l = none ∨ h l = none</code> — a disjunction whose two sides are one statement. So the hypothesis is really <code>∀ l, h l = none</code> wearing a disguise, and the only work in the forward direction is taking the disguise off: <code>funext</code> to get down to one address, <code>rcases</code> to open the disjunction, and either branch supplies the equation. The backward direction is <code>disjoint_empty_left</code> with the equation used first: once <code>h</code> has been replaced by <code>Heap.empty</code>, the left disjunct is <code>rfl</code>.',
     walk:[
       {tac:'constructor', h:'Split the <code>↔</code> into <code>case mp</code> and <code>case mpr</code>.'},
       {tac:'· intro hd', h:'Named the disjointness. The goal is <code>h = Heap.empty</code>, an equation between two heaps, which is an equation between two functions.'},
       {tac:'funext l', h:'Reduced it to one address: <code>⊢ h l = Heap.empty l</code>. Now the hypothesis, which is about addresses, can be applied.'},
       {tac:'rcases hd l with h1 | h1 <;> exact h1', h:'Applied disjointness at <code>l</code> and split what came back. Both branches carry the identical hypothesis <code>h1 : h l = none</code>, and <code>exact h1</code> closes both — <code>Heap.empty l</code> is <code>none</code> after reduction, so no rewriting is called for. One tactic per branch, so <code>&lt;;&gt;</code> needs no bullet here.'},
       {tac:'· intro he l', h:'The other direction. Two names again: the equation, and the address that the folded <code>Heap.disjoint h h</code> in the goal binds.'},
       {tac:'subst he', h:'Replaced <code>h</code> by <code>Heap.empty</code> everywhere and removed <code>h</code> from the context. The goal is now <code>Heap.empty l = none ∨ Heap.empty l = none</code>.'},
       {tac:'exact Or.inl rfl', h:'The same term as <code>disjoint_empty_left</code>, for the same reason: <code>Heap.empty l</code> reduces to <code>none</code>. Either injection would do, since the two disjuncts are now the same statement.'}
     ],
     deep:[
       {t:'trace', title:'The forward half',
        start:'h : Heap\n⊢ h.disjoint h ↔ h = Heap.empty',
        steps:[
          {tac:'constructor  then  intro hd',
           state:'case mp\nh : Heap\nhd : h.disjoint h\n⊢ h = Heap.empty',
           h:'An equation between two heaps. Nothing about it mentions an address, and the hypothesis says nothing except about addresses.'},
          {tac:'funext l',
           state:'case mp\nh : Heap\nhd : h.disjoint h\nl : Loc\n⊢ h l = Heap.empty l',
           h:'That mismatch is now gone: the goal is at an address and so is everything the hypothesis can say.'},
          {tac:'rcases hd l with h1 | h1',
           state:'case mp.inl\nh : Heap\nhd : h.disjoint h\nl : Loc\nh1 : h l = none\n⊢ h l = Heap.empty l',
           h:'The first of two branches, and the second is identical to it — same hypothesis, same name, same goal. That is the theorem, visible in a goal state: with both arguments the same, disjointness offers you the same fact twice.'}
        ],
        done:'No goals.'},
       {t:'code', tag:'sketch', cap:'Closing the branch by rewriting instead of by <code>exact</code>.',
        src:'theorem x19_rw (h : Heap) : Heap.disjoint h h → h = Heap.empty := by\n  intro hd\n  funext l\n  rcases hd l with h1 | h1 <;> rw [h1]'},
       {t:'state', cap:'Both branches survive, in the same state.',
        src:'error: unsolved goals\ncase inl\nh : Heap\nhd : h.disjoint h\nl : Loc\nh1 : h l = none\n⊢ none = Heap.empty l\n\ncase inr\nh : Heap\nhd : h.disjoint h\nl : Loc\nh1 : h l = none\n⊢ none = Heap.empty l'},
       {t:'p', h:'The rewrite worked and the trailing <code>rfl</code> that <code>rw</code> attempts did not fire, although <code>Heap.empty l = none</code> is true by reduction and <code>exact h1</code> exploits exactly that. The two are checked at different settings: <code>rw</code>\'s closing attempt only unfolds definitions marked as cheap to unfold, and <code>Heap.empty</code> is an ordinary <code>def</code>, while <code>exact</code> reduces as far as it needs to. Adding <code>rfl</code> as a separate tactic finishes the proof — but it has to go inside a bullet block under the <code>&lt;;&gt;</code>, or it will run on the first branch only.'}
     ],
     pitfall:'Trying to use <code>hd</code> before <code>funext</code>. <code>rcases hd l with h1 | h1</code> written immediately after <code>intro hd</code> reports <code>Unknown identifier `l`</code>: there is no address in scope yet, because the goal is still an equation between whole heaps. The order is forced — get down to a point, then instantiate.',
     variants:'The backward implication on its own is trivial and nothing needs it; the forward one is what Unit 14 spends. Stated with <code>∀ l, h l = none</code> in place of <code>h = Heap.empty</code> it is the same theorem with the <code>funext</code> moved out of the proof and into the statement, and it is weaker in use, because an equation between heaps can be rewritten with and a family of equations cannot. Replace one of the two <code>h</code>s by a different heap and the <code>↔</code> fails in both directions at once: <code>Heap.disjoint Heap.empty h</code> holds for every <code>h</code> whatever, and says nothing about either heap being empty.'
    },

    {t:'detail', title:'Disjointness is stronger than it needs to be, and that is the point', open:false,
     blocks:[
       {t:'p', h:'Suppose all you wanted from two heaps was that combining them makes sense — that there is no ambiguity about what the combination holds at any address. Disjointness gives you that, but it is not the weakest condition that does. Two heaps could both be defined at an address and agree there, and the combination would still be unambiguous. Call that <b>compatibility</b>.'},
       {t:'code', tag:'illustration', cap:'Compatibility, and a pair of heaps that has it while failing disjointness.',
        src:'def compatible (h₁ h₂ : Heap) : Prop :=\n  ∀ l v w, h₁ l = some v → h₂ l = some w → v = w\n\nexample (l : Loc) (v : Val) : compatible (Heap.singleton l v) (Heap.singleton l v) := by\n  intro x a b ha hb\n  rw [ha] at hb\n  exact some_inj a b hb\n\nexample (l : Loc) (v : Val) : ¬ Heap.disjoint (Heap.singleton l v) (Heap.singleton l v) := by\n  intro hd\n  rcases hd l with h | h <;>\n    · rw [singleton_same] at h; cases h'},
       {t:'p', h:'And compatibility really is enough for the operation to behave. Here is the combination of the next unit, proved commutative under the weaker hypothesis. The case analysis is Unit 09\'s technique and the proof is here only so that the claim is a theorem rather than an assertion.'},
       {t:'code', tag:'illustration', cap:'Commutativity of the combination, from compatibility alone.',
        src:'example (h₁ h₂ : Heap) (hc : compatible h₁ h₂) :\n    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by\n  funext l\n  unfold Heap.union\n  cases hx : h₁ l with\n  | none => cases hy : h₂ l with\n    | none => rfl\n    | some w => rfl\n  | some v => cases hy : h₂ l with\n    | none => rfl\n    | some w => rw [hc l v w hx hy]'},
       {t:'p', h:'So the course over-strengthens on purpose. Compatibility is the right condition if what you want is a well-defined operation on heaps; disjointness is the right condition if what you want is <i>ownership</i>. Under compatibility, two claims can both be about the same cell, and then "I hold this and separately you hold that" no longer means the two of you can act independently — a write through one would be visible through the other. Every theorem in the rest of this course is about who may touch what, not about whether an expression denotes, and that is why the stronger hypothesis is the one carried everywhere. It is also why <code>self_disjoint_iff_empty</code> is a theorem here and would be false under compatibility, where every heap is compatible with itself.'}
     ]},

    /* ----------------------------------------------------- the other half --- */

    {t:'sec', s:'The other half of the sentence'},

    {t:'p', h:'"The heap splits into these two pieces" needs both halves: the pieces do not overlap, and the pieces are together the whole. The second half needs an operation, so here it is, together with the relation that uses it. Both are stated here and nothing on this page proves anything about either; the definition of splitting has to mention the combination, so the combination has to exist before the definition can be written down.'},

    {t:'code', tag:'verified', cap:'Combination, and the relation this module is heading for.',
     src:'def Heap.union (h₁ h₂ : Heap) : Heap :=\n  fun l =>\n    match h₁ l with\n    | some v => some v\n    | none   => h₂ l\n\ndef Heap.splits (whole left right : Heap) : Prop :=\n  Heap.disjoint left right ∧ whole = Heap.union left right'},

    {t:'p', h:'<code>Heap.splits whole left right</code> is a conjunction, and you can now prove the first conjunct of it. The second is an equation between heaps, and the right-hand side is a function defined by a <code>match</code>: a construct that chooses its answer by looking at which constructor of <code>Option</code> its argument is. It is asked here about <code>h₁ l</code>, so at an address where <code>h₁</code> is defined the combination answers what <code>h₁</code> holds, and elsewhere it defers to <code>h₂</code>. That asymmetry is a decision, and it is the first thing Unit 09 has to justify. What you have here is the text of an operation and not one fact about it.'},

    {t:'detail', title:'Why not make the union demand a disjointness proof?', open:false,
     blocks:[
       {t:'p', h:'The honest mathematical object is a partial operation: the union of two heaps is defined when, and only when, they are disjoint. The first way to write that in a total type theory is to make the proof an argument, so that you cannot form the combination without supplying one.'},
       {t:'code', tag:'sketch', cap:'A union that demands its proof, and the attempt to state that it is associative.',
        src:'def unionOf (h₁ h₂ : Heap) (_ : Heap.disjoint h₁ h₂) : Heap :=\n  Heap.union h₁ h₂\n\nexample (h₁ h₂ h₃ : Heap) (d₁₂ : Heap.disjoint h₁ h₂) (d₂₃ : Heap.disjoint h₂ h₃) :\n    unionOf (unionOf h₁ h₂ d₁₂) h₃ = unionOf h₁ (unionOf h₂ h₃ d₂₃) := rfl'},
       {t:'state', cap:'Not a failed proof — a statement that cannot be written.',
        src:'error: Type mismatch\n  unionOf h₁ (unionOf h₂ h₃ d₂₃)\nhas type\n  h₁.disjoint (unionOf h₂ h₃ d₂₃) → Heap\nbut is expected to have type\n  (unionOf h₁ h₂ d₁₂).disjoint h₃ → Heap'},
       {t:'p', h:'Neither side is a heap. Each is still a function waiting for a disjointness proof, and the two proofs wanted are different — one about <code>h₁</code> against a combination, one about a combination against <code>h₃</code>. Neither is available, and producing either is itself a theorem. So the associativity of this operation cannot even be <i>stated</i> until two lemmas about it have been proved, and those lemmas are about the operation whose statement is blocked. The way out is to make the operation total and carry disjointness separately, at every use site. That is the next unit\'s subject, and its cost is one extra hypothesis on almost every lemma in this module.'}
     ]},

    {t:'dod', h:'You can state disjointness of two heaps at one address at a time and say what the set-flavoured version would have cost. You can open a folded <code>def</code> returning a <code>Prop</code> with <code>intro</code>, and apply a disjointness hypothesis at an address to get a disjunction you can case on. You can write a proof as a term with no tactics in it, and say why <code>rfl</code> settles <code>Heap.empty l = none</code>. You can collapse two equal variables into one with <code>subst</code>, and run a two-tactic block on every branch a split produced with <code>&lt;;&gt;</code> and a focus dot — and you can say what goes wrong when the dot is left out. You can prove that owning two cells separately forces their addresses to differ, and that the only heap disjoint from itself is the empty one.'},

    {t:'p', h:'We can say two heaps do not overlap. We still cannot <i>combine</i> them, and "the heap splits into these two pieces" needs both halves of that sentence.'}

  ]
});
