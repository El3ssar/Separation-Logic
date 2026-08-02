registerChapter({
  id: 'star',
  num: '14',
  phase: 'Phase 2 · The logic of ownership',
  title: 'Separating conjunction, and what it cannot do',
  blurb: 'One definition, two mechanical moves, and then the two theorems that make this a different logic: you cannot forget a conjunct, and you cannot copy one.',

  orient: {
    youWill: [
      'Write the definition of <code>∗</code> from memory and name its four components in order.',
      'Say what each of <code>Heap.disjoint h₁ h₂</code> and <code>h = Heap.union h₁ h₂</code> is holding up, by reading a compiled counterexample to the connective you get when each is deleted.',
      'Build a star with a flat six-slot <code>⟨…⟩</code>, and take one apart with a six-name <code>intro</code> pattern — and say why proving a star is a creative act and using one is not.',
      'Prove that owning one address twice over is contradictory, in three lines that spend nothing but Unit 08.',
      'Prove that <code>P ∗ Q ⊢ P</code> is <b>false</b>, and read the witness that makes it false.',
      'Prove that <code>P ⊢ P ∗ P</code> is <b>false</b> as a rule, and point at the single conjunct of the definition that forbids it — by deleting that conjunct and watching duplication come back.',
      'Say what a substructural logic is, which rule of ordinary logic each failure corresponds to, and name the rule that the first failure makes necessary.'
    ],
    needs: [
      'Unit 13: <code>emp</code>, <code>↦</code>, and that an ownership hypothesis is definitionally an equation between heaps, so <code>subst</code>, <code>rw</code> and <code>congrFun</code> all reach through it.',
      'Unit 12: <code>Assertion</code>, <code>⊢</code>, <code>aAnd</code>, <code>aFalse</code>, <code>aTrue</code>, and <code>and_left</code> — the projection that is about to have no analogue.',
      'Unit 08: <code>Heap.disjoint</code>, <code>singleton_disjoint</code>, <code>singleton_disjoint_iff</code>, and <code>self_disjoint_iff_empty</code>. Unit 09: <code>Heap.union</code>, <code>union_of_none</code>, <code>union_of_some</code>, <code>union_self</code>.',
      'Unit 01: that <code>⟨…⟩</code> flattens, and exercise <code>x06</code>, which was this connective\'s shape with the heaps taken out.'
    ],
    payoff: 'Every structural rule in the remaining twenty-four units exists to compensate for something on this page. A precondition that mentions a cell the command never touches cannot be thinned away, so that cell has to be carried through the proof by a rule written for the purpose — and Unit 27 proves that rule. The first of this unit\'s two refutations is why it has to exist; the second is why <code>∗</code> is a different kind of conjunction at all.'
  },

  blocks: [

    /* ============================================================== opening === */

    {t:'p', h:'Write down what <i>I own this cell, and separately that one</i> has to say about the heap in hand. It has to say that the heap comes apart: there is a piece the left claim owns, a piece the right claim owns, the two pieces do not overlap, and together they are all of it. Nothing in that sentence says <i>which</i> way the heap comes apart, and it cannot: each heap divides differently, and the assertion has to be readable at any of them. So the division is quantified — existentially, because the claim is that <i>some</i> division works, not that every one does. Everything else is fixed.'},

    {t:'p', h:'On paper this is one line: <code>P ∗ Q</code> holds at <code>h</code> when <code>h = h₁ ⊎ h₂</code> with <code>P</code> at <code>h₁</code> and <code>Q</code> at <code>h₂</code>. The symbol <code>⊎</code> is doing three jobs at once. It asserts that the two heaps do not overlap; it forms their combination; and it names the decomposition, so that <code>h₁</code> and <code>h₂</code> can be talked about afterwards. A reader who has only ever seen it on paper cannot tell those three apart, because one glyph hides all three.'},

    {t:'p', h:'Lean has no <code>⊎</code>, and Module 2 declined to build one. Unit 09 made <code>Heap.union</code> total and left-biased rather than proof-carrying, and Unit 08 kept <code>Heap.disjoint</code> as a separate proposition, for reasons that were about rewriting and had nothing to do with logic. The consequence lands here: the three jobs come apart into a binder and two conjuncts, and each of the two conjuncts can be pointed at, deleted, and priced.'},

    {t:'code', tag:'verified', cap:'The separating conjunction. Four components under two existentials.',
     src:'def star (P Q : Assertion) : Assertion :=\n  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂\ninfixr:55 " ∗ " => star'},

    {t:'anat', tag:'verified',
     src:'def star (P Q : Assertion) : Assertion :=\n  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂',
     parts:[
       {m:'fun σ h', h:'The two arguments every <code>Assertion</code> takes. The store passes through untouched and is handed to both conjuncts unchanged — nobody owns a variable, and there is nothing to divide. Only the heap is cut.'},
       {m:'∃ h₁ h₂', h:'The cut. It is existential, and that single fact is the source of every asymmetry on this page: to <i>prove</i> a star you must produce <code>h₁</code> and <code>h₂</code> yourself, and to <i>use</i> one you are handed two heaps you know nothing else about. Turning the quantifier round — <i>however</i> the heap is cut, <code>P</code> holds on the left and <code>Q</code> on the right — gives a connective satisfied by almost nothing, because one of the cuts always available is the whole heap beside the empty one, and <code>0 ↦ 4</code> is false of a two-cell heap.'},
       {m:'Heap.disjoint h₁ h₂', h:'The two pieces do not overlap. This is what makes the connective say <i>separately</i> rather than <i>as well</i>, and it is the conjunct Unit 08\'s <code>singleton_disjoint_iff</code> was proved to spend.'},
       {m:'h = Heap.union h₁ h₂', h:'The two pieces are all of the heap, and nothing else. Without it the cut would float free of <code>h</code> and the assertion would stop being about the heap it is evaluated at.'},
       {m:'P σ h₁', h:'The left conjunct is evaluated at the left piece — not at <code>h</code>. This is the whole difference from <code>aAnd</code>, which hands both conjuncts the same <code>h</code>.'},
       {m:'Q σ h₂', h:'And the right conjunct at the right piece. The two conjuncts are never asked about each other\'s memory, which is what makes a specification of one part of a program survive being placed beside another.'}
     ]},

    {t:'p', h:'Four components under two witnesses: six slots. Unit 01 asked you to pack and unpack exactly that shape, thirteen units ago, with numbers in place of the heaps. It was <code>x06</code>, and it was chosen then because this is where it lands.'},

    /* ============================================================ precedence === */

    {t:'sec', s:'Where the symbol binds'},

    {t:'p', h:'<code>infixr:55</code> puts <code>∗</code> between the two notations already in play. Entailment is <code>infix:40</code> from Unit 12 and <code>↦</code> is <code>infix:60</code> from Unit 13, so a star binds looser than a points-to and tighter than a turnstile. That is not a preference; it is what makes the statements of this course readable without brackets, and it can be checked rather than asserted.'},

    {t:'code', tag:'illustration', cap:'Three parses, each stated as an equation between the bracketed form and the bare one, and each closed by <code>rfl</code>. If any parse were different, the <code>rfl</code> would fail.',
     src:'example (P Q R : Assertion) : ((P ∗ Q) ⊢ R) = (P ∗ Q ⊢ R) := rfl\nexample (l₁ l₂ : Loc) (v₁ v₂ : Val) : ((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) = (l₁ ↦ v₁ ∗ l₂ ↦ v₂) := rfl\nexample (P Q R : Assertion) : (P ∗ (Q ∗ R)) = (P ∗ Q ∗ R) := rfl'},

    {t:'p', h:'The third line is the <code>r</code> in <code>infixr</code>: three-way stars group to the right. Nothing yet says the grouping does not matter, and nothing so far says it should not — the definition cuts the heap in two, and cutting a heap in two twice is not visibly the same operation as doing it the other way round. Unit 16 is where that gets settled.'},

    /* =============================================================== picture === */

    {t:'sec', s:'The same heap, or complementary halves'},

    {t:'svg', cap:'One heap, holding <code>4</code> at address 0 and <code>7</code> at address 3. Under <code>aAnd</code> both conjuncts are asked about all six addresses. Under <code>∗</code> the addresses are divided, and each conjunct is asked only about its own side. Where the line falls is not fixed by the picture — the definition says only that <i>some</i> line exists.',
     src:'<svg viewBox="0 0 600 268" role="img" aria-label="A heap handed whole to both conjuncts of a classical conjunction, and divided between the conjuncts of a separating conjunction">\n  <g class="dg">\n    <text x="8" y="26" class="dg-t">aAnd P Q</text>\n    <g class="dg-t sm">\n      <text x="202" y="26" text-anchor="middle" class="dg-note">0</text>\n      <text x="262" y="26" text-anchor="middle" class="dg-note">1</text>\n      <text x="322" y="26" text-anchor="middle" class="dg-note">2</text>\n      <text x="382" y="26" text-anchor="middle" class="dg-note">3</text>\n      <text x="442" y="26" text-anchor="middle" class="dg-note">4</text>\n      <text x="502" y="26" text-anchor="middle" class="dg-note">5</text>\n    </g>\n    <g class="dg-cells">\n      <text x="140" y="58" class="dg-t">h</text>\n      <rect class="a"      x="176" y="36" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="236" y="36" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="36" width="52" height="34" rx="5"/>\n      <rect class="a"      x="356" y="36" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="416" y="36" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="36" width="52" height="34" rx="5"/>\n      <text x="202" y="58" text-anchor="middle" class="dg-t">4</text>\n      <text x="382" y="58" text-anchor="middle" class="dg-t">7</text>\n    </g>\n    <rect class="dg-box a" x="176" y="82" width="352" height="20" rx="5"/>\n    <text x="352" y="96" text-anchor="middle" class="dg-note">P is asked about all of h</text>\n    <rect class="dg-box a" x="176" y="108" width="352" height="20" rx="5"/>\n    <text x="352" y="122" text-anchor="middle" class="dg-note">Q is asked about all of h</text>\n\n    <text x="8" y="180" class="dg-t">P ∗ Q</text>\n    <g class="dg-cells">\n      <text x="140" y="212" class="dg-t">h</text>\n      <rect class="a"      x="176" y="190" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="236" y="190" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="296" y="190" width="52" height="34" rx="5"/>\n      <rect class="b"      x="356" y="190" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="416" y="190" width="52" height="34" rx="5"/>\n      <rect class="dg-box" x="476" y="190" width="52" height="34" rx="5"/>\n      <text x="202" y="212" text-anchor="middle" class="dg-t">4</text>\n      <text x="382" y="212" text-anchor="middle" class="dg-t">7</text>\n    </g>\n    <line class="dg-arr thin" x1="352" y1="182" x2="352" y2="256"/>\n    <rect class="dg-box a" x="176" y="236" width="172" height="20" rx="5"/>\n    <text x="262" y="250" text-anchor="middle" class="dg-note">P at h₁</text>\n    <rect class="dg-box b" x="356" y="236" width="172" height="20" rx="5"/>\n    <text x="442" y="250" text-anchor="middle" class="dg-note">Q at h₂</text>\n  </g>\n</svg>'},

    {t:'p', h:'Unit 13 ended by showing what the top half of that picture costs: two exact ownership claims about different addresses, conjoined with <code>aAnd</code>, are both handed the whole heap, and no heap can answer to both. The bottom half is the repair, and it is a different connective, not a patched one.'},

    /* ================================================================= build === */

    {t:'sec', s:'Building a star: you choose the cut'},

    {t:'p', h:'Suppose you have everything a star wants — two heaps, a proof they do not overlap, a proof that they combine to the heap in question, and a proof of each conjunct at its own half — and the goal is <code>(P ∗ Q) σ h</code>. That goal does not look like an existential. It looks like a name applied to two arguments, because <code>star</code> is a <code>def</code> and Lean displays the folded name. <code>show</code> restates it as what it is.'},

    {t:'state', cap:'The goal after <code>show ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>, with the four ingredients in the context above it. The bound <code>h₁ h₂</code> under the <code>∃</code> shadow the two already in scope; they are different variables and Lean is content, which is worth knowing before it surprises you.',
     src:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P σ h₁ ∧ Q σ h₂'},

    {t:'p', h:'Six slots, and Unit 01\'s flattening rule says a single <code>⟨…⟩</code> with six entries fills them: the anonymous constructor re-associates rightwards through nested pairs, and <code>∃ h₁ h₂, A ∧ B ∧ C ∧ D</code> is nested pairs all the way down. So the whole construction is one bracket, and no lemma is needed to build a star. That is the first of the two mechanical moves, and it is the exercise below.'},

    {t:'p', h:'The <code>show</code> is a readability device and comes out again: <code>exact ⟨h₁, h₂, hd, hu, hp, hq⟩</code> elaborates against the folded goal directly, because <code>show</code> changed nothing but the display.'},

    {t:'ex',
     id: 'x31',
     name: 'star_intro',
     why: 'This is the construction move with everything else removed, and it is the shape of every star you will ever prove: choose two heaps, discharge disjointness, discharge the equation, prove each side. It is packaged as a named theorem so that later proofs can hand over four ingredients without writing the bracket out, and so that this page can say, honestly, that building a star needs no syntax you did not have in Unit 01.',
     setup: 'Everything the definition asks for is already a hypothesis, in the order the definition asks for it. Nothing has to be discovered; the exercise is to see that the goal is a tuple.',
     goal: 'theorem star_intro {P Q : Assertion} {σ : Store} {h h₁ h₂ : Heap}\n    (hd : Heap.disjoint h₁ h₂) (hu : h = Heap.union h₁ h₂)\n    (hp : P σ h₁) (hq : Q σ h₂) : (P ∗ Q) σ h :=',
     hints: [
       'The goal <code>(P ∗ Q) σ h</code> is a folded <code>def</code>. Unfolded it reads <code>∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>: two heaps to be produced, and then four claims about them. The <code>h₁</code> and <code>h₂</code> bound by that <code>∃</code> are not the two in your context — they are fresh binders that happen to be spelled the same way.',
       'To prove that two heaps with four properties exist you have to say which two heaps. Nothing has to be searched for: the statement already hands you a pair carrying all four properties, so name that pair, and then the four remaining obligations are the four hypotheses, one each, in the order the definition lists them.',
       'The anonymous constructor <code>⟨…⟩</code>, flat. Unit 01 established that it re-associates rightwards, so you do not have to write the nesting the type has.',
       'The whole proof is <code>⟨h₁, h₂, …⟩</code> and then the four hypotheses in the order the definition lists them. The statement ends <code>:=</code>, not <code>:= by</code>, so no tactic block is involved.'
     ],
     sol: 'theorem star_intro {P Q : Assertion} {σ : Store} {h h₁ h₂ : Heap}\n    (hd : Heap.disjoint h₁ h₂) (hu : h = Heap.union h₁ h₂)\n    (hp : P σ h₁) (hq : Q σ h₂) : (P ∗ Q) σ h :=\n  ⟨h₁, h₂, hd, hu, hp, hq⟩',
     solNote: 'One line, and the only positive fact about <code>∗</code> this unit proves. Everything after it says either what a star cannot do, or what happens to a connective that is not one.',
     expl: 'The goal is an existential over a chain of conjunctions, so its proof is a tuple. Lean checks the tuple against the type by pairing off entries from the left and nesting whatever is left over, which is exactly the shape the type has, so the flat bracket is accepted with no nesting written down.',
     walk: [
       {tac: '⟨h₁, h₂, hd, hu, hp, hq⟩', h: 'The first two entries fix the cut — this is where the creative act would be, if the hypotheses had not already named it. The remaining four discharge the four conjuncts in order: they do not overlap, they combine to <code>h</code>, <code>P</code> holds on the left, <code>Q</code> on the right.'}
     ],
     deep: [
       {t:'trace', title:'What the goal is, before and after the display is changed',
        start:'⊢ (P ∗ Q) σ h',
        steps:[
          {tac:'(the goal as stated)',
           state:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ (P ∗ Q) σ h',
           h:'Lean prints <code>Heap.disjoint h₁ h₂</code> as <code>h₁.disjoint h₂</code> and <code>Heap.union h₁ h₂</code> as <code>h₁.union h₂</code>. The hypotheses are the four the tuple will consume.'},
          {tac:'show ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂',
           state:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ ∃ h₁ h₂, h₁.disjoint h₂ ∧ h = h₁.union h₂ ∧ P σ h₁ ∧ Q σ h₂',
           h:'Optional, and not in the solution — <code>show</code> changes the display and nothing else. It is worth typing once, because it is the only way to see the six slots you are about to fill.'}
        ],
        done:'exact ⟨h₁, h₂, hd, hu, hp, hq⟩ closes it either way.'},
       {t:'code', tag:'illustration', cap:'The nesting the type actually has, written out. Accepted, and never worth writing.',
        src:'example {P Q : Assertion} {σ : Store} {h h₁ h₂ : Heap}\n    (hd : Heap.disjoint h₁ h₂) (hu : h = Heap.union h₁ h₂)\n    (hp : P σ h₁) (hq : Q σ h₂) : (P ∗ Q) σ h :=\n  ⟨h₁, h₂, ⟨hd, ⟨hu, ⟨hp, hq⟩⟩⟩⟩'}
     ],
     pitfall: 'Supplying five entries instead of six — forgetting that <b>both</b> heaps are witnesses. <code>⟨h₁, hd, hu, hp, hq⟩</code> reports <code>Application type mismatch: The argument hd has type h₁.disjoint h₂ of sort `Prop` but is expected to have type Heap of sort `Type`</code>, because the second slot of the outer existential wants the second heap and got a proof instead. The message names the slot that went wrong, and counting the entries against the definition fixes it.',
     variants: 'Drop <code>hd</code> and the theorem does not become harder, it becomes <b>false</b>, and the counterexample is already on this page: take <code>P</code> and <code>Q</code> both to be <code>0 ↦ 4</code> and both halves to be <code>Heap.singleton 0 4</code>. The union equation holds by <code>union_self</code>, both ownership claims hold by <code>rfl</code> — and the conclusion <code>((0 ↦ 4) ∗ (0 ↦ 4)) σ (Heap.singleton 0 4)</code> is exactly what <code>x32</code> refutes. Nothing in the remaining hypotheses says the two halves fail to overlap, and <code>Heap.union</code> is defined for overlapping heaps too. Drop <code>hu</code> instead and it is false for a different reason: <code>h</code> is now an unrelated heap. Take both conjuncts to be <code>emp</code>, both halves <code>Heap.empty</code>, and <code>h</code> the singleton at 0 — the hypotheses are all satisfied and the conclusion claims a one-cell heap is the union of two empty ones. Reverse <code>hu</code> to <code>Heap.union h₁ h₂ = h</code> and nothing is false, only misaligned: the tuple is rejected at its fourth entry with <code>The argument hu has type h₁.union h₂ = h but is expected to have type h = h₁.union h₂</code>. The repair is <code>hu.symm</code>, and Unit 15 spends a whole discipline on which way round an equation slot wants its argument.'
    },

    {t:'p', h:'With that in hand, a two-cell heap satisfies the separating conjunction of the two claims that Unit 13\'s closing exhibit showed <code>aAnd</code> could not hold at once. The cut is the one the heap was written as, the disjointness is Unit 08\'s <code>singleton_disjoint</code>, and all three remaining slots are <code>rfl</code>: the heap <i>is</i> the union of the two singletons by construction, and each singleton <i>is</i> what its own <code>↦</code> asserts it to be.'},

    {t:'code', tag:'illustration', cap:'The first satisfiable two-cell assertion in the course.',
     src:'example : (((0 : Loc) ↦ 4) ∗ ((1 : Loc) ↦ 7)) (fun _ => 0)\n    (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) :=\n  star_intro (singleton_disjoint 4 7 (by simp)) rfl rfl rfl'},

    /* =============================================================== consume === */

    {t:'sec', s:'Using a star: the cut is chosen for you'},

    {t:'p', h:'The other direction is where the existential bites. A hypothesis of type <code>(P ∗ Q) σ h</code> tells you that <i>some</i> cut exists. It does not tell you which, and no tactic can find out, because the assertion is true of every heap that has any such cut at all. What you get is two heaps with no other description, and four facts about them.'},

    {t:'p', h:'An entailment out of a star therefore opens with one <code>intro</code> taking three things: the store, the heap, and a six-name pattern for the premise. The pattern destructures through the folded <code>def</code> exactly as <code>obtain</code> did against <code>Heap.splits</code> in Unit 11.'},

    {t:'trace', title:'One intro, six names',
     start:'⊢ P ∗ Q ⊢ aTrue',
     steps:[
       {tac:'intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩',
        state:'P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhp : P σ h₁\nhq : Q σ h₂\n⊢ aTrue σ h',
        h:'Three binders come from <code>⊢</code> — the store, the heap, and the premise — and the premise is taken apart on arrival. The context is now identical to <code>star_intro</code>\'s, which is the point: what one move produces, the other consumes.'}
     ],
     done:'What happens next depends entirely on P and Q.'},

    {t:'p', h:'Read the context and ask what is known about <code>h₁</code>. That it does not overlap <code>h₂</code>; that the two together are <code>h</code>; and that <code>P</code> holds at it. Nothing else. If <code>P</code> is an exact ownership claim, the third fact is an equation and pins <code>h₁</code> down completely — which is why the proofs on this page all begin by spending it. If <code>P</code> is something looser, the cut stays vague and the proof has to work with the two structural facts alone.'},

    /* ============================================================== deletion === */

    {t:'sec', s:'What each conjunct is holding up'},

    {t:'p', h:'A definition with four components invites the question of which of them are load-bearing. The two that are about heaps rather than about <code>P</code> and <code>Q</code> both are, and they hold up different things — which is easier to see by deleting one at a time than by arguing about the whole.'},

    {t:'h4', s:'Delete the equation'},

    {t:'p', h:'Without <code>h = Heap.union h₁ h₂</code> the cut is no longer a cut of anything. The two heaps still exist and still satisfy the conjuncts, but nothing ties them to the heap the assertion is evaluated at — so the heap argument is not used, and the assertion says only that <code>P</code> and <code>Q</code> are satisfiable somewhere by non-overlapping heaps. That is a statement about the world, not about what you hold.'},

    {t:'code', tag:'illustration', cap:'Delete the equation and owning nothing entails owning two cells. The heap binder in <code>starNoEq</code> is an underscore because nothing in the body could use it; the entailment\'s premise is discarded for the same reason.',
     src:'def starNoEq (P Q : Assertion) : Assertion :=\n  fun σ _ => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂\n\nexample : emp ⊢ starNoEq (0 ↦ 4) (1 ↦ 7) := by\n  intro σ h _\n  exact ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl⟩'},

    {t:'p', h:'Every other component describes the pieces; this one says the pieces are what you have.'},

    {t:'h4', s:'Delete disjointness'},

    {t:'p', h:'The other deletion leaves the connective a claim about the heap in hand and destroys what it claims. <code>Heap.union</code> is total and left-biased, so two heaps that both define an address combine perfectly happily, with the left one winning. Delete the disjointness conjunct and a one-cell heap will pass as the combination of that cell with a different value stored at the same address.'},

    {t:'code', tag:'verified', cap:'The connective without its disjointness requirement. It is in the corpus because the last exercise of this unit is about it.',
     src:'def starNoDisj (P Q : Assertion) : Assertion :=\n  fun σ h => ∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂'},

    {t:'code', tag:'illustration', cap:'A heap holding <code>4</code> at address 0, satisfying “address 0 holds 4, and separately address 0 holds 7”. The middle obligation is closed by hand because no lemma states it: at address 0 the left heap wins, and everywhere else both are silent.',
     src:'example : starNoDisj (0 ↦ 4) (0 ↦ 7) (fun _ => 0) (Heap.singleton 0 4) := by\n  refine ⟨Heap.singleton 0 4, Heap.singleton 0 7, ?_, rfl, rfl⟩\n  funext l\n  by_cases hl : l = 0\n  · rw [hl, union_of_some (Heap.singleton 0 7) (singleton_same 0 4), singleton_same]\n  · rw [union_of_none (Heap.singleton 0 7) (singleton_other 0 l 4 hl),\n        singleton_other 0 l 7 hl, singleton_other 0 l 4 hl]'},

    {t:'p', h:'Unit 08 proved that two singletons are disjoint only when their addresses differ, and called the result <i>separation implies non-aliasing</i>. That theorem is the reason the disjointness conjunct is there, and the exhibit above is what its absence costs: a connective that says <i>separately</i> and does not mean it. There is a second cost, and it is the sharper one, but it needs the failures below before it can be stated.'},

    /* ============================================================= same loc === */

    {t:'sec', s:'The same address, twice'},

    {t:'p', h:'The first theorem is the aliasing exhibit turned into a proof about the real connective. Claim address <code>l</code> with <code>v₁</code>, and separately claim address <code>l</code> with <code>v₂</code>: the two halves both contain <code>l</code>, so they overlap, so the disjointness conjunct is false and no heap satisfies the conjunction. The values need not differ. It is the addresses that collide.'},

    {t:'p', h:'The proof is three lines and spends nothing later than Unit 08. Destructure; use each ownership hypothesis as the equation it is, replacing both heap variables by singletons; then hand the disjointness proof to <code>singleton_disjoint_iff</code>, which converts it into <code>l ≠ l</code>, and apply that to <code>rfl</code>.'},

    {t:'ex',
     id: 'x32',
     name: 'star_same_loc_absurd',
     why: 'This is the consumption move on its first real target, and the first time <code>singleton_disjoint_iff</code> is spent — the <code>↔</code> Unit 08 proved and then had no use for. It is also, line for line, Unit 17\'s non-aliasing theorem: that proof is these three lines with the final <code>rfl</code> removed, so that what comes out is the disequality itself rather than the contradiction it produces. Prove this one and you have written that one.',
     setup: 'Two claims on one address, conjoined separately. The conclusion is <code>aFalse</code>, so the goal after <code>intro</code> is <code>aFalse σ h</code>, which unfolds to <code>False</code> — anything that produces a contradiction closes it.',
     goal: 'theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :\n    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by',
     hints: [
       'Unfolded, the premise says: there are heaps <code>h₁</code> and <code>h₂</code> that do not overlap, whose union is <code>h</code>, with <code>h₁ = Heap.singleton l v₁</code> and <code>h₂ = Heap.singleton l v₂</code>. The goal is <code>False</code>.',
       'Two singletons at the same address are not disjoint, and one of your hypotheses says they are. Replace the two heap variables by the singletons they are equal to, and the disjointness hypothesis becomes a false statement about two singletons at one address.',
       '<code>intro</code> with a six-name pattern, then <code>subst</code> on each ownership hypothesis, then <code>singleton_disjoint_iff</code> — whose forward direction turns disjointness of two singletons into a disequality between their addresses.',
       'Open with <code>intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩</code>. That leaves <code>hd : h₁.disjoint h₂</code>, <code>hp : (l ↦ v₁) σ h₁</code>, <code>hq : (l ↦ v₂) σ h₂</code> and the goal <code>aFalse σ h</code>. The union equation is the one component you never touch, so it is an underscore.'
     ],
     sol: 'theorem star_same_loc_absurd (l : Loc) (v₁ v₂ : Val) :\n    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩\n  subst hp; subst hq\n  exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl',
     solNote: 'Three lines, and only the last one mentions a lemma. The underscore in the pattern is a fact about the theorem, not a shortcut: no proof that two ownership claims collide will ever look at how the heap was cut.',
     expl: 'The premise supplies a disjointness proof for two heaps and, separately, equations identifying both of them as singletons at the same address. <code>subst</code> pushes the equations into the disjointness proof, which then has the exact shape <code>singleton_disjoint_iff</code> talks about. Its forward direction reads off <code>l ≠ l</code>, and a disequality is a function into <code>False</code>, so applying it to <code>rfl</code> is the contradiction.',
     walk: [
       {tac: 'intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩', h: 'Three binders from <code>⊢</code> and then the premise opened on arrival. The goal drops from an entailment to <code>aFalse σ h</code>, and six things enter the context — five of them named, one deliberately not.'},
       {tac: 'subst hp', h: 'Nothing about <code>hp</code>\'s displayed type looks like an equation, but <code>(l ↦ v₁) σ h₁</code> <i>is</i> <code>h₁ = Heap.singleton l v₁</code>, so <code>subst</code> deletes <code>h₁</code> and puts the singleton wherever it stood — including inside <code>hd</code>, which is the only place that matters.'},
       {tac: 'subst hq', h: 'The same for the other half. Now <code>hd</code> asserts that two singletons at address <code>l</code> do not overlap, and both heap variables are gone from the context.'},
       {tac: 'exact ((singleton_disjoint_iff v₁ v₂).mp hd) rfl', h: '<code>.mp</code> takes the forward direction of Unit 08\'s <code>↔</code>, which converts that disjointness into <code>l ≠ l</code>. A disequality is a function from a proof of the equation to <code>False</code>, so feeding it <code>rfl</code> produces the <code>False</code> the goal wants.'}
     ],
     deep: [
       {t:'trace', title:'The two heap variables leaving the context',
        start:'⊢ l ↦ v₁ ∗ l ↦ v₂ ⊢ aFalse',
        steps:[
          {tac:'intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩',
           state:'l : Loc\nv₁ v₂ : Val\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nleft✝ : h = h₁.union h₂\nhp : (l ↦ v₁) σ h₁\nhq : (l ↦ v₂) σ h₂\n⊢ aFalse σ h',
           h:'The underscore did not discard the union equation — it kept it under an inaccessible name, <code>left✝</code>, which is Lean\'s field name for the first component of the conjunction. It is in the context and cannot be typed, which is exactly what an underscore means.'},
          {tac:'subst hp; subst hq',
           state:'l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nhd : (Heap.singleton l v₁).disjoint (Heap.singleton l v₂)\nleft✝ : h = (Heap.singleton l v₁).union (Heap.singleton l v₂)\n⊢ aFalse σ h',
           h:'Both heap variables are gone and both substitutions reached inside <code>hd</code>. The hypothesis is now literally the left-hand side of <code>singleton_disjoint_iff</code> at <code>l₁ = l₂ = l</code>.'}
        ],
        done:'One application closes it.'},
       {t:'code', tag:'verified', cap:'The same theorem with a different last line, and it is in the corpus under its own name. <code>absurd</code> takes the fact and its refutation; <code>by simp</code> proves <code>¬ (l ≠ l)</code>. Two spellings of one step.',
        src:'theorem star_pointsTo_same_false (l : Loc) (v₁ v₂ : Val) :\n    (l ↦ v₁) ∗ (l ↦ v₂) ⊢ aFalse := by\n  intro σ h ⟨h₁, h₂, hd, _, hp, hq⟩\n  subst hp; subst hq\n  exact absurd ((singleton_disjoint_iff v₁ v₂).mp hd) (by simp)'},
       {t:'p', h:'A third route avoids <code>subst</code> altogether: <code>rw [hp, hq] at hd</code> rewrites the two equations into the disjointness hypothesis and leaves the heap variables in the context, unused. It compiles, and it is one line longer in effect, because the variables it leaves behind are then dead weight in every goal display for the rest of the proof.'}
     ],
     pitfall: 'Writing five names in the pattern instead of six. <code>intro σ h ⟨h₁, h₂, hd, hp, hq⟩</code> is <b>accepted</b> — flattening stops one level earlier, nothing is reported — and the last two names silently shift onto the wrong components: <code>hp</code> becomes the union equation <code>h = h₁.union h₂</code> and <code>hq</code> becomes the whole remaining conjunction <code>(l ↦ v₁) σ h₁ ∧ (l ↦ v₂) σ h₂</code>. The next line then half-succeeds, which is what makes this hard to see: <code>subst hp</code> works, because <code>hp</code> genuinely is an equation — it eliminates <code>h</code> and quietly changes the goal to <code>aFalse σ (h₁.union h₂)</code> — and only <code>subst hq</code> fails, with <code>Tactic `subst` failed: did not find equation for eliminating \'hq\'</code>. The message names <code>hq</code> and says nothing about the pattern, and the tactic that actually consumed the wrong hypothesis has already reported success. When a destructuring goes wrong, count the components of the definition before reading the message.',
     variants: 'Require <code>v₁ ≠ v₂</code> as a hypothesis and the theorem is still true and the proof is unchanged — the hypothesis is never used, and Lean will warn that it is unused. That is the content of the theorem: the values are irrelevant, and even the <i>same</i> claim twice over is contradictory, which is exactly what fails in the no-contraction exercise below. Change the second conjunct to a different address, <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ aFalse</code> with <code>l₁ ≠ l₂</code>, and the statement becomes false: <code>singleton_disjoint</code> proves the two halves disjoint and the compiled example above exhibits a heap satisfying it. Replace <code>∗</code> by <code>aAnd</code> and the statement becomes <b>false</b> as written: with <code>v₁ = v₂</code> both conjuncts are the same claim and the singleton at <code>l</code> satisfies both, so <code>aAnd (l ↦ v) (l ↦ v) ⊢ aFalse</code> has a compiled refutation. Unit 13\'s classical version needed the addresses or the values to differ. The separating version needs neither, and that is the sharpest way to state what disjointness adds.'
    },

    /* ========================================================== refutations === */

    {t:'sec', s:'Refutations cost more than proofs'},

    {t:'p', h:'Everything after this point is a negation, and negations are worked in the opposite direction. To prove an entailment you are handed an arbitrary state and reason forwards. To refute one you must produce the state, and nothing in the goal suggests it. <code>pointsTo_not_emp</code> had one heap worth trying. Between them the two below ask you to choose an assertion to instantiate at, a heap to supply, a cut of that heap to name and an address to evaluate at — and a wrong choice at any of the four leaves you holding something true and useless rather than an error message, which is the one kind of stuck Lean will not help you out of. That is why they are the hardest exercises in the module so far.'},

    /* ============================================================ weakening === */

    {t:'sec', s:'No weakening'},

    {t:'p', h:'Unit 12 proved <code>and_left : aAnd P Q ⊢ P</code> in one line, and the line was <code>fun _ _ h => h.1</code>. It is a projection: a conjunction is a pair, and you are entitled to the first component whenever you want it. The corresponding statement for <code>∗</code> is one character different and is false.'},

    {t:'cmp',
     left: {t:'Classical conjunction — proved in Unit 12', kind:'good',
            h:'A pair, projected. Both conjuncts were asked about the same heap, so discarding one of them changes nothing about what is being claimed of that heap.',
            src:'theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1'},
     right:{t:'Separating conjunction — refuted below', kind:'bad', tag:'sketch',
            h:'Not a pair, and there is no proof to write: the statement is false. <code>P ∗ Q</code> at <code>h</code> says <code>h</code> is <i>both</i> pieces; <code>P</code> at <code>h</code> says <code>h</code> is the left piece alone. Dropping <code>Q</code> silently changes the claim about how much memory you are holding.',
            src:'example (P Q : Assertion) : P ∗ Q ⊢ P'}},

    {t:'p', h:'The Lean below refutes one instance; the argument above is why every instance fails. Take <code>P</code> to be <code>0 ↦ 4</code> and <code>Q</code> to be <code>1 ↦ 7</code>. The premise is satisfied by the two-cell heap of the compiled example above — the union of the two singletons. The conclusion, at that same heap, says the heap <i>is</i> the single cell at address 0 — and address 1 is where that falls over, because the two-cell heap answers <code>some 7</code> there and a one-cell heap at address 0 answers <code>none</code>.'},

    {t:'ex',
     id: 'x33',
     name: 'no_star_weakening',
     hard: true,
     why: 'This is the frame rule\'s reason to exist. If a precondition mentioning a cell the command never touches could be thinned away, verifying a command inside a larger heap would be free and there would be nothing to prove. It cannot, so the untouched part has to be carried through every proof by a rule written for the purpose — and Units 23, 27 and 34 all argue from this theorem by name. No later Lean proof cites it; what it supports is an argument rather than a proof term, which is why it is referred to by name and never by application.',
     setup: 'Two cells at distinct addresses, and the claim that the conjunction of both entails the first. You choose the state; everything else follows from it. <code>congrFun</code> is Unit 03\'s converse of <code>funext</code> and reaches through the folded <code>↦</code>, as it did in Unit 07.',
     goal: 'theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by',
     hints: [
       'The goal is <code>¬ (…)</code>, which is <code>(…) → False</code>. So the first move gives you the entailment as a hypothesis and leaves you to derive <code>False</code>. An entailment is a function of three arguments: a store, a heap, and a proof of the premise at that state.',
       'Pick the state that makes the premise easiest to supply — the heap that <i>is</i> the two cells. Apply the entailment there. What comes back says that heap is the single cell at address 0. Now find an address where those two heaps disagree.',
       '<code>star_intro</code>\'s four ingredients, or the six-slot bracket written out, to supply the premise; <code>congrFun</code> to evaluate the resulting heap equation at an address; <code>union_of_none</code>, <code>singleton_same</code> and <code>singleton_other</code> to compute both sides there.',
       'Open with <code>intro hall</code>, leaving <code>hall</code> the entailment and <code>⊢ False</code>. Then <code>have h := hall (fun _ => 0) (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7)) ⟨…⟩</code>, where the bracket is the six-slot premise. Address 1 is the one that works; address 0 gives you <code>some 4 = some 4</code>.'
     ],
     sol: 'theorem no_star_weakening : ¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)) := by\n  intro hall\n  have h := hall (fun _ => 0) (Heap.union (Heap.singleton 0 4) (Heap.singleton 1 7))\n    ⟨Heap.singleton 0 4, Heap.singleton 1 7, singleton_disjoint 4 7 (by simp), rfl, rfl, rfl⟩\n  have h1 := congrFun h 1\n  rw [union_of_none (Heap.singleton 1 7) (singleton_other 0 1 4 (by simp)),\n      singleton_same, singleton_other 0 1 4 (by simp)] at h1\n  exact absurd h1 (by simp)',
     solNote: 'Five lines, of which one is the choice of witness and three are arithmetic on that witness. If you climbed all four hints and are still stuck, open this: the hard part is knowing that the state has to be chosen before anything can be computed, and that is a thing to be shown once rather than discovered.',
     expl: 'Assume the entailment. Apply it at the two-cell heap, with the premise supplied by naming the cut explicitly. What returns is a claim that the two-cell heap equals the one-cell heap at address 0. Evaluate that equation at address 1 with <code>congrFun</code>: the left side is the union, whose left half is silent at 1, so it reads through to <code>some 7</code>; the right side is a singleton at 0, which is <code>none</code> at 1. <code>some 7 = none</code> is the contradiction.',
     walk: [
       {tac: 'intro hall', h: 'Turns the negation into a hypothesis plus <code>⊢ False</code>. From here the entailment is an assumption to be used, not a goal to be proved — the goal has become a search for something impossible.'},
       {tac: 'have h := hall (fun _ => 0) (Heap.union …) ⟨…⟩', h: 'Applies the entailment at a state of your choosing. The store is arbitrary and picked to be constant zero; the heap is the union of the two singletons; the third argument is the premise, supplied as the six-slot bracket with the cut named. Three of the six entries are <code>rfl</code>, because the heap was built to make them so. What comes back, <code>h</code>, is the conclusion at that heap: an equation between two heaps.'},
       {tac: 'have h1 := congrFun h 1', h: 'Evaluates the heap equation at address 1, turning an equation between functions into an equation between two <code>Option Val</code> values. Address 1 is the choice that makes the proof work; address 0 gives <code>some 4 = some 4</code> and closes nothing.'},
       {tac: 'rw [union_of_none …, singleton_same, singleton_other …] at h1', h: 'Computes both sides. <code>union_of_none</code> needs to know the left half is silent at 1, which <code>singleton_other</code> supplies; then <code>singleton_same</code> reads <code>some 7</code> off the right half, and a second <code>singleton_other</code> reads <code>none</code> off the conclusion\'s singleton. <code>h1</code> becomes <code>some 7 = none</code>.'},
       {tac: 'exact absurd h1 (by simp)', h: 'A constructor equation between <code>some</code> and <code>none</code> is refuted by <code>simp</code>, and <code>absurd</code> pairs the fact with its refutation to produce <code>False</code>.'}
     ],
     deep: [
       {t:'trace', title:'Four steps, and the hypothesis narrowing at each',
        start:'⊢ ¬0 ↦ 4 ∗ 1 ↦ 7 ⊢ 0 ↦ 4',
        steps:[
          {tac:'intro hall',
           state:'hall : 0 ↦ 4 ∗ 1 ↦ 7 ⊢ 0 ↦ 4\n⊢ False',
           h:'The starting goal is printed without a single bracket, and reads as four symbols in a row; <code>¬</code> takes an argument at level 40 and <code>⊢</code> sits at exactly 40, so it swallows the whole entailment and the display is <code>¬((0 ↦ 4 ∗ 1 ↦ 7) ⊢ (0 ↦ 4))</code>. After <code>intro</code> the whole statement is one hypothesis and there is no goal left to analyse. Everything from here is forward reasoning out of <code>hall</code>.'},
          {tac:'have h := hall (fun _ => 0) (Heap.union …) ⟨…⟩',
           state:'hall : 0 ↦ 4 ∗ 1 ↦ 7 ⊢ 0 ↦ 4\nh : (0 ↦ 4) (fun x => 0) ((Heap.singleton 0 4).union (Heap.singleton 1 7))\n⊢ False',
           h:'<code>h</code> reads: the union of the two singletons satisfies <code>0 ↦ 4</code>. That is the false thing, and it is still folded — <code>(0 ↦ 4) σ h</code> rather than the equation it is.'},
          {tac:'have h1 := congrFun h 1',
           state:'hall : 0 ↦ 4 ∗ 1 ↦ 7 ⊢ 0 ↦ 4\nh : (0 ↦ 4) (fun x => 0) ((Heap.singleton 0 4).union (Heap.singleton 1 7))\nh1 : (Heap.singleton 0 4).union (Heap.singleton 1 7) 1 = Heap.singleton 0 4 1\n⊢ False',
           h:'<code>congrFun</code> looked straight through the folded <code>↦</code> and found the equation between functions underneath it, then applied both sides to 1. Neither side has been computed yet.'},
          {tac:'rw [union_of_none …, singleton_same, singleton_other …] at h1',
           state:'hall : 0 ↦ 4 ∗ 1 ↦ 7 ⊢ 0 ↦ 4\nh : (0 ↦ 4) (fun x => 0) ((Heap.singleton 0 4).union (Heap.singleton 1 7))\nh1 : some 7 = none\n⊢ False',
           h:'Three rewrites, one per side and one to license the first. The witness is now a single false equation between two constructors.'}
        ],
        done:'exact absurd h1 (by simp)'},
       {t:'p', h:'The three <code>rfl</code>s in the premise bracket are worth a second look, because they are <code>rfl</code> for two different reasons. The two ownership claims are about the <i>halves</i>, and the halves were named as the very singletons the two <code>↦</code>s unfold to, so those two stay <code>rfl</code> whatever <code>h</code> is. The equation is <code>rfl</code> only because <code>h</code> was spelled as the union of those halves. Spell the same heap as <code>Heap.write (Heap.singleton 0 4) 1 7</code> and exactly that one entry breaks — <code>The argument rfl … is expected to have type (Heap.singleton 0 4).write 1 7 = (Heap.singleton 0 4).union (Heap.singleton 1 7)</code> — and repairing it costs a <code>funext</code> and a two-way <code>by_cases</code>, nine lines to prove two spellings of one heap equal. Choosing the witness includes choosing how to spell it.'}
     ],
     pitfall: 'Evaluating at address 0. It is the address the conclusion is about, so it is the natural first choice, and it gives <code>h1 : some 4 = some 4</code> — true, useless, and the subsequent <code>absurd</code> fails with <code>unsolved goals … ⊢ False</code> rather than with anything that names the mistake. The entailment fails because of the memory it <i>forgets</i>, so the refutation has to be found at an address the conclusion never mentions.',
     variants: 'Swap the conclusion to the other conjunct — <code>¬ ((0 ↦ 4) ∗ (1 ↦ 7) ⊢ (1 ↦ 7))</code> — and it is equally false, by the same proof with address 0 in place of address 1 and <code>union_of_some</code> in place of <code>union_of_none</code>. Weaken the conclusion to <code>aTrue</code> and the entailment becomes true and trivial, which is the boundary: you may forget what an assertion <i>says</i>, never what it <i>owns</i>. Replace <code>∗</code> by <code>aAnd</code> and the statement becomes false as a negation, because <code>and_left</code> proves the entailment it denies — the one-character difference is the whole of this unit.'
    },

    /* ========================================================== contraction === */

    {t:'sec', s:'No contraction'},

    {t:'p', h:'The other classical entitlement is duplication. In Unit 12, <code>P ⊢ aAnd P P</code> is <code>fun _ _ hp => ⟨hp, hp⟩</code>: one proof, used twice, and the heap is unchanged because both conjuncts are asked about it. For <code>∗</code> the corresponding statement fails, and it fails at a component you can name.'},

    {t:'p', h:'Suppose <code>P ⊢ P ∗ P</code> held for every <code>P</code>. Take a heap <code>h</code> satisfying an exact ownership claim and apply the entailment there: you get two heaps whose union is <code>h</code>, each satisfying the same exact claim, and a proof that they do not overlap. But an exact claim pins its heap down, so both halves <i>are</i> <code>h</code> — and Unit 08\'s <code>self_disjoint_iff_empty</code> says a heap that does not overlap itself is empty. A one-cell heap is not empty. The contradiction is at the disjointness conjunct, and it is at no other.'},

    {t:'ex',
     id: 'x34',
     name: 'no_star_duplication',
     hard: true,
     why: 'Duplicating a hypothesis is so routine in ordinary reasoning that its absence is invisible until someone states it. This is the statement, and it is what makes <code>∗</code> a connective about resources rather than a conjunction with a side condition: a proof may not spend the same cell twice, because there is only one of it. It is also the rule you will feel from Unit 23 on: each conjunct of a precondition is spent once, so a specification that needs a cell twice has to say so twice, and nothing in the logic will supply the second copy.',
     setup: 'A negated universal. The <code>P</code> you instantiate at is yours to choose, and the choice decides how hard the rest is. <code>self_disjoint_iff_empty</code> is available and so is <code>singleton_disjoint_iff</code>; the solution takes the second route because it needs no <code>Heap.empty</code> anywhere.',
     goal: 'theorem no_star_duplication : ¬ (∀ P : Assertion, P ⊢ P ∗ P) := by',
     hints: [
       'The goal is <code>¬ (∀ P, P ⊢ P ∗ P)</code>, so after the first move you hold a hypothesis that is a function: give it an assertion and it gives you an entailment. You have to derive <code>False</code>. Nothing in the goal names an assertion, so you choose one.',
       'Choose an assertion that pins its heap down exactly, and a heap satisfying it. The entailment then hands you a cut of that heap into two halves, each of which must satisfy the same exact claim — so each half is the whole heap. Two facts about that heap are now in conflict.',
       '<code>obtain</code> to open the star the entailment returns; then rewrite both halves to the singleton with <code>have</code> and <code>subst</code>; then <code>singleton_disjoint_iff</code>, exactly as in <code>x32</code>.',
       'Open with <code>intro hall</code>, then <code>obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl</code>. The final <code>rfl</code> is the premise: the singleton satisfies <code>4 ↦ 7</code> by definition. That leaves you with <code>hp</code> and <code>hq</code> saying both halves are that singleton.'
     ],
     sol: 'theorem no_star_duplication : ¬ (∀ P : Assertion, P ⊢ P ∗ P) := by\n  intro hall\n  obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl\n  have e1 : h₁ = Heap.singleton 4 7 := hp\n  have e2 : h₂ = Heap.singleton 4 7 := hq\n  subst e1; subst e2\n  exact ((singleton_disjoint_iff 7 7).mp hd) rfl',
     solNote: 'Six lines, and the last is <code>x32</code>\'s last line with the two values equal. That is not a coincidence: duplication asks for the same cell twice, which is the aliasing failure with both claims identical.',
     expl: 'Instantiate the supposed rule at an exact ownership claim and at the one heap satisfying it. The star it returns must cut that heap into two disjoint halves, each satisfying the same claim — so each half is the singleton. The disjointness proof then says the singleton does not overlap itself, and two singletons at one address are never disjoint.',
     walk: [
       {tac: 'intro hall', h: 'The negation becomes a hypothesis: <code>hall</code> is the rule, quantified over every assertion, and the goal is <code>False</code>.'},
       {tac: 'obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl', h: 'Four applications in one line — the assertion, the store, the heap, and the premise — and the six-slot result is destructured immediately. The premise is <code>rfl</code> because <code>(4 ↦ 7) σ (Heap.singleton 4 7)</code> unfolds to <code>Heap.singleton 4 7 = Heap.singleton 4 7</code>.'},
       {tac: 'have e1 : h₁ = Heap.singleton 4 7 := hp', h: 'Restates <code>hp</code> at the type it definitionally has. <code>subst</code> will act on an equation, and this is the cheapest way to hand it one whose type says so out loud. The proof term is <code>hp</code> unchanged.'},
       {tac: 'have e2 : h₂ = Heap.singleton 4 7 := hq', h: 'The same for the right half. Both halves of the cut are now known to be the entire heap.'},
       {tac: 'subst e1; subst e2', h: 'Deletes both heap variables and pushes the singleton into <code>hd</code>. <code>hd</code> now asserts that <code>Heap.singleton 4 7</code> does not overlap itself.'},
       {tac: 'exact ((singleton_disjoint_iff 7 7).mp hd) rfl', h: 'Both values are 7 and both addresses are 4, so the forward direction yields <code>4 ≠ 4</code>, and <code>rfl</code> refutes it.'}
     ],
     deep: [
       {t:'trace', title:'From a rule to a contradiction, in three states',
        start:'⊢ ¬∀ (P : Assertion), P ⊢ P ∗ P',
        steps:[
          {tac:'intro hall',
           state:'hall : ∀ (P : Assertion), P ⊢ P ∗ P\n⊢ False',
           h:'The universally quantified rule, as a hypothesis. Choosing what to instantiate it at is the whole exercise.'},
          {tac:'obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hall (4 ↦ 7) (fun _ => 0) (Heap.singleton 4 7) rfl',
           state:'hall : ∀ (P : Assertion), P ⊢ P ∗ P\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : Heap.singleton 4 7 = h₁.union h₂\nhp : (4 ↦ 7) (fun x => 0) h₁\nhq : (4 ↦ 7) (fun x => 0) h₂\n⊢ False',
           h:'The cut the rule promised. Note <code>hu</code>: the singleton is the union of the two halves. It is never used, because <code>hp</code> and <code>hq</code> already pin both halves down individually.'},
          {tac:'subst e1; subst e2',
           state:'hall : ∀ (P : Assertion), P ⊢ P ∗ P\nhp hq : (4 ↦ 7) (fun x => 0) (Heap.singleton 4 7)\nhd : (Heap.singleton 4 7).disjoint (Heap.singleton 4 7)\nhu : Heap.singleton 4 7 = (Heap.singleton 4 7).union (Heap.singleton 4 7)\n⊢ False',
           h:'<code>hd</code> is the false hypothesis: one heap, disjoint from itself, and not empty. <code>hp</code> and <code>hq</code> have collapsed to the same statement and Lean displays them on one line.'}
        ],
        done:'exact ((singleton_disjoint_iff 7 7).mp hd) rfl'},
       {t:'p', h:'The alternative ending is <code>self_disjoint_iff_empty</code>, which turns <code>hd</code> into <code>Heap.singleton 4 7 = Heap.empty</code> — and then that has to be refuted, which the one-line ending never had to do. By hand it is three lines: <code>congrFun</code> at address 4, <code>singleton_same</code> to read the left side, and <code>absurd</code> against <code>by simp [Heap.empty]</code>, because plain <code>simp</code> will not look inside <code>Heap.empty</code> and answers <code>simp made no progress</code>. Handing it to Unit 13\'s <code>pointsTo_not_emp</code> instead costs one line, <code>exact pointsTo_not_emp 4 7 (fun _ _ hx => hx.trans ((self_disjoint_iff_empty _).mp hd))</code>, because that theorem is the refutation already packaged. Either route says the more general thing about why duplication fails: an assertion can only be duplicated at heaps that are disjoint from themselves, and Unit 13 already proved that a heap owning a cell is not one of them.'},
       {t:'p', h:'The two <code>have</code>s can also be dropped: <code>subst hp; subst hq</code> closes the proof on its own, because <code>hp</code> already <i>is</i> the equation. They earn their place by putting the equation on the page in a form the reader can see, which is the same service <code>show</code> performs for a goal.'}
     ],
     pitfall: 'Instantiating at the wrong assertion, and then hunting for a contradiction that is not there. <code>hall emp</code> and <code>hall aTrue</code> both look like reasonable places to start, and both entailments are <b>true</b> — <code>emp ⊢ emp ∗ emp</code> and <code>aTrue ⊢ aTrue ∗ aTrue</code> each compile — so the proof will not close and nothing in the goal says why. A refutation is only as good as its witness, and the witness here has to be an assertion that <i>owns</i> something. If a refutation stalls, suspect the choice before the tactics.',
     variants: 'Drop the <code>∀</code> and state it at one assertion — <code>¬ ((4 ↦ 7) ⊢ (4 ↦ 7) ∗ (4 ↦ 7))</code> — and it is true, with the same proof minus the instantiation. It is a weaker statement and a better one to cite, because it names the assertion at fault. Now the other direction: contraction is <b>not</b> uniformly absent. <code>emp ⊢ emp ∗ emp</code> holds, with <code>Heap.empty</code> for both halves; and so does <code>aTrue ⊢ aTrue ∗ aTrue</code>, with <code>h</code> and <code>Heap.empty</code>. Both compile. So the theorem above is genuinely about the quantifier: <i>some</i> assertions duplicate, and the ones that do not are the ones that own something.'
    },

    {t:'p', h:'That last observation is where the disjointness conjunct comes back. It was deleted once already, to show that <code>starNoDisj</code> loses non-aliasing. The second cost is that it hands duplication straight back — for every assertion, with no hypotheses, in one <code>exact</code> — because <code>Heap.union h h = h</code> and there is no longer anything to check.'},

    {t:'ex',
     id: 'x35',
     name: 'starNoDisj_dup',
     why: 'A definition is understood when you can say which clause is responsible for which theorem. This exercise localises the failure of contraction to a single conjunct: put it back and duplication dies, take it out and duplication is a one-liner. Unit 09\'s <code>union_self</code> was proved with no application in sight; this is it.',
     setup: '<code>starNoDisj</code> is the connective of the section above — the definition of <code>∗</code> with the disjointness conjunct deleted, and nothing else changed. It is given; you prove it duplicable.',
     goal: 'theorem starNoDisj_dup (P : Assertion) : P ⊢ starNoDisj P P := by',
     hints: [
       'The goal is an entailment, so it is a claim about every store and every heap: whenever <code>P</code> holds at <code>h</code>, <code>starNoDisj P P</code> holds at that same <code>h</code>. Unfolded, that second half reads <code>∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ P σ h₂</code> — five slots this time, not six, because the disjointness conjunct is the one that has been deleted.',
       'You are choosing a cut, and you have exactly one heap to build it out of. Use it twice. Then the equation slot asks whether that heap is the union of itself with itself, and the two conjunct slots each ask for <code>P</code> at it, which you have.',
       '<code>union_self</code> from Unit 09, and the fact that it points the wrong way for the slot it has to fill.',
       'Open with <code>intro σ h hp</code>, then <code>exact ⟨h, h, …, hp, hp⟩</code>. The middle slot wants <code>h = Heap.union h h</code>; <code>union_self h</code> states the reverse.'
     ],
     sol: 'theorem starNoDisj_dup (P : Assertion) : P ⊢ starNoDisj P P := by\n  intro σ h hp\n  exact ⟨h, h, (union_self h).symm, hp, hp⟩',
     solNote: 'Two lines, for every assertion, with no hypothesis about <code>P</code> at all. Compare the six lines and the carefully chosen witness that the previous exercise needed to deny the same statement about <code>∗</code>.',
     expl: 'With the disjointness conjunct gone, the cut has nothing to satisfy except the union equation, and the union of a heap with itself is itself. So take the heap twice, and the same proof of <code>P</code> twice. The single subtlety is orientation: <code>union_self</code> concludes <code>Heap.union h h = h</code> and the slot wants the equation the other way round.',
     walk: [
       {tac: 'intro σ h hp', h: 'Three binders out of <code>⊢</code>. The goal becomes <code>starNoDisj P P σ h</code>, folded, and <code>hp : P σ h</code> is the only thing available to prove either conjunct with.'},
       {tac: 'exact ⟨h, h, (union_self h).symm, hp, hp⟩', h: 'The first two entries are the cut, and both are the whole heap — which is precisely what disjointness would have forbidden. The third fills the union equation, reversed with <code>.symm</code>. The last two are the same proof of <code>P</code>, offered twice: the resource has been copied.'}
     ],
     deep: [
       {t:'trace', title:'The five slots, once the display is unfolded',
        start:'⊢ P ⊢ starNoDisj P P',
        steps:[
          {tac:'intro σ h hp',
           state:'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ starNoDisj P P σ h',
           h:'One premise, one heap. The goal is folded, so nothing about the tuple you owe is visible yet.'},
          {tac:'show ∃ h₁ h₂, h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ P σ h₂',
           state:'P : Assertion\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ h₁ h₂, h = h₁.union h₂ ∧ P σ h₁ ∧ P σ h₂',
           h:'Five slots. The one that costs anything is the equation, and only because of the direction it wants.'}
        ],
        done:'exact ⟨h, h, (union_self h).symm, hp, hp⟩'},
       {t:'p', h:'Put the disjointness conjunct back and the same two lines fail, one entry earlier. Against <code>P ∗ P</code> the third entry of the bracket is asked for <code>h.disjoint h</code> rather than for the union equation: <code>The argument Eq.symm (union_self h) has type h = h.union h but is expected to have type h.disjoint h</code>, and the entry behind it is off by one and reports its own mismatch too. There is no repair, because filling that entry needs <code>Heap.disjoint h h</code>, which by <code>self_disjoint_iff_empty</code> holds only when <code>h</code> is empty. The exercise above and the one before it are the two halves of one fact.'}
     ],
     pitfall: 'Writing <code>union_self h</code> without <code>.symm</code>. The message is <code>The argument union_self h has type h.union h = h but is expected to have type h = h.union h</code>, which names both sides and is one of the clearest errors Lean produces — but it is easy to read past, because the two types differ only in order. The slot is <code>h = Heap.union h₁ h₂</code>, with <code>h</code> on the left, always.',
     variants: 'Delete the union equation as well and the connective stays duplicable for a second and worse reason: the heap argument is now unused, so <code>⟨h, h, hp, hp⟩</code> works and would have worked for any two heaps at all. Keep disjointness and delete only the equation — that is <code>starNoEq</code>, from the first of this unit\'s two deletions — and duplication dies again, because two copies of a non-empty heap still overlap: <code>¬ (∀ P, P ⊢ starNoEq P P)</code> holds, by <code>x34</code>\'s argument with one fewer name in the pattern. So disjointness is the conjunct that decides it, and it decides it in both directions. The converse, <code>starNoDisj P P ⊢ P</code>, is not only unproved — it is refutable: <code>¬ (∀ P, starNoDisj P P ⊢ P)</code> holds, and the witness is an assertion satisfied by two heaps separately but not by their union — <code>fun _ h => h = Heap.singleton 0 4 ∨ h = Heap.singleton 1 7</code>. Both singletons satisfy it, so they cut their union legitimately; their union satisfies it neither way round. The premise gives you <code>P</code> at two halves of <code>h</code> and nothing that transports either to <code>h</code> itself.'
    },

    /* ============================================================ the names === */

    {t:'sec', s:'Two names for the two failures'},

    {t:'p', h:'Both refutations are instances of something with a name, and the name is older than separation logic. Ordinary logic grants you moves that have nothing to do with the connectives — they are about the <i>hypotheses</i> rather than about what the hypotheses say — and they are called structural rules. Two of them are the two theorems above.'},

    {t:'dl', items:[
      {k:'Weakening', h:'The entitlement to add a hypothesis you do not use, or equivalently to discard one. <code>and_left</code> is its conjunctive form: from <code>P ∧ Q</code> conclude <code>P</code>, throwing <code>Q</code> away. Exercise <code>x33</code> is the statement that <code>∗</code> does not have it. The reason is not subtle: throwing away a conjunct would mean forgetting the memory it owns, and the memory does not go away because you stopped mentioning it.'},
      {k:'Contraction', h:'The entitlement to use a hypothesis twice, or equivalently to duplicate it. <code>P ⊢ aAnd P P</code> is its conjunctive form. Exercise <code>x34</code> is the statement that <code>∗</code> does not have it, and <code>x35</code> localises the refusal to one conjunct of the definition. Duplicating a resource would produce memory that does not exist.'},
      {k:'A substructural logic', h:'One in which at least one structural rule is dropped. Separation logic drops both of the above for <code>∗</code> — while keeping both for <code>aAnd</code>, which is still in the language and still has <code>and_left</code>. A resource-carrying conjunction and a truth-carrying one coexist, and choosing between them at each point in a specification is most of the skill of writing one.'}
    ]},

    {t:'p', h:'The slogan is that <code>∗</code> is <i>linear</i> in resources: each cell is owned once, by exactly one conjunct, and the count is preserved by every rule. Unit 12 said that lifting the classical connectives pointwise achieved nothing; this is what a connective that achieves something looks like, and the price of it is on this page.'},

    {t:'note', kind:'warn', title:'What the absence of weakening costs you next',
     h:'A specification is a precondition, a command and a postcondition. Suppose the precondition owns two cells and the command touches one of them. With weakening you would drop the untouched cell from the precondition, verify the command against what is left, and be done — the untouched cell would take care of itself. Exercise <code>x33</code> says you cannot: <code>(0 ↦ 4) ∗ (1 ↦ 7) ⊢ (0 ↦ 4)</code> is false, so the two-cell precondition does not entail the one-cell one and there is no way to get from the specification you want to the specification you can prove. So either every rule is stated at every heap it might ever run in — which is the aliasing disaster Unit 00 opened with — or there is a separate rule that takes a proof about a small heap and carries an untouched conjunct through it unchanged. That rule is the <b>frame rule</b>. Unit 23 states the primitive memory rules on exactly the cells they touch and then fails, deliberately, to compose two of them; Unit 27 proves the rule that repairs it.'},

    /* ========================================================== what bought === */

    {t:'sec', s:'What Unit 07\'s decision actually bought'},

    {t:'p', h:'It is tempting to credit exactness with everything on this page, since <code>↦</code> is exact and the refutations are about <code>↦</code>. It is the wrong reading: Module 1 decided exactness and Module 2 decided disjointness, independently of each other, and they pay for different theorems.'},

    {t:'p', h:'Non-aliasing comes from disjointness. Unit 08 proved that two singletons at the same address are not disjoint, <code>x32</code> spent that proof, and nothing in either argument required the assertions to be exact — the deleted-conjunct exhibit above shows it going wrong the moment disjointness leaves, with the exactness untouched. The absence of weakening is the part that comes from exactness. Under Unit 07\'s loose reading, <i>the cell holds this value and the heap may hold anything else besides</i>, weakening is provable, in three lines, for an arbitrary right conjunct.'},

    {t:'detail', title:'Weakening, proved — for the reading Unit 07 rejected', tag:'aside', open:false, blocks:[
      {t:'p', h:'<code>ptsAtLeast l v</code> is Unit 07\'s loose reading: <code>h l = some v</code>, with no claim about the rest of the heap. It is an <code>Assertion</code> like any other, so it can stand on the left of a <code>∗</code>, and the entailment that <code>x33</code> refutes for <code>↦</code> goes through for it without effort.'},
      {t:'code', tag:'illustration', cap:'Three lines, arbitrary <code>Q</code>, no hypotheses. The proof is exactly the reason the conclusion is provable: the left half holds <code>v</code> at <code>l</code>, and a left-biased union of anything onto it still answers <code>some v</code> there.',
       src:'example (l : Loc) (v : Val) (Q : Assertion) : ptsAtLeast l v ∗ Q ⊢ ptsAtLeast l v := by\n  intro σ h ⟨h₁, h₂, _, hu, hp, _⟩\n  subst hu\n  exact union_of_some h₂ hp'},
      {t:'p', h:'The single step that carries it is <code>union_of_some</code>. A loose claim survives being placed in a bigger heap, because it never said how big the heap was; an exact claim does not, because it did. Everything in <code>x33</code>\'s refutation happens at address 1 — an address the conclusion mentions only by insisting there is nothing there.'},
      {t:'p', h:'Had Unit 07 chosen the loose reading, <code>x32</code> and <code>x34</code> would both still go through — each needs disjointness and nothing else — and only <code>x33</code> would change, from a refutation into the three lines above. Weakening is the single theorem that turns on the choice, and it is the one the frame rule is about.'}
    ]},

    {t:'dod', h:'You can write the definition of <code>∗</code> and name its four components in order; say what breaks when the equation is deleted and what breaks when disjointness is deleted, with a compiled counterexample for each; build a star with a flat six-slot bracket and take one apart with a six-name <code>intro</code> pattern, and say why one of those is a choice and the other is not; prove that two ownership claims at one address are jointly unsatisfiable; refute <code>P ∗ Q ⊢ P</code> and read the address at which it fails; refute <code>∀ P, P ⊢ P ∗ P</code> and name the conjunct responsible, by deleting it and watching duplication return; define weakening, contraction and substructural logic; and say why the absence of weakening forces a rule that carries untouched memory through a proof.'},

    {t:'p', h:'A connective with no projection and no duplication. Whether it has anything at all is the next question: does it even have a unit? Is it commutative?'}

  ]
});
