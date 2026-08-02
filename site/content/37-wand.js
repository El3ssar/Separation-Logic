registerChapter({
  id: 'wand',
  num: '34',
  phase: 'Phase 7 · Unbounded structures',
  title: 'Giving a piece away, and getting it back',
  blurb: 'The connective that names what is left of an assertion when part of the memory it describes has been handed to someone else.',

  orient: {
    youWill: [
      'Read <code>P -∗ Q</code> aloud as a claim about the memory you are holding, and say which heap each of its three parts is about.',
      'Say why lifting <code>→</code> pointwise, the way Unit 12 lifted <code>∧</code> and <code>∨</code>, gives a connective whose modus ponens survives <code>aAnd</code> and fails across a <code>∗</code> — and exhibit the heap that refutes it.',
      'Prove <code>wand_intro</code> and <code>wand_elim</code>, and recognise them as currying and uncurrying.',
      'Prove the adjunction <code>(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)</code> out of those two lemmas, without opening the definition of either connective.',
      'Say why cashing a wand consumes its argument, whereas an ordinary implication may be applied to the same hypothesis any number of times.',
      'Read the variance of <code>-∗</code> off its definition rather than remembering it, and refute the version with one side turned the wrong way.',
      'Build a structure with a hole in one line, and fill the hole in one line.'
    ],
    needs: [
      'Unit 14: the six slots of <code>∗</code>, and that it has neither projection nor duplication.',
      'Unit 15: <code>star_mono_left</code>, <code>star_mono_right</code>, <code>star_comm</code>.',
      'Unit 12: <code>⊢</code> as a folded <code>def</code> with three binders, and <code>entails_trans</code>.',
      'Unit 08 to 10: <code>Heap.disjoint</code>, <code>Heap.union</code>, <code>union_comm</code>, <code>union_assoc</code>, and the two bridges <code>disjoint_union_left</code> and <code>disjoint_union_right</code>.',
      'Unit 01: that <code>P ∧ Q → R</code> and <code>P → (Q → R)</code> are the same thing, and that the translation between them is application and abstraction.'
    ],
    payoff: 'Every proof that lends part of a data structure out and takes it back — which is every proof about a loop that walks one — needs an assertion for what the lender is holding meanwhile. This unit supplies it, and the two one-line theorems at the end are the shape such a proof takes.'
  },

  blocks: [

    /* ================================================== the missing thing ==== */

    {t:'p', h:"Take the pattern literally. You hold <code>node p x n ∗ listRep xs n</code>: one node, and the tail of a list hanging off its next field. Now do something to the node. Every rule you have takes one cell and gives one cell back, so the node leaves the description of the list while the rule runs and rejoins it afterwards. Between those two moments you are still holding something, and no assertion you have names it."},

    {t:'p', h:"It is not <code>listRep xs n</code>. That is what is left of the <i>memory</i>, and it is not what is left of the <i>claim</i>. The claim you started with was about a list; what you want back is the list; and <code>listRep xs n</code> on its own has forgotten that there was ever a node in front of it. What you hold in the meantime is a promise — <i>hand me back a <code>node p x n</code> and I have <code>node p x n ∗ listRep xs n</code> again</i> — and nothing built out of <code>emp</code>, <code>↦</code>, <code>∗</code>, <code>pure</code> and <code>aExists</code> says that."},

    {t:'p', h:"Say what shape the missing thing has, before hunting for it. Unit 14 established that <code>∗</code> has no projection: there is no route from <code>P ∗ Q</code> to <code>P</code>. So there is also no route from an entailment <code>P ∗ Q ⊢ R</code> to an entailment out of <code>P</code> alone — the <code>Q</code> has to go somewhere, and the only place left is the right-hand side. That is a move you have seen before, for a different pair of connectives."},

    {t:'txt', cap:'Above the line, what you are given; below it, what you want instead. The top rule is a fact about <code>∧</code> and <code>→</code>. The bottom one is not yet a fact about anything, because the symbol in it has no meaning.',
     src:"      P ∧ Q → R                      P ∗ Q ⊢ R\n    ───────────────  known       ───────────────  wanted\n      P → (Q → R)                    P ⊢ Q -∗ R"},

    {t:'code', tag:'illustration', cap:'The top line, compiled, so that <i>known</i> is a fact on the page rather than an appeal to memory. Left to right is <code>fun f hp hq => f ⟨hp, hq⟩</code>; right to left is <code>fun g h => g h.1 h.2</code>. Both are three characters of bracket work and nothing else.',
     src:"example (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) :=\n  ⟨fun f hp hq => f ⟨hp, hq⟩, fun g h => g h.1 h.2⟩"},

    {t:'p', h:"The top line is currying, and Unit 01 supplied both halves of it without naming it: a proof of <code>P ∧ Q → R</code> is a function taking a pair, a proof of <code>P → (Q → R)</code> is a function taking one argument and returning a function, and <code>⟨…⟩</code> and <code>.1</code>/<code>.2</code> are what carry a proof between the two forms. The bottom line is a <i>specification</i>. There is no <code>-∗</code> yet; the task is to find an assertion, written out of <code>Q</code> and <code>R</code>, that makes the bottom rule hold in both directions. Everything below is that search and its verification."},

    /* ============================================ the obvious lift, and why ==== */

    {t:'sec', s:'Lifting the arrow, and where it stops'},

    {t:'p', h:"Unit 12 built <code>aAnd</code>, <code>aOr</code> and <code>aExists</code> by the same recipe every time: take the connective of ordinary logic and apply it at each state. Two assertions, one store, one heap, and the classical connective in the middle. Nothing in that recipe cares which connective it is, so run it on <code>→</code>."},

    {t:'code', tag:'illustration', cap:'The pointwise lift of implication, and the law that makes it look right. Against <code>aAnd</code> — one heap, both conjuncts — modus ponens is a projection and an application, and Lean needs neither the store nor the heap to see it.',
     src:"def aImp (P Q : Assertion) : Assertion := fun σ h => P σ h → Q σ h\n\nexample (P Q : Assertion) : aAnd (aImp P Q) P ⊢ Q := fun _ _ hpq => hpq.1 hpq.2"},

    {t:'p', h:"So nothing is wrong with implication. What has to be tested is implication across a <i>split</i>: hold the implication in one piece of memory, hold its premise in a separate piece, and conclude. That is <code>aImp P Q ∗ P ⊢ Q</code>, and two tactics take the proof as far as it goes."},

    {t:'code', tag:'sketch', cap:'Two tactics and no third. <code>intro</code> takes the store, the heap and the six slots of the star; <code>subst hu</code> spends the union equation, which shortens the goal. After that there is no tactic to write, and Lean reports <code>unsolved goals</code> with the state below.',
     src:"example (P Q : Assertion) : aImp P Q ∗ P ⊢ Q := by\n  intro σ h ⟨h₁, h₂, hd, hu, himp, hp⟩\n  subst hu"},

    {t:'state', cap:'The state where the proof stops. Three heaps are in play and the hypotheses name the wrong ones.',
     src:"P Q : Assertion\nσ : Store\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhimp : aImp P Q σ h₁\nhp : P σ h₂\n⊢ Q σ (h₁.union h₂)"},

    {t:'p', h:"Read the three lines that matter. <code>himp</code> unfolds to <i>if <code>P</code> holds at <code>h₁</code> then <code>Q</code> holds at <code>h₁</code></i>. <code>hp</code> says <code>P</code> holds at <code>h₂</code>. Those are different heaps, and the whole content of <code>∗</code> is that they are different heaps — <code>hd</code> says so. So the implication's premise is never available where the implication is, and its conclusion, if it were available, would be about <code>h₁</code> rather than about the union the goal asks for. The hypothesis is about the wrong heap in two independent ways."},

    {t:'p', h:"That is not an unfinished proof. The entailment is false, and one heap is enough to show it."},

    {t:'code', tag:'illustration', cap:'Take <code>P</code> to be <code>0 ↦ 4</code> and <code>Q</code> to be <code>aFalse</code>, and cut the one-cell heap into the empty heap and itself. The lifted implication holds at the empty heap <i>because its premise fails there</i> — the empty heap is not <code>Heap.singleton 0 4</code>, so <code>fun he => absurd …</code> discharges it — and a vacuous truth at one heap constrains nothing at any other. The conclusion <code>aFalse</code> is then available at a heap that plainly exists.',
     src:"example :\n    ¬ (aImp (0 ↦ 4) aFalse ∗ (0 ↦ 4) ⊢ aFalse) := by\n  intro hyp\n  have hprem : (aImp (0 ↦ 4) aFalse ∗ (0 ↦ 4)) (fun _ => 0) (Heap.singleton 0 4) :=\n    ⟨Heap.empty, Heap.singleton 0 4, disjoint_empty_left _, (union_empty_left _).symm,\n      fun he => absurd (congrFun he 0) (by simp [Heap.empty, Heap.singleton]), rfl⟩\n  exact hyp (fun _ => 0) (Heap.singleton 0 4) hprem"},

    {t:'p', h:"Go back to the stuck state and ask what <code>himp</code> would have had to say for the proof to close. It would have to say: <i>for every heap <code>h'</code> disjoint from mine at which <code>P</code> holds, <code>Q</code> holds at my heap unioned with <code>h'</code></i>. That sentence mentions all three heaps and relates them the way the goal needs. Written down, there is nothing left to invent."},

    /* ================================================== the definition ==== */

    {t:'sec', s:'The connective the goal asked for'},

    {t:'anat', cap:'The wand. One <code>∀</code>, two hypotheses, one conclusion — and the union in the conclusion is the whole difference between this and <code>aImp</code>.',
     src:"def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')\ninfixr:54 \" -∗ \" => wand",
     parts:[
       {m:'fun σ h', h:"An <code>Assertion</code> is a predicate on a store and a heap, so the definition opens the same way <code>star</code> and <code>pointsTo</code> do. <code>h</code> is <i>the memory the holder of the wand owns</i>, and everything after this arrow is a claim about it."},
       {m:"∀ h'", h:"A quantifier over heaps inside an assertion, and the first universal one in the course. <code>∗</code> quantifies over heaps too, but existentially and over <i>my</i> heap — <i>there is a way to cut mine in two</i> — where this one ranges over heaps that are not mine and may never turn up. That is what makes the wand a promise rather than a fact: the holder commits to every future in which someone arrives with a suitable <code>h'</code>."},
       {m:"Heap.disjoint h h'", h:"The visitor's heap must be separate from mine. Drop this hypothesis and the wand would promise something about heaps that overlap what I own, which is a promise nobody could keep — the union would silently discard cells, because Unit 09 made <code>Heap.union</code> left-biased and total."},
       {m:"P σ h'", h:"The visitor's heap satisfies <code>P</code>. This is the argument of the promise, and it sits to the <i>left</i> of an arrow, which is the whole of the variance question settled later on this page."},
       {m:"Q σ (Heap.union h h')", h:"The payoff, and it is about the <b>combined</b> heap. That is the clause <code>aImp</code> could not have: the conclusion is not about my heap, and not about the visitor's, but about both of them together."},
       {m:'infixr:54', h:"Precedence 54, one below <code>∗</code> at 55, so the wand binds <i>looser</i> than the star. <code>P ∗ Q -∗ R</code> is <code>(P ∗ Q) -∗ R</code> and <code>P -∗ Q ∗ R</code> is <code>P -∗ (Q ∗ R)</code>. Both of those are the reading you want, which is why 54 was chosen: a wand almost always has a star on one side or the other, and a wand whose arguments needed brackets would be unreadable."}
     ]},

    {t:'quote', h:"<i>I hold a resource such that, given a separate heap satisfying <code>P</code>, the combination satisfies <code>Q</code>.</i>"},

    {t:'p', h:"That is the sentence to keep. It is in the first person, like every assertion since Unit 13, and it is a claim about what the holder owns — not about what is true. A wand is a resource in exactly the sense that <code>l ↦ v</code> is: something you can have, hand over, or spend."},

    {t:'p', h:"Being right-associative matters too, because <code>P -∗ (Q -∗ R)</code> is a shape that arrives on its own — it is what currying twice produces — and <code>P -∗ Q -∗ R</code> is how it prints. Four parses, checked rather than asserted."},

    {t:'code', tag:'illustration', cap:'Each line is an equation between two <code>Assertion</code>s closed by <code>rfl</code>, so it holds exactly when the two sides are the same term after parsing. The third line is right-associativity; the fourth is <code>⊢</code> at 40, looser than both, so an entailment never needs brackets around a wand.',
     src:"example (P Q R : Assertion) : (P ∗ Q -∗ R) = ((P ∗ Q) -∗ R) := rfl\nexample (P Q R : Assertion) : (P -∗ Q ∗ R) = (P -∗ (Q ∗ R)) := rfl\nexample (P Q R : Assertion) : (P -∗ Q -∗ R) = (P -∗ (Q -∗ R)) := rfl\nexample (P Q R : Assertion) : (P ⊢ Q -∗ R) = (P ⊢ (Q -∗ R)) := rfl"},

    /* ================================================== currying ==== */

    {t:'sec', s:'Currying, and uncurrying'},

    {t:'p', h:"The specification had two halves. The first: from <code>P ∗ Q ⊢ R</code> produce <code>P ⊢ Q -∗ R</code>. Its proof is short for a reason worth naming — the definition of <code>wand</code> was written so that the heap the goal wants is the heap the hypothesis takes, spelled the same way, so the two meet with no work in between."},

    {t:'p', h:"An entailment has three binders, so <code>intro σ hh hp</code> is a complete opening for any goal of the form <code>P ⊢ …</code>. Here it leaves this:"},

    {t:'state', cap:'After three <code>intro</code>s. The goal is the wand applied to a store and a heap — and a wand is a <code>∀</code>, so <code>intro</code> has not run out of things to introduce.',
     src:"P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ (Q -∗ R) σ hh"},

    {t:'p', h:"Three more <code>intro</code>s go through the definition: the visitor's heap <code>h'</code>, the disjointness <code>hd</code>, and the proof <code>hq</code> that <code>Q</code> holds at <code>h'</code>. The corpus writes all six names on one line. What is left is <code>R σ (hh.union h')</code>, and the hypothesis <code>h</code> produces exactly that, given a store, a heap and a proof that <code>P ∗ Q</code> holds there. The heap to hand it is <code>Heap.union hh h'</code>, and then the union equation in the star's fourth slot is <code>rfl</code>, because the definition of the wand put that union there."},

    {t:'ex',
     id:'m11-1',
     name:'wand_intro',
     why:"Currying, and the cleanest instance in the course of &ldquo;choose the cut&rdquo;. Every other proof that builds a <code>∗</code> has to pick two heaps and then prove they union to the one in the goal; here the goal hands you both halves and the equation is <code>rfl</code>. That is not luck — it is the definition of <code>wand</code> being read backwards. It is one of the two theorems the adjunction is assembled from, and it is the move that turns a goal shaped like a wand back into a goal shaped like a star — which is how the folded example at the end of this unit gets its list back together.",
     setup:"You have the six-slot anonymous constructor for <code>∗</code> (Unit 14) and nothing else. No heap lemma is needed anywhere in this proof.",
     goal:"theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R := by",
     hints:[
       "The goal <code>P ⊢ Q -∗ R</code> unfolds to: for every store <code>σ</code> and heap <code>hh</code>, if <code>P σ hh</code> then <code>(Q -∗ R) σ hh</code> — and that last thing unfolds again, to: for every heap <code>h'</code> disjoint from <code>hh</code> with <code>Q σ h'</code>, <code>R σ (hh.union h')</code>. Six things to assume, one thing to prove.",
       "You are given an entailment out of <code>P ∗ Q</code> and you have a heap satisfying <code>P</code> and a separate heap satisfying <code>Q</code>. Put them together into a proof that <code>P ∗ Q</code> holds at their union, and apply what you were given to it.",
       "One <code>intro</code> with six names, then one <code>exact</code>. The <code>exact</code> applies <code>h</code> to a store, a heap and a six-slot <code>⟨…⟩</code>.",
       "<code>intro σ hh hp h' hd hq</code>. That leaves <code>⊢ R σ (hh.union h')</code>, with <code>hp : P σ hh</code>, <code>hd : hh.disjoint h'</code> and <code>hq : Q σ h'</code> in context. Now apply <code>h</code> at the heap <code>Heap.union hh h'</code>."
     ],
     sol:"theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R := by\n  intro σ hh hp h' hd hq\n  exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
     solNote:"The heap is called <code>hh</code> rather than <code>h</code> because <code>h</code> is already the name of the hypothesis. Naming it <code>h</code> instead compiles the <code>intro</code> and then fails on the next line, where <code>h σ</code> is the heap applied to a store.",
     expl:"Six binders, one term. Three of the binders come from the entailment and three from the wand, and the reader who counts them has understood the definition. The star is then built by the anonymous constructor with the two heaps the context already contains, and the equation slot is <code>rfl</code> because the goal's heap is spelled <code>hh.union h'</code> and the cut is <code>(hh, h')</code>.",
     walk:[
       {tac:'intro σ hh hp', h:"Three binders of the entailment: the store, the heap, and the assumption <code>P σ hh</code>. The goal becomes <code>(Q -∗ R) σ hh</code> — the wand applied to a store and a heap. Nothing about that display says it is a <code>∀</code>, and that is why the next line looks like it should not typecheck."},
       {tac:"intro h' hd hq", h:"Three more, through the definition of <code>wand</code>. <code>h'</code> is the heap the visitor brings, <code>hd : hh.disjoint h'</code> the separation, <code>hq : Q σ h'</code> the argument. The goal becomes <code>R σ (hh.union h')</code>. The corpus writes these three on the same line as the previous three."},
       {tac:"exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩", h:"The hypothesis <code>h</code> is an entailment, so it is a function of a store, a heap and a proof. The heap is the one the goal is about. The six-slot bracket is the cut <code>(hh, h')</code>, the disjointness you were handed, the equation <code>Heap.union hh h' = Heap.union hh h'</code> — which is <code>rfl</code> — and the two halves."}
     ],
     deep:[
       {t:'trace', title:'wand_intro, with the six binders separated',
        start:"P Q R : Assertion\nh : P ∗ Q ⊢ R\n⊢ P ⊢ Q -∗ R",
        steps:[
          {tac:'intro σ hh hp',
           state:"P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ (Q -∗ R) σ hh",
           h:"The entailment is used up. The goal is now the wand at a particular store and heap."},
          {tac:"intro h' hd hq",
           state:"P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\nhd : hh.disjoint h'\nhq : Q σ h'\n⊢ R σ (hh.union h')",
           h:"Three more binders out of the definition. Everything the star needs is now in the context, under a name, and the goal names the union that the star will have to equal."},
          {tac:"exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
           state:"No goals.",
           h:"The only decision in the whole proof is which heap to apply <code>h</code> at, and the goal has already told you."}
        ],
        done:'No goals.'},
       {t:'p', h:"Compare it with the ordinary currying term the reader wrote in Unit 01: <code>fun hp hq => f ⟨hp, hq⟩</code>. The same three moves — take the two arguments separately, pair them, feed the pair to the function you were given. What is added here is a heap for each argument and a proof that the two heaps do not overlap, and those are precisely the extra slots <code>∗</code> has that <code>∧</code> does not."}
     ],
     pitfall:"Naming the heap <code>h</code>. The <code>intro</code> line is accepted — Lean shadows the hypothesis, which becomes <code>h✝</code> — and the error lands on the next line, where <code>h</code> now denotes a heap: <code>Application type mismatch: The argument σ has type Store but is expected to have type Loc in the application h σ</code>. The message is about a store and a location and says nothing about shadowing, so read the <code>intro</code> line rather than the <code>exact</code> line.",
     variants:"Drop the disjointness slot from <code>∗</code> — Unit 14's <code>starNoDisj</code> — and this proof still goes through with five slots instead of six, because <code>wand_intro</code> never inspects <code>hd</code>; it only passes it on. That is a hint about which of the two lemmas on this page is doing the real work, and the answer is the other one. · Reverse the hypothesis to <code>Q ∗ P ⊢ R</code> and the proof needs the cut written the other way round, <code>⟨h', hh, disjoint_symm hd, union_comm hd, hq, hp⟩</code> — the two heap lemmas Unit 15 spent on <code>star_comm</code>, arriving for the same reason. · Replace the hypothesis by <code>aAnd P Q ⊢ R</code> — Unit 12's conjunction, one heap where the star had two — and the theorem becomes false. The point of failure is the slot the <code>exact</code> fills: <code>aAnd</code> would want <code>P</code> and <code>Q</code> at <i>the same</i> heap, and the context holds them at two. Witness: <code>P := 0 ↦ 4</code>, <code>Q := 1 ↦ 5</code>, <code>R := aFalse</code>. No heap is both <code>Heap.singleton 0 4</code> and <code>Heap.singleton 1 5</code>, so <code>aAnd P Q</code> is satisfied nowhere and entails <code>aFalse</code>; but the two singletons are disjoint, and <code>aFalse</code> does not hold at their union. Compiled as <code>¬ (∀ P Q R : Assertion, (aAnd P Q ⊢ R) → (P ⊢ Q -∗ R))</code>."
    },

    {t:'p', h:"The other half of the specification is the reverse direction, and the lemma that carries it is the one you cash a wand with. Hold a wand in one piece of memory, hold its argument in a separate piece, and you have the conclusion — over the two pieces together, which is what the <code>∗</code> in the statement is doing."},

    {t:'ex',
     id:'m11-2',
     name:'wand_elim',
     why:"Cashing a promise. This is modus ponens for resources, and it is the reason a wand is worth holding at all: it is the theorem the hole pattern at the end of this unit spends, and the second of the two lemmas the adjunction is built from. It also contains, in one line, the reason a wand is not an implication — the <code>rw [hu]</code> step, where the goal's heap is replaced by the union the wand's conclusion is about.",
     setup:"The premise is a star, so open it with the six-name <code>intro</code> pattern. The wand in the fifth slot is a function of three arguments.",
     goal:"theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by",
     hints:[
       "Unfolded once: for every <code>σ</code> and <code>h</code>, if <code>h</code> splits into disjoint <code>h₁</code> and <code>h₂</code> with the wand at <code>h₁</code> and <code>P</code> at <code>h₂</code>, then <code>Q</code> holds at <code>h</code>. Unfolded twice, because the wand is itself a <code>∀</code>: what holds at <code>h₁</code> is <i>for every heap disjoint from <code>h₁</code> at which <code>P</code> holds, <code>Q</code> holds at that heap unioned onto <code>h₁</code></i>. Two heaps in the hypothesis, one in the goal, and three names for what are only two heaps.",
       "The wand you hold is a promise about <i>your</i> heap unioned with a separate one satisfying <code>P</code>. You have such a heap: it is the other half of the cut. So the promise applies, and what it gives you is <code>Q</code> at the union — which is the heap you started with, by the star's equation slot.",
       "Three lines: the six-name <code>intro</code> pattern, one <code>rw</code> with the union equation, then apply the wand to the three things it wants.",
       "<code>intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩</code>, then <code>rw [hu]</code>. That turns the goal <code>Q σ h</code> into <code>Q σ (h₁.union h₂)</code>, which is the shape <code>hw</code> concludes in."
     ],
     sol:"theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by\n  intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩\n  rw [hu]\n  exact hw h₂ hd hp",
     expl:"The whole proof is the observation that the wand's three requirements are already in the context: a heap (<code>h₂</code>), its disjointness from the wand's own heap (<code>hd</code>), and a proof that <code>P</code> holds there (<code>hp</code>). What the wand returns is a proof about <code>h₁.union h₂</code>, and the goal is about <code>h</code>. <code>rw [hu]</code> is the one line that reconciles the two.",
     walk:[
       {tac:"intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩", h:"Three binders and a six-name pattern. <code>hw : (P -∗ Q) σ h₁</code> is the wand, sitting in the fifth slot; <code>hp : P σ h₂</code> is its argument, in the sixth. The goal is <code>Q σ h</code>."},
       {tac:'rw [hu]', h:"<code>hu : h = h₁.union h₂</code>, so this replaces <code>h</code> in the goal, leaving <code>Q σ (h₁.union h₂)</code>. Nothing has been proved; the goal has been restated in the vocabulary the wand speaks."},
       {tac:'exact hw h₂ hd hp', h:"<code>hw</code> is a <code>∀</code> followed by two arrows, so it takes a heap, a disjointness proof and a proof of <code>P</code>, in that order, and returns <code>Q σ (h₁.union h₂)</code> — the goal exactly."}
     ],
     deep:[
       {t:'trace', title:'wand_elim, three tactics',
        start:"P Q : Assertion\n⊢ (P -∗ Q) ∗ P ⊢ Q",
        steps:[
          {tac:"intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩",
           state:"P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhw : (P -∗ Q) σ h₁\nhp : P σ h₂\n⊢ Q σ h",
           h:"Everything the wand wants is here, but the goal is about <code>h</code> and the wand talks about <code>h₁.union h₂</code>."},
          {tac:'rw [hu]',
           state:"P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhw : (P -∗ Q) σ h₁\nhp : P σ h₂\n⊢ Q σ (h₁.union h₂)",
           h:"One symbol changed in the goal. This is the line the proof cannot do without, and skipping it is the standard mistake — see the pitfall."},
          {tac:'exact hw h₂ hd hp',
           state:"No goals.",
           h:"The order of the three arguments is the order of the definition: heap, disjointness, premise."}
        ],
        done:'No goals.'},
       {t:'p', h:"Set this proof beside <code>wand_intro</code>'s. <code>wand_intro</code> ends by <i>building</i> a star out of two heaps it was handed; <code>wand_elim</code> begins by <i>consuming</i> one. Unit 14 named that asymmetry when it introduced the existential cut, and here the two halves of it stand next to each other, one lemma each."}
     ],
     pitfall:"Omitting <code>rw [hu]</code> and writing <code>exact hw h₂ hd hp</code> straight after the <code>intro</code>. Lean answers <code>Type mismatch: hw h₂ hd hp has type Q σ (h₁.union h₂) but is expected to have type Q σ h</code>. The two heaps are equal — <code>hu</code> says so — but they are not the <i>same term</i>, and <code>exact</code> matches up to definitional equality, which an equation between two variables is not. <code>subst hu</code> works as well as <code>rw [hu]</code>, and removes <code>h</code> from the context entirely.",
     variants:"Swap the order of the star and the theorem becomes <code>P ∗ (P -∗ Q) ⊢ Q</code>, which is also true and is <code>entails_trans (star_comm …) (wand_elim …)</code> — that composition is the body of <code>hole_elim</code> later on this page. · Drop the disjointness conjunct from <code>∗</code> and this proof breaks, because <code>hd</code> is the third argument the wand demands and there would be nothing to supply. That is the sense in which <code>wand_elim</code> is where the separation is spent, while <code>wand_intro</code> only carries it. · Strengthen the conclusion to <code>Q ∗ P</code> — <i>cash the promise and keep the argument</i> — and the theorem becomes false; the refutation is in the next section."
    },

    /* ================================================== consumption ==== */

    {t:'sec', s:'A promise that spends what it is given'},

    {t:'p', h:"Ordinary implication does not consume anything. From <code>A → B</code> and <code>A</code> you may conclude <code>A ∧ B</code>, and the single proof of <code>A</code> is spent twice over — once in the left component, once inside the application. That is contraction, and Unit 14 said what it costs: a logic in which hypotheses may be duplicated cannot be a logic about resources."},

    {t:'cmp',
     left:{t:'Implication keeps its premise', kind:'good', tag:'illustration', src:"example (A B : Prop) : (A → B) → A → A ∧ B := fun f a => ⟨a, f a⟩",
           h:"<code>a</code> appears twice on the right-hand side, and nothing forbids it. A proof is not a resource; using it does not use it up, so the question of how many copies you have never arises."},
     right:{t:'The wand does not', kind:'bad', src:"example :\n    ¬ (((0 ↦ 4) -∗ (0 ↦ 4)) ∗ (0 ↦ 4) ⊢ (0 ↦ 4) ∗ (0 ↦ 4)) := by\n  intro hyp\n  have hprem : (((0 ↦ 4) -∗ (0 ↦ 4)) ∗ (0 ↦ 4)) (fun _ => 0) (Heap.singleton 0 4) :=\n    ⟨Heap.empty, Heap.singleton 0 4, disjoint_empty_left _, (union_empty_left _).symm,\n      (fun h' _ hp => by rw [union_empty_left]; exact hp), rfl⟩\n  exact star_pointsTo_same_false 0 4 4 (fun _ => 0) (Heap.singleton 0 4)\n    (hyp (fun _ => 0) (Heap.singleton 0 4) hprem)",
            tag:'illustration',
            h:"The premise is satisfiable — the one-cell heap satisfies it, with the identity wand sitting at the empty half. The conclusion is not satisfiable at any heap, by Unit 14's <code>star_pointsTo_same_false</code>. So cashing the wand and keeping the cell is refuted, at a heap that exists."}},

    {t:'p', h:"The reason is in the definition and not in the theorem. A wand's argument arrives as a <i>separate heap</i>, and the conclusion is about the union of that heap with the wand's own. There is one copy of the argument's memory and it ends up inside the result. To have <code>Q</code> and still have <code>P</code> you would need the cells of <code>P</code> in two disjoint places at once, and Unit 14 proved that impossible for exact assertions."},

    {t:'p', h:"That has a second consequence, about repetition rather than about keeping. A wand may be applied to memory you have not yet spent, and to no other. There is no way to apply <code>l ↦ v -∗ Q</code> twice to the same cell, because after the first application the cell is inside the result and is no longer available as a disjoint argument. An implication has no such restriction, and that is the difference between a logic of truth and a logic of ownership, appearing this time in the shape of a connective rather than in the failure of a law."},

    /* ================================================== adjunction ==== */

    {t:'sec', s:'The adjunction'},

    {t:'p', h:"The two lemmas together are the specification, and the form in which it gets used is the single biconditional: an entailment whose left-hand side is a star and an entailment whose right-hand side is a wand are the <i>same</i> statement, so either may be traded for the other at any point in a proof."},

    {t:'p', h:"The forward direction is <code>wand_intro</code> and nothing else. The reverse direction is the interesting one, and the point of the exercise is that it is proved <i>from</i> <code>wand_elim</code> rather than from the definition of anything. Given <code>h : P ⊢ Q -∗ R</code>, improve the left conjunct of <code>P ∗ Q</code> with it — that is <code>star_mono_left</code>, Unit 15 — reaching <code>(Q -∗ R) ∗ Q</code>, which is <code>wand_elim</code>'s premise verbatim. Two links, one <code>entails_trans</code>."},

    {t:'ex',
     id:'m11-3',
     name:'star_wand_adjunction',
     why:"The theorem the connective exists for, and the one you will reach for. It says that <code>-∗</code> is not an extra piece of vocabulary but a way of writing something you could already say — with the crucial difference that the new way is an <i>assertion</i>, so it can appear inside a bigger assertion, under a <code>∗</code>, in a precondition. Proving it out of the two previous lemmas rather than from the model is the lesson: once the halves are named, the whole is free.",
     setup:"An <code>↔</code> between two propositions, so <code>constructor</code> splits it into a <code>case mp</code> and a <code>case mpr</code>. Neither branch opens a definition. You need <code>star_mono_left</code> and <code>entails_trans</code> from Unit 15 and Unit 12.",
     goal:"theorem star_wand_adjunction (P Q R : Assertion) : (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R) := by",
     hints:[
       "Two implications between propositions about entailments. Forwards: given a proof that <code>P ∗ Q ⊢ R</code>, produce one that <code>P ⊢ Q -∗ R</code>. Backwards: the other way round. Nothing here mentions a heap.",
       "Forwards is a theorem you have already proved, applied with no arguments. Backwards: you hold <code>P ⊢ Q -∗ R</code> and want <code>P ∗ Q ⊢ R</code>. Rewrite the left-hand side of the star using what you hold, and then read what you are left with.",
       "<code>constructor</code>, then one focus dot each. The forward branch is a single name. The backward branch is <code>entails_trans</code> gluing <code>star_mono_left</code> to <code>wand_elim</code>.",
       "<code>constructor</code>; the first branch is <code>exact wand_intro</code>. In the second, after <code>intro h</code>, write <code>refine entails_trans (star_mono_left Q h) ?_</code> — that leaves the goal <code>(Q -∗ R) ∗ Q ⊢ R</code>."
     ],
     sol:"theorem star_wand_adjunction (P Q R : Assertion) : (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R) := by\n  constructor\n  · exact wand_intro\n  · intro h\n    refine entails_trans (star_mono_left Q h) ?_\n    exact wand_elim Q R",
     solNote:"The forward branch is <code>exact wand_intro</code> with no arguments at all: the implicit binders of <code>wand_intro</code> are exactly the three assertions in scope, and its explicit argument is the very hypothesis the goal is asking you to consume.",
     expl:"Both halves are compositions of finished theorems. The backward direction is the shape Unit 17 called proof by composition: name the entailment you want to end at, name the one you can start with, and let <code>entails_trans</code> hold them together. Here the middle assertion is <code>(Q -∗ R) ∗ Q</code>, and it is forced — it is what <code>star_mono_left</code> produces and what <code>wand_elim</code> consumes.",
     walk:[
       {tac:'constructor', h:"Splits the <code>↔</code> into <code>case mp</code> with goal <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code> and <code>case mpr</code> with the converse."},
       {tac:'· exact wand_intro', h:"The whole forward direction. <code>wand_intro</code> takes a proof of <code>P ∗ Q ⊢ R</code> and returns one of <code>P ⊢ Q -∗ R</code>, which is a function of exactly the type of the goal."},
       {tac:'· intro h', h:"In the backward branch, name the hypothesis <code>h : P ⊢ Q -∗ R</code>. The goal becomes <code>P ∗ Q ⊢ R</code>."},
       {tac:'refine entails_trans (star_mono_left Q h) ?_', h:"<code>star_mono_left Q h : P ∗ Q ⊢ (Q -∗ R) ∗ Q</code> — the left conjunct improved and the right one untouched. <code>entails_trans</code> takes that as its first link and leaves the second as a hole, so the goal becomes <code>(Q -∗ R) ∗ Q ⊢ R</code>."},
       {tac:'exact wand_elim Q R', h:"That hole is the previous exercise, with its two arguments supplied explicitly because <code>wand_elim</code>'s binders are explicit."}
     ],
     deep:[
       {t:'trace', title:'star_wand_adjunction, the backward branch',
        start:"P Q R : Assertion\n⊢ P ∗ Q ⊢ R ↔ P ⊢ Q -∗ R",
        steps:[
          {tac:'constructor',
           state:"case mp\nP Q R : Assertion\n⊢ P ∗ Q ⊢ R → P ⊢ Q -∗ R\n\ncase mpr\nP Q R : Assertion\n⊢ P ⊢ Q -∗ R → P ∗ Q ⊢ R",
           h:"Both goals at once, as Lean prints them. The turnstiles are doubled and the brackets are gone, in the start state and in both branches: the outer <code>⊢</code> is the goal display, the inner ones are <code>Entails</code> at 40, and <code>↔</code> and <code>→</code> are looser than that, so the statement needs no brackets to parse the way it is written on the page. It needs them to be <i>read</i>, which is why the goal field keeps them."},
          {tac:'intro h',
           state:"case mpr\nP Q R : Assertion\nh : P ⊢ Q -∗ R\n⊢ P ∗ Q ⊢ R",
           h:"The second branch, with the hypothesis named. This is the only branch with any content."},
          {tac:'refine entails_trans (star_mono_left Q h) ?_',
           state:"case mpr\nP Q R : Assertion\nh : P ⊢ Q -∗ R\n⊢ (Q -∗ R) ∗ Q ⊢ R",
           h:"The remaining hole. It is <code>wand_elim</code>'s statement with <code>P</code> renamed to <code>Q</code> and <code>Q</code> renamed to <code>R</code>, which is why the arguments have to be given in that order."}
        ],
        done:'No goals.'},
       {t:'p', h:"The adjunction pins the wand down completely, and that is checkable rather than a slogan. Suppose some assertion <code>W</code> — anything at all, however defined — satisfies the same biconditional for every <code>P</code>. Then <code>W</code> and <code>Q -∗ R</code> entail each other, and the proof is four lines with no heaps in it."},
       {t:'code', tag:'illustration', cap:'Apply the assumed biconditional at <code>P := W</code> to <code>entails_refl W</code>, and you get <code>W ∗ Q ⊢ R</code>, which <code>wand_intro</code> turns into one half. Apply it at <code>P := Q -∗ R</code> to <code>wand_elim</code> and you get the other. So the specification stated at the top of this unit has exactly one solution, up to <code>⊣⊢</code>.',
        src:"example (Q R W : Assertion)\n    (hW : ∀ P : Assertion, (P ∗ Q ⊢ R) ↔ (P ⊢ W)) :\n    W ⊣⊢ (Q -∗ R) :=\n  ⟨wand_intro ((hW W).mpr (entails_refl W)),\n   (hW (Q -∗ R)).mp (wand_elim Q R)⟩"}
     ],
     pitfall:"Reaching for <code>star_mono_right</code>. It is the wrong side, and it is wrong in the <i>first</i> argument rather than in the result: <code>star_mono_right Q h : Q ∗ P ⊢ Q ∗ (Q -∗ R)</code>, whereas <code>entails_trans</code> needs its first link to start at <code>P ∗ Q</code>. Lean reports <code>Application type mismatch: The argument star_mono_right Q h has type Q ∗ P ⊢ Q ∗ (Q -∗ R) but is expected to have type P ∗ Q ⊢ ?m.12 in the application entails_trans (star_mono_right Q h)</code> — and only that one error, because the mismatch is caught before the <code>?_</code> hole is ever created. The unassigned metavariable in the middle is the reason to read the complaint as being about the <i>left</i> of the arrow: Lean is telling you it never got as far as deciding what the intermediate assertion should be. The rule is Unit 15's: <code>_left</code> and <code>_right</code> name which <i>conjunct</i> the entailment is applied to, not which side of the turnstile you are working on.",
     variants:"State the reverse direction as a separate theorem and it is <code>fun h => entails_trans (star_mono_left Q h) (wand_elim Q R)</code>, a term with no tactic in it; the <code>constructor</code> and the dots exist only because the two halves are being packaged. · Weaken the <code>↔</code> to the forward implication alone and you have <code>wand_intro</code> back, so nothing is lost and nothing is gained — the content of this theorem is entirely in the direction that is not <code>wand_intro</code>. · Replace <code>∗</code> by <code>aAnd</code> and <code>-∗</code> by <code>aImp</code> and the biconditional is true again, for the reason the top line of this unit's first schematic gives: it is ordinary currying, lifted pointwise. The wand exists because that substitution changes which connective divides the heap."
    },

    {t:'note', kind:'key', title:'What the adjunction says', h:"Fix <code>Q</code>. Then <code>· ∗ Q</code> and <code>Q -∗ ·</code> are two operations on assertions, and the theorem says that entailments <i>out of</i> the first are the same things as entailments <i>into</i> the second. A pair of operations related that way is called an <b>adjunction</b>, the second is the <b>right adjoint</b> of the first, and the exhibit inside the exercise shows the standard consequence: a right adjoint, if it exists, is determined up to equivalence. So <code>-∗</code> is not one definition among several that would have worked. It is the only one."},

    {t:'detail', title:'The name for the whole structure, and where to find it elsewhere', tag:'aside', open:false, blocks:[
      {t:'p', h:"Assertions now carry two commutative monoids on the same carrier: the classical one from Unit 12, with <code>aAnd</code> and <code>aTrue</code>, and the separating one from Units 14 to 16, with <code>∗</code> and <code>emp</code>. Each has a right adjoint. The second's is <code>-∗</code>; the first's is <code>aImp</code>, the lift this page tried first, which is a perfectly good right adjoint <i>for <code>aAnd</code></i> and fails only as one for <code>∗</code>. An ordered set carrying both is a <b>BI algebra</b>, the models of the logic of <b>bunched implications</b>, and separation logic is what you get by taking heaps as the resources. Ordered, not preordered: entailment failed antisymmetry in Unit 12, so the object being described is assertions with <code>⊣⊢</code>-equivalent ones identified."},
      {t:'p', h:"The same structure read as a category is called <i>closed symmetric monoidal</i>, and the three words translate: <i>closed</i> means <code>∗</code> has a right adjoint, which is this unit; <i>symmetric</i> means <code>star_comm</code>, Unit 15; <i>monoidal</i> means <code>star_assoc_left</code> and the unit laws, Units 15 and 16. In that vocabulary <code>wand_elim</code> has a name of its own — the <b>counit</b> of the adjunction, the canonical map out of applying the right adjoint and then the left. Nothing in any of those words is a fact the course has not proved, and nothing in this paragraph is needed to read the rest of the unit."},
      {t:'p', h:"<code>-∗</code> is pronounced <i>wand</i>, and the literature calls it the magic wand. Neither name is a description; if you want one, the first-person reading above is it."}
    ]},

    /* ================================================== variance ==== */

    {t:'sec', s:'Variance, read off the definition'},

    {t:'p', h:"Which way round do the two arguments of <code>-∗</code> vary? The answer is in the definition and does not have to be remembered. <code>P σ h'</code> sits to the left of an arrow and <code>Q σ (Heap.union h h')</code> to the right, so a wand behaves exactly as a function type does: strengthening what it demands weakens the wand, strengthening what it delivers strengthens it. To go from <code>P -∗ Q</code> to <code>P' -∗ Q'</code> you therefore need <code>P' ⊢ P</code> — the new demand must be <i>stronger</i>, so that anything satisfying it satisfies the old one — and <code>Q ⊢ Q'</code>."},

    {t:'p', h:"Unit 22 read the variance of a Hoare triple off its definition in the same way and for the same reason, and it is the same shape: you may always demand more of the caller and promise less."},

    {t:'ex',
     id:'m11-4',
     name:'wand_mono',
     why:"The congruence rule for the new connective. Without it you cannot improve either side of a wand while it sits inside a bigger assertion, which is what every use of the hole pattern eventually needs. It is also the exercise in which the reader either reads the variance off the definition or gets it backwards, and the hypotheses are labelled so that getting it backwards produces an error rather than a wrong theorem.",
     setup:"Both hypotheses are entailments, so both are functions of a store, a heap and a proof. The proof applies each of them exactly once.",
     goal:"theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q') := by",
     hints:[
       "Unfolded: given a wand from <code>P</code> to <code>Q</code> at heap <code>h</code>, a heap <code>h'</code> disjoint from it, and a proof of <code>P' σ h'</code>, produce <code>Q' σ (h.union h')</code>.",
       "You are handed <code>P'</code> and the wand wants <code>P</code>; convert with <code>hp</code>. The wand then gives you <code>Q</code> and the goal wants <code>Q'</code>; convert with <code>hq</code>. Two conversions, one at each end, in that order.",
       "Six <code>intro</code>s and one <code>exact</code>. The <code>exact</code> is <code>hq</code> applied to a store, a heap and a proof — and that proof is the wand applied to three things, one of which is <code>hp</code> applied to three things.",
       "<code>intro σ h hw h' hd hp'</code>. That leaves <code>⊢ Q' σ (h.union h')</code> with <code>hw : (P -∗ Q) σ h</code>, <code>hd : h.disjoint h'</code> and <code>hp' : P' σ h'</code>. Now nest: <code>hp σ h' hp'</code> has type <code>P σ h'</code>."
     ],
     sol:"theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q') := by\n  intro σ h hw h' hd hp'\n  exact hq σ _ (hw h' hd (hp σ h' hp'))",
     expl:"Three applications nested inside one another, and their order is the order of the data: <code>hp</code> upgrades the incoming argument, the wand does the work, <code>hq</code> weakens the outgoing result. The underscore in <code>hq σ _ …</code> is the union heap, which Lean recovers from the type of the third argument.",
     walk:[
       {tac:"intro σ h hw h' hd hp'", h:"Three binders from the entailment and three from the wand in the goal. The goal becomes <code>Q' σ (h.union h')</code>, and the wand <code>hw</code> is now a hypothesis rather than a goal — which is what makes this proof about applying it rather than about proving it."},
       {tac:"exact hq σ _ (hw h' hd (hp σ h' hp'))", h:"Read it inside out. <code>hp σ h' hp' : P σ h'</code> converts the argument you were given into the argument the wand wants. <code>hw h' hd (…) : Q σ (h.union h')</code> is the wand cashed. <code>hq σ _ (…) : Q' σ (h.union h')</code> weakens the result to the goal; the heap is left as <code>_</code> because it is determined."}
     ],
     deep:[
       {t:'trace', title:'wand_mono, two tactics',
        start:"P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\n⊢ P -∗ Q ⊢ P' -∗ Q'",
        steps:[
          {tac:"intro σ h hw h' hd hp'",
           state:"P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\nσ : Store\nh : Heap\nhw : (P -∗ Q) σ h\nh' : Heap\nhd : h.disjoint h'\nhp' : P' σ h'\n⊢ Q' σ (h.union h')",
           h:"The heaps decide where each conversion happens. <code>hp'</code> is at <code>h'</code> and so is the wand's demand, so <code>hp</code> is applied at <code>h'</code>; the goal is at <code>h.union h'</code> and so is the wand's delivery, so <code>hq</code> is applied there."},
          {tac:"exact hq σ _ (hw h' hd (hp σ h' hp'))",
           state:"No goals.",
           h:"The two hypotheses are used once each and never inspected. No heap lemma appears, because no heap is ever taken apart."}
        ],
        done:'No goals.'}
     ],
     pitfall:"Writing the hypotheses the other way round when you state the theorem yourself — <code>P ⊢ P'</code> instead of <code>P' ⊢ P</code>. The proof then stalls at the innermost application, with <code>Application type mismatch: The argument hp' has type P' σ h' but is expected to have type P σ h' in the application hp σ h' hp'</code>. Contravariance is not a convention to memorise: it is forced by which side of the arrow the assertion sits on.",
     variants:"Turn the left hypothesis round to <code>P ⊢ P'</code> and keep the conclusion, and the theorem is false. Witness: <code>aFalse ⊢ emp</code> holds (by <code>fun _ _ hf => hf.elim</code>), <code>aFalse -∗ aFalse</code> holds at every heap because its argument is unsatisfiable, and <code>emp -∗ aFalse</code> holds at none, since the empty heap is always available as a visitor. Compiled: <code>¬ ((aFalse -∗ aFalse) ⊢ (emp -∗ aFalse))</code>. · Turn the right hypothesis round to <code>Q' ⊢ Q</code> and the same pair of assertions refutes it: <code>emp -∗ emp</code> holds at the empty heap and <code>emp -∗ aFalse</code> does not, while <code>aFalse ⊢ emp</code> supplies the reversed hypothesis. · Drop <code>hq</code> altogether, leaving contravariance on its own, and the proof loses its outermost application and nothing else — which is the check that the two halves really are independent."
    },

    /* ================================================== the hole ==== */

    {t:'sec', s:'A structure with a hole'},

    {t:'p', h:"Now the pattern the unit opened with. You hold <code>P ∗ R</code>. You want to hand the <code>P</code> to someone and still be able to say, in one assertion, what you are left with. The answer is a wand, and the two directions of the exchange are one line each."},

    {t:'svg', cap:'Lending and recovering. On the left, what you hold: the whole thing. On the right, what you hold once <code>P</code> has been handed over: the <code>P</code> itself, sitting beside a claim shaped like the original with a <code>P</code>-sized hole in it. <code>hole_intro</code> goes left to right and <code>hole_elim</code> comes back.',
     src:"<svg viewBox=\"0 0 640 210\" role=\"img\" aria-label=\"On the left, a single assertion P star R drawn as two adjacent cells. On the right, the cell P standing alone beside a box containing a dashed empty slot and the cell R, labelled P wand P star R. Two arrows between them, labelled hole_intro going right and hole_elim coming back\">\n  <defs>\n    <marker id=\"ah37\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"currentColor\"/>\n    </marker>\n  </defs>\n  <g class=\"dg\">\n    <text x=\"22\" y=\"24\" class=\"dg-lab\">what you hold</text>\n    <rect class=\"dg-box a\" x=\"22\" y=\"42\" width=\"84\" height=\"48\" rx=\"5\"/>\n    <rect class=\"dg-box b\" x=\"106\" y=\"42\" width=\"124\" height=\"48\" rx=\"5\"/>\n    <text x=\"64\" y=\"72\" text-anchor=\"middle\" class=\"dg-t\">P</text>\n    <text x=\"168\" y=\"72\" text-anchor=\"middle\" class=\"dg-t\">R</text>\n    <text x=\"126\" y=\"114\" text-anchor=\"middle\" class=\"dg-note\">P ∗ R</text>\n    <path d=\"M 258 58 L 372 58\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah37)\"/>\n    <text x=\"315\" y=\"48\" text-anchor=\"middle\" class=\"dg-note\">hole_intro</text>\n    <path d=\"M 372 84 L 258 84\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah37)\"/>\n    <text x=\"315\" y=\"104\" text-anchor=\"middle\" class=\"dg-note\">hole_elim</text>\n    <text x=\"398\" y=\"24\" class=\"dg-lab\">after lending P out</text>\n    <rect class=\"dg-box a\" x=\"398\" y=\"42\" width=\"64\" height=\"48\" rx=\"5\"/>\n    <text x=\"430\" y=\"72\" text-anchor=\"middle\" class=\"dg-t\">P</text>\n    <text x=\"478\" y=\"72\" text-anchor=\"middle\" class=\"dg-t\">∗</text>\n    <rect class=\"dg-box c\" x=\"496\" y=\"32\" width=\"128\" height=\"68\" rx=\"6\"/>\n    <rect x=\"506\" y=\"42\" width=\"48\" height=\"48\" rx=\"5\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.2\" stroke-dasharray=\"4 3\" opacity=\"0.55\"/>\n    <text x=\"530\" y=\"72\" text-anchor=\"middle\" class=\"dg-note\">?</text>\n    <rect class=\"dg-box b\" x=\"562\" y=\"42\" width=\"52\" height=\"48\" rx=\"5\"/>\n    <text x=\"588\" y=\"72\" text-anchor=\"middle\" class=\"dg-t\">R</text>\n    <text x=\"560\" y=\"122\" text-anchor=\"middle\" class=\"dg-note\">P -∗ (P ∗ R)</text>\n  </g>\n</svg>"},

    {t:'p', h:"The residual claim on the right is <code>P -∗ (P ∗ R)</code>, and the theorem that produces it is worth stating on its own: anything you hold is, for free, a promise to produce itself alongside whatever you are given. That is <code>wand_unit</code>. Its proof is the six-binder pattern once more, and the only decision in it is the cut — the visitor's heap goes on the <i>left</i> of the star, because the conclusion is <code>P ∗ Q</code> and it is <code>P</code> that the visitor brought."},

    {t:'p', h:"With <code>wand_unit</code> in hand, the two exchange lemmas are compositions. Lending is <code>star_mono_right</code> applied to it: leave the <code>P</code> alone and turn the <code>R</code> into the promise. Recovering is <code>wand_elim</code> after a commutation, because <code>wand_elim</code> wants the wand on the left and the picture has it on the right."},

    {t:'ex',
     id:'x68',
     name:'wand_unit, hole_intro, hole_elim',
     why:"The working pattern, in three statements. A proof that walks a data structure and lends part of it out uses <code>hole_intro</code> where the piece is handed over and <code>hole_elim</code> where it comes back, and <code>wand_unit</code> is what makes the first of those true. The second and third are each a single application of theorems you have already proved, which is the evidence that the connective has been set up correctly — a definition that needed a new heap argument for its own basic pattern would be the wrong definition.",
     setup:"<code>wand_unit</code> is proved from the definition. <code>hole_intro</code> and <code>hole_elim</code> are terms, with no <code>by</code> in them: the first is one application of <code>star_mono_right</code>, the second one <code>entails_trans</code>.",
     goal:"theorem wand_unit (P Q : Assertion) : Q ⊢ P -∗ (P ∗ Q) := by\n  sorry\n\ntheorem hole_intro (P R : Assertion) : P ∗ R ⊢ P ∗ (P -∗ (P ∗ R)) :=\n  sorry\n\ntheorem hole_elim (P R : Assertion) : P ∗ (P -∗ (P ∗ R)) ⊢ P ∗ R :=",
     hints:[
       "<code>wand_unit</code> unfolded: given <code>Q</code> at heap <code>h</code>, a heap <code>h'</code> disjoint from it, and <code>P</code> at <code>h'</code>, show <code>(P ∗ Q) σ (h.union h')</code>. The other two are entailments between two stars, and the two stars differ in one conjunct each time: <code>hole_intro</code> has <code>R</code> on the left and <code>P -∗ (P ∗ R)</code> on the right, in the second position both times; <code>hole_elim</code> is the same pair the other way round. Nothing in either of those two mentions a heap.",
       "For <code>wand_unit</code>: the star in the goal needs a cut of <code>h.union h'</code>, and you have exactly two pieces. Which of them satisfies <code>P</code> decides which way round the cut goes, and then both the disjointness and the equation have to be turned round to match. For the other two: improve one conjunct in place, and commute then cash.",
       "<code>wand_unit</code>: <code>intro</code> with six names, then a six-slot bracket whose third and fourth components are <code>disjoint_symm</code> and <code>union_comm</code> applied to the disjointness you were handed. <code>hole_intro</code>: <code>star_mono_right</code>. <code>hole_elim</code>: <code>entails_trans</code>, <code>star_comm</code>, <code>wand_elim</code>.",
       "<code>intro σ h hq h' hd hp</code> leaves <code>⊢ (P ∗ Q) σ (h.union h')</code> with <code>hp : P σ h'</code> and <code>hq : Q σ h</code>. So the cut is <code>(h', h)</code>, not <code>(h, h')</code>. Then <code>hole_intro</code> is <code>star_mono_right P (wand_unit P R)</code>."
     ],
     sol:"theorem wand_unit (P Q : Assertion) : Q ⊢ P -∗ (P ∗ Q) := by\n  intro σ h hq h' hd hp\n  exact ⟨h', h, disjoint_symm hd, union_comm hd, hp, hq⟩\n\ntheorem hole_intro (P R : Assertion) : P ∗ R ⊢ P ∗ (P -∗ (P ∗ R)) :=\n  star_mono_right P (wand_unit P R)\n\ntheorem hole_elim (P R : Assertion) : P ∗ (P -∗ (P ∗ R)) ⊢ P ∗ R :=\n  entails_trans (star_comm P (P -∗ (P ∗ R))) (wand_elim P (P ∗ R))",
     solNote:"<code>hole_intro</code> and <code>hole_elim</code> contain no <code>by</code>, no heap and no store. They are the shape every real use of the wand takes, and they exist as named theorems so that a proof using the pattern can cite two lines instead of repeating six.",
     expl:"<code>wand_unit</code> is where the memory is handled, and its content is one choice: the cut is <code>(h', h)</code>, with the visitor's heap first, because the goal's star is <code>P ∗ Q</code> and <code>P</code> is what the visitor brought. Making that choice forces the two heap lemmas — <code>disjoint_symm</code> for the third slot and <code>union_comm</code> for the fourth — and they are the only two lemmas anywhere in this exercise.",
     walk:[
       {tac:"intro σ h hq h' hd hp", h:"Six binders again. <code>hq : Q σ h</code> is what you hold; <code>hp : P σ h'</code> is what the visitor brought; <code>hd : h.disjoint h'</code> separates them. The goal is <code>(P ∗ Q) σ (h.union h')</code>."},
       {tac:"exact ⟨h', h, disjoint_symm hd, union_comm hd, hp, hq⟩", h:"The cut is written the opposite way round to the union in the goal, so the third slot needs <code>h'.disjoint h</code> — that is <code>disjoint_symm hd</code> — and the fourth needs <code>h.union h' = h'.union h</code>, which is <code>union_comm hd</code>. The last two slots are the two hypotheses, in the order the conclusion names them."},
       {tac:'star_mono_right P (wand_unit P R)', h:"<code>hole_intro</code>. <code>star_mono_right</code> improves the right conjunct and leaves the left one untouched, so the <code>P</code> you are lending is undisturbed and the <code>R</code> becomes the promise. No new argument: the entire theorem is <code>wand_unit</code> placed under a star."},
       {tac:'entails_trans (star_comm P (P -∗ (P ∗ R))) (wand_elim P (P ∗ R))', h:"<code>hole_elim</code>. <code>wand_elim</code> consumes <code>(P -∗ Q) ∗ P</code>, wand first; the picture has the wand second. <code>star_comm</code> swaps them, and <code>entails_trans</code> composes the swap with the cashing. The second argument's <code>Q</code> is instantiated to <code>P ∗ R</code>, which is why it reads as it does."}
     ],
     deep:[
       {t:'trace', title:'wand_unit, and why the cut is backwards',
        start:"P Q : Assertion\n⊢ Q ⊢ P -∗ P ∗ Q",
        steps:[
          {tac:"intro σ h hq h' hd hp",
           state:"P Q : Assertion\nσ : Store\nh : Heap\nhq : Q σ h\nh' : Heap\nhd : h.disjoint h'\nhp : P σ h'\n⊢ (P ∗ Q) σ (h.union h')",
           h:"The start state above prints the conclusion as <code>P -∗ P ∗ Q</code>: Lean drops brackets it does not need, and <code>∗</code> at 55 binds tighter than <code>-∗</code> at 54, so that is the same term as the <code>P -∗ (P ∗ Q)</code> in the goal field. Now read this state's goal and its two proofs together. The star wants <code>P</code> in its first component and <code>P</code> is at <code>h'</code>; the union in the goal has <code>h</code> first. The two orders disagree, and that disagreement is the whole proof."},
          {tac:"exact ⟨h', h, disjoint_symm hd, union_comm hd, hp, hq⟩",
           state:"No goals.",
           h:"Both heap lemmas are applied to the same <code>hd</code>. Unit 15 spent exactly this pair on <code>star_comm</code>, for exactly this reason."}
        ],
        done:'No goals.'},
       {t:'p', h:"Writing <code>⟨h, h', hd, rfl, hp, hq⟩</code> instead — the cut in the order the union suggests — gets as far as the fifth slot and then reports <code>Application type mismatch: The argument hp has type P σ h' but is expected to have type P σ h in the application And.intro hp</code>. The complaint arrives at the value, not at the heap, which is the usual way a wrong cut announces itself."}
     ],
     pitfall:"Trying to prove <code>hole_intro</code> by opening the star. It works, and it costs three tactics instead of one term: <code>intro σ h ⟨h₁, h₂, hd, hu, hp, hr⟩</code>, then <code>refine ⟨h₁, h₂, hd, hu, hp, ?_⟩</code> — the same cut, the same equation, the left conjunct passed straight through — then <code>exact fun h' hd' hp' => ⟨h', h₂, disjoint_symm hd', union_comm hd', hp', hr⟩</code> for the hole. That last line is <code>wand_unit</code>'s proof written out again: the same backwards cut and the same two heap lemmas. The tell that the one-line proof was available is visible in the <code>refine</code>: five of the six slots were copied unchanged from the hypothesis. Whenever the two sides of an entailment differ in exactly one conjunct, the answer is <code>star_mono_left</code> or <code>star_mono_right</code> applied to something, and the only question is which.",
     variants:"What is <code>emp -∗ P</code>? The visitor brings nothing, so the promise is worth exactly <code>P</code> — and both directions are in the fragment as <code>emp_wand_elim</code> and <code>emp_wand_intro</code>. The first applies the wand to <code>Heap.empty</code>, using <code>disjoint_empty_right</code> and then <code>union_empty_right</code> to get back to the heap it started at. The second goes the other way: the visitor's heap satisfies <code>emp</code>, so it <i>is</i> <code>Heap.empty</code>, and <code>union_empty_right</code> rewrites the goal. So <code>emp</code> is a unit for <code>-∗</code> on the left, in the sense that <code>emp -∗ P ⊣⊢ P</code>. · Strengthen <code>hole_intro</code> to an equivalence and you would need the converse of <code>wand_unit</code>, <code>P -∗ (P ∗ R) ⊢ R</code>, which is false. Take <code>P</code> and <code>R</code> both <code>0 ↦ 4</code> and evaluate at <code>Heap.singleton 0 5</code>: no heap disjoint from that one satisfies <code>0 ↦ 4</code>, since both would claim address 0, so the wand holds vacuously — while <code>0 ↦ 4</code> is false there, because the cell holds 5. Compiled, with <code>singleton_disjoint_iff</code> supplying the contradiction. <code>hole_elim</code> shows the equivalence does hold once the <code>P</code> is standing beside it, which is the difference the <code>∗</code> makes."
    },

    {t:'note', kind:'info', title:'Where this shape actually turns up', h:"A loop that walks a linked list holds, at each step, the part behind it and the part in front. To do anything to the node under the cursor it has to take that node out of the description of the list, and put it back afterwards. What it holds meanwhile is <code>node p x n -∗ listRep (x :: xs) p</code>: <i>give me this node back and I have the list again</i>. Nothing else in the assertion language says that: the piece the cursor is standing on has to leave the description of the list, and something has to hold its place while it is away."},

    {t:'code', tag:'illustration', cap:'The pattern at a list node, both directions, obtained by instantiating the two theorems and nothing else. The residual assertion is <code>node p x n -∗ (node p x n ∗ listRep xs n)</code>, and the sentence to read off it is <i>hand me back the node and I have the node and the tail again</i>.',
     src:"example (p x n : Nat) (xs : List Nat) :\n    node p x n ∗ listRep xs n ⊢\n      node p x n ∗ (node p x n -∗ (node p x n ∗ listRep xs n)) :=\n  hole_intro (node p x n) (listRep xs n)\n\nexample (p x n : Nat) (xs : List Nat) :\n    node p x n ∗ (node p x n -∗ (node p x n ∗ listRep xs n)) ⊢\n      node p x n ∗ listRep xs n :=\n  hole_elim (node p x n) (listRep xs n)"},

    {t:'detail', title:'The same thing with listRep folded back up', tag:'aside', open:false, blocks:[
      {t:'p', h:"The instance above keeps <code>node p x n ∗ listRep xs n</code> unfolded on both sides. Folding it into <code>listRep (x :: xs) p</code> is more useful and needs one extra ingredient — the non-nullness conjunct, which the <code>cons</code> clause of Unit 32's definition carries and which nobody in the exchange ever spends. Carrying it along is what the first three lines do."},
      {t:'code', tag:'illustration', cap:'Eight lines, no heap named anywhere. <code>star_swap_middle</code> brings the node to the front; <code>star_mono_right</code> aims the rest of the work at the second conjunct; <code>wand_intro</code> turns the goal from a wand into a star, which is the adjunction being used as a tactic; the four lines after it re-bracket the three conjuncts into the order the definition wants, and the last supplies the existential witness.',
       src:"example (p x n : Nat) (xs : List Nat) :\n    pure (fun _ => p ≠ 0) ∗ node p x n ∗ listRep xs n ⊢\n      node p x n ∗ (node p x n -∗ listRep (x :: xs) p) := by\n  refine entails_trans (star_swap_middle _ _ _) ?_\n  refine star_mono_right _ ?_\n  refine wand_intro ?_\n  refine entails_trans (star_comm _ _) ?_\n  refine entails_trans (star_assoc_right _ _ _) ?_\n  refine entails_trans (star_mono_left _ (star_comm _ _)) ?_\n  refine entails_trans (star_assoc_left _ _ _) ?_\n  exact fun σ h hstar => ⟨n, hstar⟩"},
      {t:'p', h:"The third line is the one to look at. The goal at that point is a wand, and <code>wand_intro</code> converts it into an entailment whose left-hand side is a star — after which the proof is ordinary Module 3 bookkeeping of the kind Unit 33's inductive step is made of. That is the adjunction earning its keep: it lets you stop reasoning about promises and go back to reasoning about stars."}
    ]},

    /* ================================================== curry with resources ==== */

    {t:'sec', s:'Currying, with the resources counted'},

    {t:'p', h:"The unit opened by asking for the bottom line of a two-line schematic. Having got it, the top line's other consequence is available too: currying and uncurrying a wand itself. A promise that consumes <code>P ∗ Q</code> and a promise that consumes <code>P</code> and then consumes <code>Q</code> are the same promise, and the equivalence is two entailments."},

    {t:'p', h:"Both directions are proved from the definition, and both spend the same two facts: the associativity of <code>Heap.union</code>, and the two bridges relating disjointness to union. That is not incidental. Currying a wand means regrouping three heaps — the one you hold, the first visitor's, the second visitor's — and re-grouping heaps is exactly what Unit 10 built <code>union_assoc</code>, <code>disjoint_union_left</code> and <code>disjoint_union_right</code> for. Those three lemmas have been spent together twice before, in Unit 11's <code>splits_assoc</code> and Unit 16's <code>star_assoc_left</code>, and both times for the same reason. A wand is the third thing in the course that regroups three heaps."},

    {t:'p', h:"The naming rule matters here more than usual, and Unit 16 stated it: <code>disjoint_union_left</code> names a union on the <b>left</b> of <code>Heap.disjoint</code>, <code>disjoint_union_right</code> one on the right. Which of the two you need at each step is decided by the hypothesis in front of you, not by the direction you are proving."},

    {t:'ex',
     id:'x69',
     name:'wand_curry and wand_uncurry',
     hard: false,
     why:"The sharpest statement of what the adjunction buys, and the one proof on this page that regroups heaps rather than merely renaming them. Currying an ordinary implication rearranges nothing; currying a wand rearranges three heaps and needs a theorem about each rearrangement, which is what &ldquo;resource-sensitive&rdquo; amounts to when you write it out. The second direction is the first one reflected — every step becomes its opposite — so writing it measures whether you knew what each step of the first was for.",
     setup:"Both directions open with the definition of <code>wand</code> and never mention <code>wand_intro</code> or <code>wand_elim</code>. You need <code>union_assoc</code>, <code>disjoint_union_left</code> and <code>disjoint_union_right</code> from Unit 10.",
     goal:"theorem wand_curry (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R) := by\n  sorry\n\ntheorem wand_uncurry (P Q R : Assertion) : (P -∗ (Q -∗ R)) ⊢ (P ∗ Q) -∗ R := by",
     hints:[
       "In <code>wand_curry</code> you hold a wand at heap <code>h</code> that wants a single heap satisfying <code>P ∗ Q</code>. Two visitors turn up instead, one with <code>h₁</code> satisfying <code>P</code> and then one with <code>h₂</code> satisfying <code>Q</code>, and the goal is <code>R</code> at <code>(h.union h₁).union h₂</code>. In <code>wand_uncurry</code> one visitor turns up with a heap that splits, and you must feed the two halves to a wand that takes them one at a time.",
       "Build the visitor the wand you hold is expecting: in <code>wand_curry</code> that is <code>h₁.union h₂</code>, satisfying <code>P ∗ Q</code>. To offer it you must show it is disjoint from <code>h</code>, which you do not have directly — you have that <code>h.union h₁</code> is disjoint from <code>h₂</code>, and that <code>h</code> is disjoint from <code>h₁</code>. Take the first apart and put the pieces back together the other way. The wand then delivers <code>R</code> at a heap bracketed the opposite way from the goal's, and the two are equal because union is associative. In <code>wand_uncurry</code> every one of those three steps happens in reverse: the bundled disjointness you must take apart is the one you were handed, the one you must build is the one the inner wand demands, and the bracketing that needs correcting is the goal's rather than the result's.",
       "One <code>intro</code> that goes all the way through both wands, then <code>obtain</code> on a bridge, then a <code>have</code> building the disjointness the wand needs with the other bridge, then a <code>have</code> cashing the wand, then <code>rw [union_assoc]</code>, then <code>exact</code>. The mirror uses the same bridges the other way round and <code>rw [← union_assoc]</code>.",
       "<code>intro σ h hw h₁ hd₁ hp h₂ hd₂ hq</code> — nine names, because there are three <code>∀</code>s in the goal. Then <code>obtain ⟨hdh2, hd12⟩ := disjoint_union_left.mp hd₂</code>, since <code>hd₂ : (h.union h₁).disjoint h₂</code> has the union on the left."
     ],
     sol:"theorem wand_curry (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R) := by\n  intro σ h hw h₁ hd₁ hp h₂ hd₂ hq\n  obtain ⟨hdh2, hd12⟩ := disjoint_union_left.mp hd₂\n  have hdd : Heap.disjoint h (Heap.union h₁ h₂) :=\n    disjoint_union_right.mpr ⟨hd₁, hdh2⟩\n  have hR := hw (Heap.union h₁ h₂) hdd ⟨h₁, h₂, hd12, rfl, hp, hq⟩\n  rw [union_assoc]\n  exact hR\n\ntheorem wand_uncurry (P Q R : Assertion) : (P -∗ (Q -∗ R)) ⊢ (P ∗ Q) -∗ R := by\n  intro σ h hw h' hd ⟨h₁, h₂, hd₁₂, hu, hp, hq⟩\n  subst hu\n  obtain ⟨hdh1, hdh2⟩ := disjoint_union_right.mp hd\n  have hR := hw h₁ hdh1 hp h₂ (disjoint_union_left.mpr ⟨hdh2, hd₁₂⟩) hq\n  rw [← union_assoc]\n  exact hR",
     solNote:"The two proofs are mirror images, and the mirror is exact: <code>disjoint_union_left.mp</code> against <code>disjoint_union_right.mp</code>, <code>disjoint_union_right.mpr</code> against <code>disjoint_union_left.mpr</code>, <code>rw [union_assoc]</code> against <code>rw [← union_assoc]</code>. Where one takes a bundled disjointness apart, the other builds one.",
     expl:"Each direction has the same three obligations: produce the heap the wand you hold wants, produce a proof that it is disjoint from your own, and reconcile the bracketing of the result with the bracketing of the goal. The first is a union, the second is a bridge used twice in opposite directions, and the third is one rewrite with <code>union_assoc</code>. Nothing else happens in either proof.",
     walk:[
       {tac:'intro σ h hw h₁ hd₁ hp h₂ hd₂ hq', h:"Nine names: three for the entailment, three for the outer wand, three for the inner one. The goal is <code>R σ ((h.union h₁).union h₂)</code> — left-bracketed, because each wand unioned its visitor onto the right of what was already there."},
       {tac:'obtain ⟨hdh2, hd12⟩ := disjoint_union_left.mp hd₂', h:"<code>hd₂ : (h.union h₁).disjoint h₂</code>. The union is on the left of <code>Heap.disjoint</code>, so <code>disjoint_union_left</code> is the bridge, and <code>.mp</code> takes the bundle apart into <code>h.disjoint h₂</code> and <code>h₁.disjoint h₂</code>. Both halves are used, one in each of the next two lines."},
       {tac:'have hdd : Heap.disjoint h (Heap.union h₁ h₂) :=', h:"The disjointness the wand you hold will demand. Its union is on the <i>right</i> of <code>Heap.disjoint</code>, so the other bridge applies, and this time in the building direction."},
       {tac:'  disjoint_union_right.mpr ⟨hd₁, hdh2⟩', h:"<code>hd₁ : h.disjoint h₁</code> came from the outer <code>intro</code>; <code>hdh2 : h.disjoint h₂</code> came from the <code>obtain</code>. Nothing else in the context would have done."},
       {tac:'have hR := hw (Heap.union h₁ h₂) hdd ⟨h₁, h₂, hd12, rfl, hp, hq⟩', h:"The wand cashed. Its three arguments are the visitor's heap, the disjointness built on the previous line, and a proof that <code>P ∗ Q</code> holds there — a six-slot bracket whose equation is <code>rfl</code> because the heap was named as that very union. The result is <code>R σ (h.union (h₁.union h₂))</code>: right-bracketed."},
       {tac:'rw [union_assoc]', h:"The goal is left-bracketed and <code>hR</code> is right-bracketed. <code>union_assoc</code> rewrites the goal into the shape <code>hR</code> has. This is the only line in the proof where a fact about <code>Heap.union</code> other than a disjointness is used."},
       {tac:'exact hR', h:"The two now agree as terms."},
       {tac:"intro σ h hw h' hd ⟨h₁, h₂, hd₁₂, hu, hp, hq⟩", h:"The mirror. Six names again, but the last of them is a six-slot pattern rather than a name, because the visitor's assertion is <code>P ∗ Q</code> and it arrives already split."},
       {tac:'subst hu', h:"<code>hu : h' = h₁.union h₂</code>. Substituting removes <code>h'</code> from the context and puts the union in its place everywhere, including in <code>hd</code>, which becomes <code>h.disjoint (h₁.union h₂)</code> — exactly the bundled form the next line takes apart."},
       {tac:'obtain ⟨hdh1, hdh2⟩ := disjoint_union_right.mp hd', h:"Union on the right of <code>Heap.disjoint</code> this time, so the other bridge. The two halves are <code>h.disjoint h₁</code> and <code>h.disjoint h₂</code>."},
       {tac:'have hR := hw h₁ hdh1 hp h₂ (disjoint_union_left.mpr ⟨hdh2, hd₁₂⟩) hq', h:"The wand cashed twice in one term, because <code>hw</code> is a wand whose conclusion is a wand. The second cashing needs <code>(h.union h₁).disjoint h₂</code>, which nothing supplies directly; the bridge builds it in the <code>_left</code> direction out of the two facts to hand. The result is <code>R σ ((h.union h₁).union h₂)</code>."},
       {tac:'rw [← union_assoc]', h:"The arrow is reversed because this time it is the goal that is right-bracketed and the hypothesis that is left-bracketed. Same lemma, opposite direction."},
       {tac:'exact hR', h:"Done. Neither proof ever looks at what <code>P</code>, <code>Q</code> or <code>R</code> are."}
     ],
     deep:[
       {t:'state', cap:'The context of <code>wand_curry</code> after the nine-name <code>intro</code>, printed once here so the trace below can show goal lines only. Every later step adds hypotheses to this and changes nothing in it.',
        src:"P Q R : Assertion\nσ : Store\nh : Heap\nhw : (P ∗ Q -∗ R) σ h\nh₁ : Heap\nhd₁ : h.disjoint h₁\nhp : P σ h₁\nh₂ : Heap\nhd₂ : (h.union h₁).disjoint h₂\nhq : Q σ h₂\n⊢ R σ ((h.union h₁).union h₂)"},
       {t:'trace', title:'wand_curry — what each step adds (goal line and new hypotheses only)',
        start:"⊢ R σ ((h.union h₁).union h₂)",
        steps:[
          {tac:'obtain ⟨hdh2, hd12⟩ := disjoint_union_left.mp hd₂',
           state:"hdh2 : h.disjoint h₂\nhd12 : h₁.disjoint h₂\n⊢ R σ ((h.union h₁).union h₂)",
           h:"The goal is untouched. All that has happened is that a bundled disjointness has become two separate ones, and both are needed."},
          {tac:'have hdd : Heap.disjoint h (Heap.union h₁ h₂) := disjoint_union_right.mpr ⟨hd₁, hdh2⟩',
           state:"hdd : h.disjoint (h₁.union h₂)\n⊢ R σ ((h.union h₁).union h₂)",
           h:"The ticket the wand will ask for. The bundle taken apart on the previous line and the bundle built on this one are different bundles, and that regrouping is the entire arithmetic of the proof."},
          {tac:'have hR := hw (Heap.union h₁ h₂) hdd ⟨h₁, h₂, hd12, rfl, hp, hq⟩',
           state:"hR : R σ (h.union (h₁.union h₂))\n⊢ R σ ((h.union h₁).union h₂)",
           h:"The two lines differ only in bracketing. Everything before this point was about getting the wand to fire at all."},
          {tac:'rw [union_assoc]',
           state:"⊢ R σ (h.union (h₁.union h₂))",
           h:"Goal and hypothesis now agree, and <code>exact hR</code> closes it."}
        ],
        done:'No goals.'},
       {t:'p', h:"The corresponding shape in <code>wand_uncurry</code> is the same picture read backwards, with one extra move at the start: <code>subst hu</code>, which is what turns the visitor's opaque heap <code>h'</code> into the union its own star says it is. Without that substitution the disjointness hypothesis <code>hd</code> still mentions <code>h'</code> and neither bridge applies to it."},
       {t:'code', tag:'illustration', cap:'A corollary that costs one line, since currying twice in the other order is the same thing after a commutation. <code>wand_mono</code> is applied contravariantly — <code>star_comm Q P : Q ∗ P ⊢ P ∗ Q</code> goes on the left of the wand — which is the variance of the previous exercise being spent.',
        src:"example (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ Q -∗ (P -∗ R) :=\n  entails_trans (wand_mono (star_comm Q P) (entails_refl R)) (wand_curry Q P R)"}
     ],
     pitfall:"Choosing the bridge by the direction of the proof rather than by the shape of the hypothesis. In <code>wand_curry</code> the hypothesis is <code>hd₂ : (h.union h₁).disjoint h₂</code>; reaching for <code>disjoint_union_right.mp</code> gives <code>Application type mismatch: The argument hd₂ has type (h.union h₁).disjoint h₂ but is expected to have type Heap.disjoint ?m.20 (Heap.union ?m.21 ?m.22)</code>. The metavariables in the expected type are the tell: Lean is showing you the shape it wanted and could not find.",
     variants:"Omit <code>rw [union_assoc]</code> and everything else compiles, ending in <code>Type mismatch: … has type R σ (h.union (h₁.union h₂)) but is expected to have type R σ ((h.union h₁).union h₂)</code>. The proof is complete apart from a bracketing, which is a good description of what currying a resource costs. · The two theorems together are an equivalence, and stating it as one <code>⊣⊢</code> is <code>⟨wand_curry P Q R, wand_uncurry P Q R⟩</code>. · Drop the disjointness conjunct from <code>∗</code> — Unit 14's <code>starNoDisj</code> — and <code>wand_curry</code> still compiles with a five-slot bracket, while <code>wand_uncurry</code> does not: its five-name pattern has no <code>hd₁₂</code> to give, and Lean reports <code>Unknown identifier `hd₁₂`</code> at the line that builds the second visitor's disjointness. The direction that <i>consumes</i> a star survives; the direction that <i>builds</i> one is where the separation is spent. That is the same asymmetry <code>wand_intro</code> and <code>wand_elim</code> showed at the start of the unit, one level up."
    },

    /* ================================================== close ==== */

    {t:'dod', h:"You can read <code>P -∗ Q</code> aloud as a claim about the memory you hold, name the three heaps in its definition and say what each one is for. You can say why the pointwise lift of implication is the wrong connective and produce the heap that refutes modus ponens for it. You can prove <code>wand_intro</code> and <code>wand_elim</code>, recognise them as currying and uncurrying, and say which of the two spends the disjointness. You can prove the adjunction from those two lemmas without opening a definition, and say what it means for a right adjoint to be determined up to equivalence. You can read the variance of <code>-∗</code> off its definition and refute the version with a hypothesis reversed. You can say why cashing a wand consumes its argument and an implication does not. And you can hand a piece of a data structure out and take it back, in one line each, naming the assertion you hold in between."},

    {t:'p', h:"The assertion language is complete: <code>emp</code>, <code>↦</code>, <code>∗</code>, <code>-∗</code>, the classical connectives, recursion. The <i>language</i> is not — <code>ite</code> and <code>loop</code> have sat in <code>Cmd</code> since Unit 18 and have never been used, and the moment they are, a distinction that has been invisible becomes essential."}

  ]
});
