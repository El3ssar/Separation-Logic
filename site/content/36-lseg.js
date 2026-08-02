registerChapter({
  id: 'lseg',
  num: '33',
  phase: 'Phase 7 · Unbounded structures',
  title: 'Segments, and the theorem that joins them',
  blurb: 'A lab. Define the piece of a list between two addresses, prove that two adjacent pieces make one, and let a proof you cannot finish tell you the definition was wrong.',

  orient: {
    youWill: [
      'Define <code>lseg xs start finish</code> and say exactly which cells it owns — and which one it deliberately does not.',
      'Prove <code>aExists_mono</code>, and use it to apply an entailment underneath an existential binder.',
      'Prove <code>lseg_append</code>: two adjacent segments make one. Its inductive step is six lines built from four named lemmas, with no heap, no union and no disjointness in it.',
      'Prove <code>lseg_listRep</code>, and read its structural identity with the previous proof as evidence that the two definitions line up.',
      'Take a definition that looks right, watch the same six lines fail on it, read the goal, and produce the heap that shows the theorem is false and not only unproved.',
      'Say what induction on a list has in common with induction on a derivation, and where the two differ.',
      'State and prove, on your own, what a list at the null pointer must be.'
    ],
    needs: [
      'Unit 32: <code>node</code>, <code>listRep</code>, and the double reading.',
      'Unit 15: <code>star_mono_left</code>, <code>star_mono_right</code>, <code>star_exists_left</code>.',
      'Unit 16: <code>star_assoc_left</code>.',
      'Unit 12: <code>aExists</code>, <code>entails_refl</code>, <code>entails_trans</code>, <code>⊣⊢</code>.',
      'Unit 20: <code>induction xs with | nil | cons x xs ih</code>, and why the induction hypothesis has to be general.'
    ],
    payoff: 'Every loop that walks a data structure is verified against an invariant of the form <i>this much is behind me, that much is still in front of me</i>. <code>lseg_append</code> is what maintains such an invariant, and the shape of its proof is the first real dividend of the algebra Module 3 spent six units building.'
  },

  blocks: [

    /* =============================================================== brief ==== */

    {t:'p', h:"Take the traversal seriously. A program walking a linked list holds a pointer <code>cur</code> that starts at the head and advances one node at a time. At any moment memory contains the whole list, but the program's knowledge of it comes in two parts: the nodes from the head up to <code>cur</code>, which it has already been through, and the nodes from <code>cur</code> onwards, which it has not. Of the two, one is describable with what you have. The nodes from <code>cur</code> onwards form a chain that ends at null, so <code>listRep</code> says exactly what they are. The nodes behind <code>cur</code> form a chain that ends at <code>cur</code>, and nothing in Unit 32 can say what that is."},

    {t:'p', h:"This lab builds the assertion for it. You will define <code>lseg xs start finish</code>, prove one lemma that lets an entailment be applied under an existential, and then prove the theorem the whole subject turns on: two adjacent segments joined end to end make one segment. Its inductive step is six lines long, mentions no heap, no union and no disjointness, and cites four lemmas — three of them proved in Units 12 to 16, one of them proved here in the first exercise. Then you will take the one clause of the definition that was a genuine choice, change it to the most plausible alternative, watch those six lines die, and read the dead goal to find out what you got wrong."},

    /* =============================================================== lseg ==== */

    {t:'sec', s:'The piece between two addresses'},

    {t:'p', h:"<code>listRep xs p</code> is anchored at both ends. It starts at <code>p</code>, which is an argument, and it stops at null, which is written into the <code>nil</code> clause. Only one of those is negotiable, and loosening it is the whole definition: make the far end an argument too."},

    {t:'code', cap:'Three arguments, two of them addresses. <code>start</code> is where the chain begins and <code>finish</code> is where it stops — and stopping is all <code>finish</code> does, since the recursion passes it down unchanged.',
     src:"def lseg : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next =>\n        pure (fun _ => start ≠ 0) ∗ node start x next ∗ lseg xs next finish"},

    {t:'cmp',
     left: {t:'Unit 32 — the complete list', src:"def listRep : List Nat → Loc → Assertion\n  | [],      p => pure (fun _ => p = 0)\n  | x :: xs, p =>\n      aExists fun next =>\n        pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next",
            h:"The empty case pins the address to null. That is what makes it a description of a whole list: follow the chain and it terminates at <code>0</code>."},
     right:{t:'This unit — the segment', src:"def lseg : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next =>\n        pure (fun _ => start ≠ 0) ∗ node start x next ∗ lseg xs next finish",
            h:"The empty case pins the address to <code>finish</code> instead. Follow the chain and it terminates wherever the caller said it should."}},

    {t:'p', h:"So a segment is <b>half-open</b>: <code>lseg xs p q</code> owns the cells of the nodes from <code>p</code> up to but <i>not including</i> whatever lives at <code>q</code>. The <code>nil</code> clause is where that is decided. It is <code>pure</code>, so it owns nothing at all, and it says only that the walk has arrived at <code>q</code> — it does not claim a node there, or claim there is one, or claim there is not. Address <code>q</code> is outside the assertion altogether. That is the property the whole unit runs on: two segments can be laid end to end without either of them owning the address where they meet."},

    {t:'svg', cap:'<code>lseg [10, 20] 1 5</code>. Four owned cells at addresses 1–4, and address 5 outside the assertion — the segment says a walk from 1 arrives there and says nothing whatever about what is stored there, or whether anything is.',
     src:"<svg viewBox=\"0 0 620 186\" role=\"img\" aria-label=\"A list segment occupying four heap cells at addresses one to four, whose last next field points at address five; address five is drawn outside the segment and is not owned\">\n  <defs>\n    <marker id=\"ah36\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"currentColor\"/>\n    </marker>\n  </defs>\n  <g class=\"dg\">\n    <g class=\"dg-t sm\">\n      <text x=\"84\"  y=\"26\" text-anchor=\"middle\" class=\"dg-note\">1</text>\n      <text x=\"144\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">2</text>\n      <text x=\"274\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">3</text>\n      <text x=\"334\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">4</text>\n      <text x=\"484\" y=\"26\" text-anchor=\"middle\" class=\"dg-note\">5</text>\n    </g>\n    <g class=\"dg-cells\">\n      <rect class=\"a\" x=\"54\"  y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"b\" x=\"114\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"a\" x=\"244\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <rect class=\"b\" x=\"304\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\"/>\n      <text x=\"84\"  y=\"59\" text-anchor=\"middle\" class=\"dg-t\">10</text>\n      <text x=\"144\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">3</text>\n      <text x=\"274\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">20</text>\n      <text x=\"334\" y=\"59\" text-anchor=\"middle\" class=\"dg-t\">5</text>\n    </g>\n    <rect x=\"454\" y=\"36\" width=\"60\" height=\"34\" rx=\"5\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.2\" stroke-dasharray=\"4 3\" opacity=\"0.5\"/>\n    <text x=\"484\" y=\"59\" text-anchor=\"middle\" class=\"dg-note\">?</text>\n    <path d=\"M 144 76 L 144 100 L 270 100 L 270 76\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah36)\"/>\n    <path d=\"M 334 76 L 334 100 L 480 100 L 480 76\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah36)\"/>\n    <path d=\"M 28 53 L 48 53\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah36)\"/>\n    <g class=\"dg-t sm\">\n      <text x=\"209\" y=\"132\" text-anchor=\"middle\" class=\"dg-note\">owned by the segment</text>\n      <text x=\"484\" y=\"132\" text-anchor=\"middle\" class=\"dg-note\">not owned</text>\n    </g>\n    <text x=\"28\" y=\"166\" class=\"dg-lab\">start = 1</text>\n    <text x=\"440\" y=\"166\" class=\"dg-lab\">finish = 5</text>\n  </g>\n</svg>"},

    {t:'p', h:"The alternative is a <b>closed</b> segment, one that owns the node at <code>finish</code> as well. It is a coherent definition and it destroys the theorem this unit exists for. Lay two closed segments end to end and the node at the junction is claimed by both, so the <code>∗</code> joining them can never be satisfied: <code>∗</code> cuts the heap into two disjoint halves, and one cell cannot be in both. That is the phenomenon Unit 14 exhibited as <code>no_star_duplication</code>. The half-open convention is what makes joining possible, and it is the same convention that makes <code>[a, b)</code> the useful kind of interval."},

    {t:'code', tag:'illustration', cap:'A two-element segment written out. The proof is <code>entails_refl _</code>, because the two sides are one term: applying <code>lseg</code> to a literal <code>::</code> selects the second clause, twice, and then to <code>[]</code> selects the first.',
     src:"example (p q : Loc) :\n    lseg [10, 20] p q ⊢\n      aExists fun n₁ => pure (fun _ => p ≠ 0) ∗ node p 10 n₁ ∗\n        aExists fun n₂ => pure (fun _ => n₁ ≠ 0) ∗ node n₁ 20 n₂ ∗\n          pure (fun _ => n₂ = q) :=\n  entails_refl _"},

    {t:'p', h:"Read the last line of that. The chain ends with a claim that <code>n₂</code>, the address in the final next field, <i>is</i> <code>q</code> — and with no cells. Everything else is two nodes' worth of memory. The <code>nil</code> clause is a statement of where you have got to, not a piece of the structure."},

    {t:'p', h:"One clause has not been justified: the <code>cons</code> case asserts <code>start ≠ 0</code>, and it is not obvious that this is the right thing for it to assert. It is the only line of the definition that was a real choice, and there are two other plausible fillings for the slot. Which one belongs there is decided later on this page, by a proof, and by which of the three candidates survives it."},

    /* =================================================== under the binder ==== */

    {t:'sec', s:'Getting under the binder'},

    {t:'p', h:"Every fact about a non-empty segment has to reach inside an <code>aExists</code>, because that is the outermost thing in the <code>cons</code> clause. Unit 15 supplies one move for that — <code>star_exists_left</code> turns <code>aExists P ∗ Q</code> into <code>aExists (fun x => P x ∗ Q)</code>, hoisting the quantifier out of the star. It leaves you facing <code>aExists P' ⊢ aExists Q'</code>, and there is nothing in the algebra that gets any further: every lemma in Units 14 to 17 relates two assertions, and here the two assertions are quantifiers whose <i>bodies</i> are what you know how to compare."},

    {t:'p', h:"What is wanted is that <code>aExists</code> is monotone: improve the body pointwise and you improve the whole. That is one theorem, and you have already proved it once, for plain propositions, in Unit 01."},

    {t:'cmp',
     left: {t:'Unit 01, exercise x05', src:"theorem exists_mono {P Q : Nat → Prop} (h : ∀ n, P n → Q n) :\n    (∃ n, P n) → ∃ n, Q n := by\n  intro hp\n  obtain ⟨n, hn⟩ := hp\n  exact ⟨n, h n hn⟩",
            h:"Take the witness out of the hypothesis, improve the body, put the same witness back. Three lines, no choices."},
     right:{t:'This unit', src:"theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :\n    aExists P ⊢ aExists Q := by\n  intro σ hh ⟨x, hp⟩\n  exact ⟨x, h x σ hh hp⟩",
            h:"The same three moves with a store and a heap threaded through, and <code>Nat</code> widened to <code>Sort u</code> because an assertion may be quantified over anything."}},

    {t:'p', h:"The two proofs are the same proof. What changed is that an entailment is a function of three arguments rather than one, so the pointwise hypothesis has to be applied to the store and the heap before it can be applied to the premise — which is why the last line reads <code>h x σ hh hp</code> and not <code>h x hp</code>."},

    {t:'p', h:"Prove it, together with the empty-segment interface. The second names what an empty segment is worth, so that a caller can read it off without unfolding the definition."},

    {t:'ex',
     id:'x66',
     name:'aExists_mono and lseg_nil_iff',
     why:"<code>aExists_mono</code> is the second line of both main proofs on this page, and there is no way round it: the <code>cons</code> clause of <code>lseg</code> begins with a quantifier, so every algebraic proof about a non-empty segment must work underneath one. <code>lseg_nil_iff</code> is the other end of the same definition, and it buys no proof — nothing in this course cites it, and both main proofs open the empty segment's <code>pure</code> by hand instead. What it buys is a name for the empty-segment interface, on the terms Unit 32 set out for its three fold/unfold lemmas: a named identity is what a later proof cites instead of unfolding a definition, and what tells you which side of the identity you had wrong when a rewrite fails.",
     setup:"Two theorems. The first is Unit 01's <code>exists_mono</code> with a store and a heap carried through; write it in tactic mode and let <code>intro</code> open the existential in the premise. The second is an <code>⊣⊢</code>, which Unit 12 defined as a pair of entailments, so it is a two-slot bracket and neither slot needs a tactic.",
     goal:"theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :\n    aExists P ⊢ aExists Q := by\n  sorry\n\ntheorem lseg_nil_iff (p q : Loc) : lseg [] p q ⊣⊢ pure (fun _ => p = q) :=",
     hints:[
       "Unfold both goals. <code>aExists P ⊢ aExists Q</code> is <code>∀ σ h, (∃ x, P x σ h) → ∃ x, Q x σ h</code>: given a store, a heap and a witness that the premise holds at some <code>x</code>, produce a witness that the conclusion does. For the second, <code>lseg [] p q</code> is what the first clause of the definition returns, and the right-hand side is that clause's body.",
       "The shape of the first argument is: take the witness apart, improve what it witnesses, put the same witness back. Nothing chooses a new witness, because nothing could — the only <code>x</code> available is the one the premise supplied. The second is two entailments between assertions that are the same assertion.",
       "For the first: <code>intro</code> with a pattern for the premise, then <code>exact</code> with an anonymous constructor. For the second: <code>entails_refl</code>, twice, inside a two-slot bracket.",
       "Open with <code>intro σ hh ⟨x, hp⟩</code>. That names the store, the heap and the two components of the existential, leaving <code>hp : P x σ hh</code> and the goal <code>aExists Q σ hh</code>. Do not call the heap <code>h</code>: that name is already the pointwise hypothesis, and shadowing it makes the last line unwriteable."
     ],
     sol:"theorem aExists_mono {α : Sort u} {P Q : α → Assertion} (h : ∀ x, P x ⊢ Q x) :\n    aExists P ⊢ aExists Q := by\n  intro σ hh ⟨x, hp⟩\n  exact ⟨x, h x σ hh hp⟩\n\ntheorem lseg_nil_iff (p q : Loc) : lseg [] p q ⊣⊢ pure (fun _ => p = q) :=\n  ⟨entails_refl _, entails_refl _⟩",
     solNote:"Four lines for the two of them, and the second theorem's content is entirely in its statement — the same situation as Unit 32's three fold/unfold lemmas, and for the same reason.",
     expl:"<code>aExists P</code> is <code>fun σ h => ∃ x, P x σ h</code>, so an entailment between two of them is a function taking a store, a heap and a proof of an existential. <code>intro</code> reaches through both the folded <code>Entails</code> and the folded <code>aExists</code> to find three binders and then a pair. The witness <code>x</code> is handed straight back; the only work is applying the pointwise hypothesis at that <code>x</code>, at this store and at this heap. <code>lseg_nil_iff</code> needs no work at all: applying <code>lseg</code> to <code>[]</code> reduces to the first clause, so both directions are reflexivity of <code>⊢</code>.",
     walk:[
       {tac:'intro σ hh ⟨x, hp⟩',
        h:"Three <code>intro</code>s, the third against a pattern. The store and the heap come from <code>Entails</code>; the pattern splits the premise into the witness <code>x</code> and the proof <code>hp : P x σ hh</code> that the body holds at it. The heap is called <code>hh</code> because <code>h</code> is taken."},
       {tac:'exact ⟨x, h x σ hh hp⟩',
        h:"Builds the goal's existential. The witness is the one that came in, unchanged — nothing in the statement could produce another. The second slot wants <code>Q x σ hh</code>; <code>h x</code> is the entailment <code>P x ⊢ Q x</code>, which is a function of a store, a heap and a premise, so it is applied to all three."},
       {tac:'⟨entails_refl _, entails_refl _⟩',
        h:"<code>⊣⊢</code> is a conjunction of two entailments, so this is one bracket with two slots. Both sides of both entailments are the same term after <code>lseg</code> is applied to <code>[]</code>, so reflexivity closes each; the underscore is the assertion, which unification reads off the goal."}
     ],
     deep:[
       {t:'trace', title:'aExists_mono, both states',
        start:"α : Sort u\nP Q : α → Assertion\nh : ∀ (x : α), P x ⊢ Q x\n⊢ aExists P ⊢ aExists Q",
        steps:[
          {tac:'intro σ hh ⟨x, hp⟩',
           state:"α : Sort u\nP Q : α → Assertion\nh : ∀ (x : α), P x ⊢ Q x\nσ : Store\nhh : Heap\nx : α\nhp : P x σ hh\n⊢ aExists Q σ hh",
           h:"Four new hypotheses from one line, and the goal is still displayed folded as <code>aExists Q σ hh</code>: <code>intro</code> unfolded the premise far enough to find a pair inside it and left the conclusion alone, because nothing had asked it to."},
          {tac:'exact ⟨x, h x σ hh hp⟩',
           state:"No goals.",
           h:"The bracket is checked against the folded goal, which reduces to <code>∃ x, Q x σ hh</code> during the check. Reduction under <code>exact</code> is doing the same job the <code>show</code> would do, without a line of proof."}
        ],
        done:'No goals.'},
       {t:'p', h:"The statement of <code>lseg_nil_iff</code> is worth reading against the theorem it does not state. <code>lseg [] p q ⊣⊢ pure (fun _ => p = q)</code> is an equivalence of <i>assertions</i>, which is the relation Unit 12 introduced because <code>⊢</code> is a preorder and not a partial order. The corresponding <code>=</code> between the two assertions is also true here, and provable by <code>rfl</code> in an <code>example</code> — but not in a <code>theorem</code>, for the reason Unit 32 set out under its own <code>cons</code> identity. The <code>⊣⊢</code> form has neither problem and is what the congruence lemmas of Unit 15 consume."}
     ],
     pitfall:"Naming the heap <code>h</code>. It is the obvious name and every other proof in the course uses it, but here <code>h</code> is already the pointwise hypothesis, and <code>intro σ h ⟨x, hp⟩</code> shadows it. The error lands on the last line and is about types rather than about names: <code>Application type mismatch: The argument x has type α of sort Sort u but is expected to have type Loc of sort Type in the application h x</code> — because <code>h</code> now denotes a heap, so <code>h x</code> is a heap lookup and <code>x</code> is being read as an address. Rename the heap, not the witness.",
     variants:"The same statement for <code>aForall</code> — Unit 15's <code>star_forall_left</code> is where that quantifier was defined — is true, but not by the same three moves. With <code>∃</code> you take the witness out of the premise and hand it back; with <code>∀</code> there is no witness to take, so you receive the point and pass it on. Compiled: <code>intro σ hh hp</code> then <code>exact fun x => h x σ hh (hp x)</code>. Monotonicity is not where <code>∀</code> and <code>∃</code> differ; crossing a star is, and Unit 15 gives the reason. · Make <code>P</code> and <code>Q</code> explicit rather than implicit and every call site on this page grows two underscores, since both are always determined by the goal. · Take <code>α : Type</code> instead of <code>Sort u</code> and the theorem still covers everything this unit needs — compiled, and both main proofs go through against it, because every existential on this page is over <code>Loc</code>. What it stops covering is an assertion quantified over a proposition, which is the case <code>Sort u</code> was chosen for in Unit 12. · Keep only the left-to-right half of <code>lseg_nil_iff</code> and you can still read <code>p = q</code> off an empty segment but can no longer build one — and neither proof on this page notices, because neither cites the lemma in either direction. That is the exact measure of what an interface lemma is: insurance against a future caller, not a step in a present argument."
    },

    /* ============================================== the worked example ==== */

    {t:'sec', s:'The worked example: two segments make one'},

    {t:'p', h:"Here is the theorem. A segment from <code>p</code> to <code>q</code> holding <code>xs</code>, laid beside a segment from <code>q</code> to <code>r</code> holding <code>ys</code>, is a segment from <code>p</code> to <code>r</code> holding <code>xs ++ ys</code>."},

    {t:'txt', cap:'What the <code>∗</code> contributes: the two segments own disjoint memory, so laying them end to end really does produce one chain and not two overlapping ones. The address <code>q</code> where they meet is owned by neither, which is why neither has to give it up.',
     src:"        xs                     ys\n  p ──────────▶ q          q ──────────▶ r\n\n                    ∗\n\n                  xs ++ ys\n  p ─────────────────────────────────────▶ r"},

    {t:'p', h:"The proof is by induction on <code>xs</code>. Unit 20 met three inductions — over a number, over a list, over a derivation — and used the third one in anger; this is the first place the second is needed for real, and the difference is worth naming. Induction on a derivation takes apart a proof that something happened and asks what the last rule was. Induction on a list takes apart a piece of <i>data</i> and asks what the head constructor was. Here the data is the first list of values, so the two cases are <code>xs = []</code> and <code>xs = x :: xs'</code>, and the induction hypothesis is the theorem for the shorter list. Nothing is being taken apart except the argument the definition recurses on, which is why the induction matches the definition exactly."},

    {t:'p', h:"One thing has to be right before the induction starts. The <code>cons</code> case will need the hypothesis at a <i>different</i> starting address — at whatever the head node's next field holds — so the hypothesis has to be general in that address. The statement quantifies over <code>ys</code>, <code>p</code>, <code>q</code> and <code>r</code> inside the <code>∀</code>, and only <code>xs</code> is introduced before <code>induction</code> runs. That is Unit 20's lesson written into the statement rather than supplied by <code>generalizing</code>."},

    {t:'code', tag:'verified', cap:'The inductive step, from the shipped proof. Eight tactic lines, and not one of them mentions a heap, a union, a disjointness or a store.',
     src:"| cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)"},

    {t:'p', h:"The first <code>refine</code> is an identity. <code>star_mono_left</code> applied to <code>entails_refl</code> improves the left conjunct of a star to itself, so the goal it leaves is the goal it was given, and the proof compiles with the line deleted — which is also the evidence that it does nothing, since <code>lseg_listRep</code>, two exercises below, is the same proof without it. It is left in place because the shipped Lean is the shipped Lean; the six lines that follow are the argument, and the trace starts after it."},

    {t:'state', cap:'The context throughout the inductive step, printed once. It does not change between the steps below except for one addition, which is named where it happens.',
     src:"case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc"},

    {t:'trace', title:'The inductive step, goal lines only — the six context lines above are unchanged and are omitted, and the one line that is added along the way is shown where it appears',
     start:"⊢ lseg (x :: xs) p q ∗ lseg ys q r ⊢ lseg (x :: xs ++ ys) p r",
     steps:[
       {tac:'refine entails_trans (star_exists_left _ _) ?_',
        state:"⊢ (aExists fun x_1 => ((_root_.pure fun x => p ≠ 0) ∗ node p x x_1 ∗ lseg xs x_1 q) ∗ lseg ys q r) ⊢\n    lseg (x :: xs ++ ys) p r",
        h:"The left-hand side has unfolded and the quantifier has come out of the star. Before this line the existential was buried inside the first conjunct, where no lemma could see it; after it, the whole premise is one <code>aExists</code>. The bound variable prints as <code>x_1</code> rather than <code>next</code>: the definition's binder name is not carried through <code>star_exists_left</code>, and Lean's fallback name <code>x</code> is already the head value in the context, so it numbers the new one apart instead of shadowing. The next line renames it <code>n</code>. A reader who reaches for <code>star_assoc_left</code> first gets <code>Application type mismatch: The argument star_assoc_left ?m.118 ?m.119 ?m.120 has type (?m.118 ∗ ?m.119) ∗ ?m.120 ⊢ ?m.118 ∗ ?m.119 ∗ ?m.120 but is expected to have type lseg (x :: xs) p q ∗ lseg ys q r ⊢ ?m.116</code> — the left conjunct is a quantifier, not a star, so there is nothing to reassociate yet."},
       {tac:'refine aExists_mono (fun n => ?_)',
        state:"n : Nat\n⊢ ((_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg (xs.append ys) n r",
        h:"This is the line that does the reaching-inside. The goal was an entailment between two quantifiers; it is now an entailment between their bodies, at an arbitrary <code>n</code> — the one new context line. From here to the end nothing is quantified and everything is a star. The conclusion has also started printing <code>xs.append ys</code> where the statement wrote <code>xs ++ ys</code>: <code>++</code> is notation for <code>List.append</code>, and the printing convention from the goal-display support page writes <code>List.append xs ys</code> as <code>xs.append ys</code>. It is the same term; nothing was rewritten."},
       {tac:'refine entails_trans (star_assoc_left _ _ _) ?_',
        state:"⊢ (_root_.pure fun x => p ≠ 0) ∗ (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg (xs.append ys) n r",
        h:"Re-bracketing. The premise was <code>(A ∗ B) ∗ C</code> with <code>A</code> the non-nullness claim; it is now <code>A ∗ (B ∗ C)</code>, which puts the same <code>A</code> at the head of both sides of the entailment. That is what makes the next line possible."},
       {tac:'refine star_mono_right _ ?_',
        state:"⊢ (node p x n ∗ lseg xs n q) ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r",
        h:"Both sides began with the identical conjunct, so it is dropped and the obligation is what is left of each. The head node goes the same way two steps later; the non-nullness claim was discharged here, by being the same claim on both sides, and no proposition about <code>p</code> was ever inspected."},
       {tac:'refine entails_trans (star_assoc_left _ _ _) ?_',
        state:"⊢ node p x n ∗ lseg xs n q ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r",
        h:"The same re-bracketing again, now with the node at the head. Two applications of one lemma, and between them one application of monotonicity: that alternation is the whole engine."},
       {tac:'exact star_mono_right _ (ih ys n q r)',
        state:"No goals.",
        h:"The node is common to both sides and comes off; the obligation underneath it is <code>lseg xs n q ∗ lseg ys q r ⊢ lseg (xs ++ ys) n r</code>, which is the induction hypothesis at the four arguments <code>ys</code>, <code>n</code>, <code>q</code>, <code>r</code>. The address it is used at is <code>n</code>, not <code>p</code>, which is why the statement had to quantify over the starting address."}
     ],
     done:'No goals.'},

    {t:'p', h:"Count what the six lines used: <code>star_exists_left</code>, <code>aExists_mono</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>, <code>star_assoc_left</code>, <code>star_mono_right</code> — four distinct lemmas in six applications, three of them from Module 3 and one from the exercise above, glued throughout by <code>entails_trans</code>. There is no <code>Heap</code> in the proof, no <code>Heap.union</code>, no <code>Heap.disjoint</code> and no <code>intro σ h</code>. Every disjointness fact the theorem needs was discharged inside <code>star_assoc_left</code>, once, in Unit 16."},

    {t:'p', h:"The route a reader is most likely to take instead is the one Modules 2 and 3 took: open the entailment, destructure the premise into heaps, and build the conclusion. It finishes — the aside below carries the compiled proof — and it costs thirteen lines where the algebra costs six. One <code>intro</code> with the premise fully destructured produces this."},

    {t:'detail', title:'What the semantic route puts in front of you', tag:'aside', open:false,
     blocks:[
       {t:'p', h:"The line is <code>intro ys p q r σ h ⟨h₁, h₂, hd, hu, ⟨n, hA, hB, hdA, huA, ⟨hne, hemp⟩, hnode⟩, hys⟩</code> — one <code>intro</code>, with the star's six slots, an existential inside slot five, and a second six-slot star inside that. It is legal and it compiles."},
       {t:'state', cap:'The context it leaves, in full, in the <code>cons</code> branch. Five heaps, two disjointness facts, two union equations.',
        src:"case cons\nx : Nat\nxs : List Nat\nih : ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nys : List Nat\np q r : Loc\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nn : Nat\nhA hB : Heap\nhdA : hA.disjoint hB\nhuA : h₁ = hA.union hB\nhne : fact (fun x => p ≠ 0) σ hA\nhemp : emp σ hA\nhnode : (node p x n ∗ lseg xs n q) σ hB\nhys : lseg ys q r σ h₂\n⊢ lseg (x :: xs ++ ys) p r σ h"},
       {t:'p', h:"To finish it you must produce the goal's own cut, which means naming a heap for the head node and a heap for the joined tail, proving they are disjoint out of <code>hd</code>, <code>hdA</code> and <code>hemp</code>, and proving their union is <code>h</code> out of <code>hu</code> and <code>huA</code> — which is <code>union_assoc</code> plus two bridge lemmas, and is precisely the work that is already inside <code>star_assoc_left</code>."},
       {t:'code', tag:'illustration', cap:'Compiled. The <code>nil</code> branch is the shipped one; the <code>cons</code> branch is thirteen lines against the algebra\'s six, and every extra line is heap bookkeeping. All five lemmas it cites — <code>union_empty_left</code>, <code>disjoint_empty_left</code>, <code>union_assoc</code>, <code>disjoint_union_left</code>, <code>disjoint_union_right</code> — are about <code>Heap</code>. Not one is about <code>∗</code>.',
        src:"theorem lseg_append_semantic : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq' : p = q := hpq\n      subst hpq'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r σ h ⟨h₁, h₂, hd, hu, ⟨n, hA, hB, hdA, huA, ⟨hne, hemp⟩, hnode⟩, hys⟩\n      have heA : hA = Heap.empty := hemp\n      subst heA\n      rw [union_empty_left] at huA\n      subst huA\n      obtain ⟨hC, hD, hdC, huC, hnd, htl⟩ := hnode\n      subst huC\n      refine ⟨n, Heap.empty, h, disjoint_empty_left _, ?_, ⟨hne, rfl⟩, ?_⟩\n      · rw [union_empty_left]\n      · refine ⟨hC, Heap.union hD h₂, ?_, ?_, hnd, ih ys n q r σ _ ⟨hD, h₂, ?_, rfl, htl, hys⟩⟩\n        · exact disjoint_union_right.mpr ⟨hdC, (disjoint_union_left.mp hd).1⟩\n        · rw [hu, union_assoc]\n        · exact (disjoint_union_left.mp hd).2"},
       {t:'p', h:"The algebraic proof is not shorter by luck. It is shorter because Unit 16 did this bookkeeping once, for all assertions, rather than once per theorem."}
     ]},

    {t:'p', h:"Now write it. The inductive step is above; what the exercise asks for is the other branch, the induction that puts them together, and the discipline of introducing exactly one variable before it."},

    {t:'ex',
     id:'m10-4',
     name:'lseg_append',
     hard:true,
     why:"The classical theorem of the subject. Every loop that walks a list is verified against an invariant saying <i>this much is behind me and that much is in front of me</i>, and every time the loop takes a step, the invariant is restored by moving one node from the front part to the back part — which is an application of this theorem. It is also the measurement the whole of Module 3 was for: the case with content is six lines of named lemmas, and the case with no content is the only one that touches heaps.",
     setup:"The inductive step is worked in full above and you may transcribe it. The <code>nil</code> case is not, and it is the one that goes down to the model: <code>lseg [] p q</code> is a <code>pure</code>, so opening it gives you a proposition <code>p = q</code> and a heap equation, and the goal is the second segment at the whole heap. <code>union_empty_left</code> is Unit 09. Note where <code>intro xs</code> sits relative to <code>induction</code>.",
     goal:"theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by",
     hints:[
       "The statement is a <code>∀</code> over five things followed by an entailment. In the <code>nil</code> case the premise is <code>lseg [] p q ∗ lseg ys q r</code>, which says: the heap splits in two, the left half is empty and <code>p = q</code>, and the right half satisfies <code>lseg ys q r</code>. The goal is <code>lseg ([] ++ ys) p r</code> at the whole heap, and <code>[] ++ ys</code> is <code>ys</code>. So the whole content of the case is that a heap plus nothing is that heap, and that <code>p</code> and <code>q</code> are the same address.",
       "Induct on the first list. The empty case is a bookkeeping identity in the model. The non-empty case peels one node off the front, and the tail of the joined segment is the joined tail — which is the induction hypothesis, used at the address the peeled node points to rather than at the address you started from.",
       "<code>intro xs</code>, then <code>induction xs with | nil => … | cons x xs ih => …</code>. In the <code>nil</code> branch: <code>intro</code> down to the premise, <code>obtain</code> to split the star, <code>subst</code> the two equations you can, then <code>rw</code> with the union equation and <code>union_empty_left</code>. In the <code>cons</code> branch, the block above.",
       "Open with <code>intro xs</code> and nothing else. It leaves <code>xs : List Nat</code> in the context and <code>⊢ ∀ (ys : List Nat) (p q r : Loc), lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r</code> as the goal, so the <code>induction xs with</code> that follows produces a hypothesis quantified over all four. Introduce <code>ys p q r</code> as well and the hypothesis arrives fixed at <code>p</code> with no arguments left to take, so the closing line is <code>exact star_mono_right _ ih</code> — and it fails with <code>Application type mismatch: The argument ih has type lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r but is expected to have type lseg xs n q ∗ lseg ys q r ⊢ lseg (xs.append ys) n r</code>."
     ],
     sol:"theorem lseg_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq' : p = q := hpq\n      subst hpq'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)",
     solNote:"Fifteen lines below the two branch headings, seven of them in the case where nothing happens. If you climbed all four hints and are still stuck, open this and read the <code>nil</code> branch against the trace below; the <code>cons</code> branch is the worked example above, unchanged.",
     expl:"The <code>nil</code> case is entirely in the model and entirely bookkeeping. The premise's left half is <code>pure (fun _ => p = q)</code>, which is a conjunction of a proposition and an emptiness claim; <code>subst</code> spends both — the first replaces <code>q</code> by <code>p</code> and the second replaces the left heap by <code>Heap.empty</code> — and then the union equation plus <code>union_empty_left</code> rewrites the goal's heap to the right half, where the second segment already lives. The <code>cons</code> case never opens the entailment at all: it rewrites the premise into the shape of the conclusion using three lemmas about <code>∗</code> and one about <code>aExists</code>, and hands the remaining obligation to the induction hypothesis.",
     walk:[
       {tac:'intro xs',
        h:"One variable, and this is the load-bearing decision of the whole proof. Everything after <code>xs</code> stays inside the <code>∀</code>, so the induction hypothesis is universally quantified over the list, the three addresses and the second list — which is what the <code>cons</code> branch needs, since it uses the hypothesis at <code>n</code> rather than at <code>p</code>."},
       {tac:'induction xs with',
        h:"Two branches, on the two constructors of <code>List</code>. The goal in each is still the four-fold <code>∀</code> followed by an entailment, since nothing else was introduced."},
       {tac:'      intro ys p q r σ h hstar',
        h:"The <code>nil</code> branch, opened all the way down to the model: four quantified variables, then the store, the heap and the premise. This is the only place in the proof where <code>σ</code> and <code>h</code> appear."},
       {tac:'      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar',
        h:"The star's six slots, with the fifth split further because <code>pure</code> is a conjunction. The disjointness slot is discarded: nothing in this branch needs to know that the empty heap does not overlap anything. What survives is the union equation, the proposition <code>p = q</code>, the emptiness of the left half, and the second segment."},
       {tac:'      have hpq\' : p = q := hpq',
        h:"A definitional restatement, of the kind Unit 22 introduced. <code>hpq</code> has type <code>fact (fun x => p = q) σ h₁</code>, which reduces to <code>p = q</code> but is not displayed that way, and <code>subst</code> matches on the displayed form. Naming the same proof at the reduced type is what makes the next line legal."},
       {tac:'      subst hpq\'',
        h:"Replaces <code>q</code> by <code>p</code> everywhere and deletes the equation. The second segment now runs from <code>p</code>, which is where the joined segment has to start."},
       {tac:'      subst he',
        h:"The other half of the <code>pure</code>: <code>he : emp σ h₁</code> is by definition <code>h₁ = Heap.empty</code>, so this replaces <code>h₁</code> throughout. The union equation becomes <code>h = Heap.empty.union h₂</code>."},
       {tac:'      rw [hu, union_empty_left]',
        h:"Two rewrites in one bracket. The first replaces the goal's heap <code>h</code> by the union; the second collapses the union to <code>h₂</code>. The goal is now the second segment at <code>h₂</code> — with <code>[] ++ ys</code> still written in the list slot, which does not matter, because it reduces to <code>ys</code>."},
       {tac:'      exact hys',
        h:"The premise's right half, unchanged. The whole <code>nil</code> case was: an empty piece was cut off the front of the heap, and putting it back changes nothing."},
       {tac:'  | cons x xs ih =>',
        h:"The other branch. <code>ih</code> is the theorem for <code>xs</code>, still quantified over <code>ys</code> and the three addresses, because those were never introduced."},
       {tac:'      intro ys p q r',
        h:"Four variables and no more. The store and the heap stay inside the entailment for the rest of the proof, which is the difference between this branch and the last one."},
       {tac:'      refine entails_trans (star_mono_left _ (entails_refl (lseg (x :: xs) p q))) ?_',
        h:"An identity: monotonicity applied to reflexivity improves the left conjunct to itself. The goal it leaves is the goal it was handed, and the proof compiles without the line."},
       {tac:'      refine entails_trans (star_exists_left _ _) ?_',
        h:"Unfolds the premise's left conjunct and lifts its <code>aExists</code> out of the star. Before this line the quantifier sat inside one half of a <code>∗</code>, where no lemma in the algebra could reach it; after it the entire premise is a single <code>aExists</code> and the conclusion has not been touched."},
       {tac:'      refine aExists_mono (fun n => ?_)',
        h:"Turns an entailment between two quantifiers into an entailment between their bodies, at an arbitrary <code>n</code> — the one line this branch adds to the context. From here down nothing is quantified and both sides of the goal are stars."},
       {tac:'      refine entails_trans (star_assoc_left _ _ _) ?_',
        h:"Re-brackets the premise from <code>(A ∗ B) ∗ C</code> to <code>A ∗ (B ∗ C)</code>, with <code>A</code> the conjunct <code>pure (fun _ => p ≠ 0)</code>. The conclusion already carried that same <code>A</code> at its head, so after this line the two sides agree on their first conjunct."},
       {tac:'      refine star_mono_right _ ?_',
        h:"Cancels the agreeing first conjunct and leaves what was under it on each side. Nothing proved <code>p ≠ 0</code>: it was the same term on both sides, and monotonicity never looks inside the conjunct it drops."},
       {tac:'      refine entails_trans (star_assoc_left _ _ _) ?_',
        h:"Re-brackets once more, so that the head node <code>node p x n</code> — which both sides also share — comes to the front of the premise instead of being buried in its left half."},
       {tac:'      exact star_mono_right _ (ih ys n q r)',
        h:"Cancels the node, leaving <code>lseg xs n q ∗ lseg ys q r ⊢ lseg (xs ++ ys) n r</code> as the obligation. That is the induction hypothesis at <code>ys</code>, <code>n</code>, <code>q</code>, <code>r</code> — at the address the peeled node points to rather than at <code>p</code>, which is exactly what introducing only <code>xs</code> bought. The trace above shows all six of these goals."}
     ],
     deep:[
       {t:'trace', title:'The nil case, where the heaps are',
        start:"case nil\nys : List Nat\np q r : Loc\nσ : Store\nh : Heap\nhstar : (lseg [] p q ∗ lseg ys q r) σ h\n⊢ lseg ([] ++ ys) p r σ h",
        steps:[
          {tac:"obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar",
           state:"case nil\nys : List Nat\np q r : Loc\nσ : Store\nh h₁ h₂ : Heap\nleft✝ : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhys : lseg ys q r σ h₂\nhpq : fact (fun x => p = q) σ h₁\nhe : emp σ h₁\n⊢ lseg ([] ++ ys) p r σ h",
           h:"Six names for the star, with the fifth split in two, so seven bindings from one line. The discarded disjointness becomes an inaccessible <code>left✝</code>. The goal has not moved: everything so far is in the context."},
          {tac:'have hpq\' : p = q := hpq; subst hpq\'; subst he',
           state:"case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₂ : Heap\nhys : lseg ys p r σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhpq : fact (fun x => p = p) σ Heap.empty\n⊢ lseg ([] ++ ys) p r σ h",
           h:"Three tactics, shown together because they have one effect between them: <code>q</code> is gone, replaced by <code>p</code>, and <code>h₁</code> is gone, replaced by <code>Heap.empty</code>. The second segment now reads <code>lseg ys p r</code>, which is the goal up to the heap."},
          {tac:'rw [hu, union_empty_left]',
           state:"case nil\nys : List Nat\np r : Loc\nσ : Store\nh h₂ : Heap\nhys : lseg ys p r σ h₂\nleft✝ : Heap.empty.disjoint h₂\nhu : h = Heap.empty.union h₂\nhpq : fact (fun x => p = p) σ Heap.empty\n⊢ lseg ([] ++ ys) p r σ h₂",
           h:"The heap in the goal becomes <code>h₂</code> and the context does not move. What remains is <code>lseg ([] ++ ys) p r σ h₂</code> against <code>hys : lseg ys p r σ h₂</code>, and <code>[] ++ ys</code> reduces to <code>ys</code> because the append is defined by recursion on its <i>first</i> argument and that argument is a literal constructor. So <code>exact hys</code> closes it, with no rewriting of the list."}
        ],
        done:'No goals.'},
       {t:'detail', title:'What the induction hypothesis looks like if you introduce too much', tag:'aside', open:false, blocks:[
         {t:'p', h:"Write <code>induction xs</code> with <code>ys</code>, <code>p</code>, <code>q</code> and <code>r</code> already introduced, and every algebraic line goes through unchanged until the last one, where the goal is"},
         {t:'state', cap:'The state at the last line, with the hypothesis fixed at the address the proof started from.',
          src:"case cons\nys : List Nat\np q r : Loc\nx : Nat\nxs : List Nat\nih : lseg xs p q ∗ lseg ys q r ⊢ lseg (xs ++ ys) p r\nn : Nat\n⊢ node p x n ∗ lseg xs n q ∗ lseg ys q r ⊢ node p x n ∗ lseg (xs.append ys) n r"},
         {t:'p', h:"Read the two: <code>ih</code> starts at <code>p</code> and the goal starts at <code>n</code>. There is nothing wrong with the tactic and nothing wrong with the four lemmas; the statement being proved was too weak, and it was too weak from the moment <code>p</code> was introduced. Unit 20 made this the point of an entire unit and its <code>generalizing</code> keyword is the other repair; here the <code>∀</code> is inside the statement, so the repair is to stop introducing."}
       ]}
     ],
     pitfall:"Reaching for <code>append_nil</code> in the <code>nil</code> case. The goal there says <code>lseg ([] ++ ys) p r</code> and the hypothesis says <code>lseg ys p r</code>, which looks like a mismatch wanting a list lemma. It is not: <code>++</code> recurses on its first argument, that argument is the literal <code>[]</code>, so the application reduces without being asked and <code>exact</code> sees through it. Unit 20's <code>append_nil</code> is the theorem for <code>xs ++ []</code>, where the literal is on the <i>other</i> side and reduction is blocked — the mirror case, and the reason that theorem needed an induction at all.",
     variants:"Delete the <code>pure (fun _ => start ≠ 0)</code> conjunct from the definition altogether and this theorem gets <i>easier</i>: the inductive step drops to four lines, because with no leading conjunct there is nothing to strip off before the node and one <code>star_assoc_left</code> is enough. Compiled. So <code>lseg_append</code> alone does not justify the clause; the next exercise is what does. · Change the conjunct to <code>start ≠ finish</code> and the theorem becomes false; that is the subject of the section below. · Swap the conclusion to <code>lseg (ys ++ xs) p r</code> and it is false at the very first cell. Take <code>xs = [7]</code> and <code>ys = [8]</code>: the premise puts <code>7</code> at address <code>p</code>, and <code>lseg [8, 7] p r</code> claims <code>8</code> is there. An appended list holds its values in the order the chain visits them, and the chain starts where the premise's <i>left</i> conjunct starts. · Replace the <code>∗</code> of the statement by <code>aAnd</code>, leaving <code>lseg</code> itself alone, and it is false at one point: the two conjuncts are handed the same heap instead of two disjoint ones. Witness — <code>xs = ys = [7]</code>, <code>p = q = r = 1</code>, heap <code>{1 ↦ 7, 2 ↦ 1}</code>. The two conjuncts are then literally the same assertion at the same heap, so the <code>aAnd</code> holds; the conclusion <code>lseg [7, 7] 1 1</code> needs four cells and there are two. Both halves compiled: the premise as a twelve-slot bracket, and the refutation of the conclusion by reading the head node's next field out of the union — it can only be <code>1</code> — and then finding that the second node needs the cell at address <code>1</code>, which the head node already owns, so the two halves of the conclusion's <code>∗</code> are not disjoint."
    },

    /* ============================================== what it is for ==== */

    {t:'p', h:"Here is what that theorem buys, in one instance. A traversal that has walked <code>visited</code> and is standing at <code>cur</code>, with the next node's cells in hand, advances by moving that node from the front to the back. The premise below is the state before the step and the conclusion is the state after it, and the proof is <code>lseg_append</code> applied at a one-element list."},

    {t:'code', tag:'illustration', cap:'One node becomes a one-element segment, and then the append theorem does the rest. The second declaration is the invariant-maintenance step of every list traversal, and its proof is a single term.',
     src:"theorem lsegOne (x : Nat) (q n : Loc) :\n    pure (fun _ => q ≠ 0) ∗ node q x n ⊢ lseg [x] q n := by\n  intro σ h ⟨h₁, h₂, hd, hu, hp, hnode⟩\n  exact ⟨n, h₁, h₂, hd, hu, hp,\n         h₂, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hnode, ⟨rfl, rfl⟩⟩\n\nexample (visited : List Nat) (x : Nat) (p cur n : Loc) :\n    lseg visited p cur ∗ (pure (fun _ => cur ≠ 0) ∗ node cur x n) ⊢\n      lseg (visited ++ [x]) p n :=\n  entails_trans (star_mono_right _ (lsegOne x cur n)) (lseg_append visited [x] p cur n)"},

    {t:'p', h:"The traversal's other half is the list still in front of it, and that is a <code>listRep</code> rather than a segment. So the loop finishes by joining a segment to a complete list, which is a second theorem — with, as it turns out, the same proof."},

    {t:'ex',
     id:'m10-5',
     name:'lseg_listRep',
     why:"This is the lemma that closes a traversal: when the walk reaches the end, what you are holding is a segment covering everything and a complete list covering nothing, and this theorem turns the pair back into the complete list you were handed. Its second value is diagnostic. It is the same proof as <code>lseg_append</code> with a different assertion on the right, and that it <i>is</i> the same proof is evidence that <code>lseg</code> and <code>listRep</code> were defined compatibly — a definition that only worked with itself would not do this.",
     setup:"Compare the two statements before you start: the second conjunct and the conclusion have changed from <code>lseg _ _ r</code> to <code>listRep _</code>, and the third address has gone. Nothing else has. The <code>nil</code> branch is Unit 32's <code>listRep</code> standing where the second <code>lseg</code> stood; the <code>cons</code> branch is the one above with the line that does nothing left out.",
     goal:"theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),\n    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p := by",
     hints:[
       "In the <code>nil</code> case the premise is <code>lseg [] p q ∗ listRep ys q</code>: the heap splits, the left half is empty and says <code>p = q</code>, the right half is a complete list starting at <code>q</code>. The goal is a complete list starting at <code>p</code> at the whole heap. In the <code>cons</code> case the premise begins with the <code>cons</code> clause of <code>lseg</code> and the goal is the <code>cons</code> clause of <code>listRep</code>, and the two clauses have the same shape: the same non-nullness conjunct, the same node, and then a recursive call — which is the only conjunct where they differ.",
       "Induct on the first list, again, and for the same reason: the hypothesis is used at the address the head node points to. The empty case is the same bookkeeping as before. The non-empty case peels one node off the segment and hands it to the list.",
       "The <code>nil</code> branch: the previous exercise's <code>nil</code> branch with <code>listRep</code> for the second <code>lseg</code>. The <code>cons</code> branch: <code>star_exists_left</code>, <code>aExists_mono</code>, <code>star_assoc_left</code>, <code>star_mono_right</code>, <code>star_assoc_left</code>, and the hypothesis under a second <code>star_mono_right</code>.",
       "Open with <code>intro xs</code>, then <code>induction xs with</code>. The <code>cons</code> branch starts <code>intro ys p q</code> — three variables, not four — and its first tactic is <code>refine entails_trans (star_exists_left _ _) ?_</code>, which leaves <code>⊢ (aExists fun x_1 =&gt; ((_root_.pure fun x =&gt; p ≠ 0) ∗ node p x x_1 ∗ lseg xs x_1 q) ∗ listRep ys q) ⊢ listRep (x :: xs ++ ys) p</code>."
     ],
     sol:"theorem lseg_listRep : ∀ (xs ys : List Nat) (p q : Loc),\n    lseg xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq' : p = q := hpq\n      subst hpq'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q)",
     solNote:"If you wrote this by copying the previous proof and deleting one variable throughout, that is the correct reaction to it and the reason the exercise is here.",
     expl:"Both clauses of <code>listRep</code> are the corresponding clauses of <code>lseg</code> with <code>finish</code> instantiated: the <code>nil</code> clause with <code>finish := 0</code>, and the <code>cons</code> clause with the same non-nullness conjunct and the same node in front of the recursive call. So every step of the previous proof matches a step of this one. The <code>nil</code> case cuts an empty heap off the front and hands back the list; the <code>cons</code> case strips the shared <code>pure</code> conjunct, strips the shared node, and applies the hypothesis to what is left.",
     walk:[
       {tac:'intro xs',
        h:"One variable, for the same reason as before: the hypothesis will be needed at the next node's address, so <code>p</code> has to stay inside the <code>∀</code>."},
       {tac:'induction xs with',
        h:"Two branches on the two constructors of <code>List</code>. In each the goal is still <code>∀ (ys : List Nat) (p q : Loc), …</code> — three binders now, not four, because the conclusion is a complete list and has no far endpoint."},
       {tac:'      intro ys p q σ h hstar',
        h:"The <code>nil</code> branch, opened down to the model: three quantified variables, then the store, the heap and the premise. As in the previous proof, this branch is the only one that will name a heap."},
       {tac:"      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar",
        h:"Splits the star into its six slots with the fifth split again, discarding disjointness. Character for character the previous proof's line: the shape of a <code>∗</code> premise does not depend on what its right conjunct asserts, so <code>hys</code> comes out as <code>listRep ys q σ h₂</code> with no change to the pattern."},
       {tac:'      have hpq\' : p = q := hpq',
        h:"Restates <code>hpq : fact (fun x => p = q) σ h₁</code> at its reduced type <code>p = q</code>, which is the form <code>subst</code> matches on."},
       {tac:'      subst hpq\'',
        h:"Replaces <code>q</code> by <code>p</code> throughout. The premise's right half becomes <code>listRep ys p σ h₂</code> — the goal, up to which heap it is asserted at."},
       {tac:'      subst he',
        h:"Spends the empty half of the <code>pure</code>: <code>h₁</code> becomes <code>Heap.empty</code>, and the union equation reads <code>h = Heap.empty.union h₂</code>."},
       {tac:'      rw [hu, union_empty_left]',
        h:"Rewrites the goal's heap to the union and then collapses the union, so the goal is now asserted at <code>h₂</code> — the half the complete list actually occupies."},
       {tac:'      exact hys',
        h:"Closes it. <code>hys : listRep ys p σ h₂</code> against a goal reading <code>listRep ([] ++ ys) p σ h₂</code>, and <code>[] ++ ys</code> reduces without being asked."},
       {tac:'      intro ys p q',
        h:"The <code>cons</code> branch. Three variables and no more: the store and the heap stay inside the entailment for the rest of the proof."},
       {tac:'      refine entails_trans (star_exists_left _ _) ?_',
        h:"Unfolds the premise's left conjunct and lifts the quantifier out of the star, exactly as above. The goal's right-hand side is a <code>listRep</code>, and nothing so far has looked at it."},
       {tac:'      refine aExists_mono (fun n => ?_)',
        h:"Under the binder. The goal becomes an entailment between the two <code>cons</code> bodies at an arbitrary <code>n</code>, and this is where the alignment of the two definitions becomes visible: both sides start with <code>pure (fun _ => p ≠ 0)</code> and both continue with <code>node p x n</code>."},
       {tac:'      refine entails_trans (star_assoc_left _ _ _) ?_',
        h:"Re-brackets the premise so the non-nullness conjunct — which the <code>listRep</code> side already carries at its head — heads the premise too."},
       {tac:'      refine star_mono_right _ ?_',
        h:"Strips that conjunct, which is literally the same term on both sides. This is the step that fails under the wrong definition, and the section below is about what it looks like when it does."},
       {tac:'      refine entails_trans (star_assoc_left _ _ _) ?_',
        h:"Re-brackets again to bring the node <code>node p x n</code>, shared by both sides, to the front of the premise."},
       {tac:'      exact star_mono_right _ (ih ys n q)',
        h:"Strips the node, leaving <code>lseg xs n q ∗ listRep ys q ⊢ listRep (xs ++ ys) n</code> — the hypothesis at <code>ys</code>, <code>n</code>, <code>q</code>. Three arguments where the previous proof passed four, and that is the only difference between the two closing lines."}
     ],
     deep:[
       {t:'trace', title:'The cons branch, goal lines only — the context is the worked example\'s, with r gone and the second and third lseg in ih replaced by listRep, plus the n that aExists_mono adds',
        start:"⊢ lseg (x :: xs) p q ∗ listRep ys q ⊢ listRep (x :: xs ++ ys) p",
        steps:[
          {tac:'refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)',
           state:"⊢ ((_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢\n    (_root_.pure fun x => p ≠ 0) ∗ node p x n ∗ listRep (xs.append ys) n",
           h:"Two lines together, since neither is new. The two sides now agree on their first two conjuncts and differ only in the last, which is what makes the rest mechanical. Set this beside the corresponding state in the worked example and exactly two things have changed: <code>lseg ys q r</code> has become <code>listRep ys q</code>, and <code>lseg (xs.append ys) n r</code> has become <code>listRep (xs.append ys) n</code>. Everything to the left of them is character for character the same."},
          {tac:'refine entails_trans (star_assoc_left _ _ _) ?_\n      refine star_mono_right _ ?_',
           state:"⊢ (node p x n ∗ lseg xs n q) ∗ listRep ys q ⊢ node p x n ∗ listRep (xs.append ys) n",
           h:"The shared <code>pure</code> conjunct has gone. Nothing proved <code>p ≠ 0</code>; it was the same claim on both sides and monotonicity dropped it. That is the whole reason the definition's non-nullness clause has to be a claim about <code>start</code> and not about the pair of endpoints."},
          {tac:'refine entails_trans (star_assoc_left _ _ _) ?_',
           state:"⊢ node p x n ∗ lseg xs n q ∗ listRep ys q ⊢ node p x n ∗ listRep (xs.append ys) n",
           h:"Re-bracketed for the last time. One <code>star_mono_right</code> and the induction hypothesis finish it."}
        ],
        done:'No goals.'},
       {t:'p', h:"There is a third theorem in the neighbourhood, and it is the one that says a segment whose <code>finish</code> is null <i>is</i> a complete list. It needs neither <code>lseg_append</code> nor a heap, and its inductive step is one line, because the <code>nil</code> clauses coincide when <code>finish</code> is <code>0</code> and the <code>cons</code> clauses coincide always. The converse is the same proof with the two sides exchanged, so the entailment is really an equivalence — which is the strongest form the alignment of the two definitions can take."},
       {t:'code', tag:'illustration', cap:'Compiled, both directions. The <code>nil</code> case is <code>entails_refl</code> because <code>lseg [] p 0</code> and <code>listRep [] p</code> are the same term; the <code>cons</code> case strips two shared conjuncts and recurses. The second proof is the first with <code>lseg</code> and <code>listRep</code> swapped in the statement and nothing else touched.',
        src:"example : ∀ (xs : List Nat) (p : Loc), lseg xs p 0 ⊢ listRep xs p := by\n  intro xs\n  induction xs with\n  | nil => intro p; exact entails_refl _\n  | cons x xs ih =>\n      intro p\n      refine aExists_mono (fun n => ?_)\n      exact star_mono_right _ (star_mono_right _ (ih n))\n\nexample : ∀ (xs : List Nat) (p : Loc), listRep xs p ⊢ lseg xs p 0 := by\n  intro xs\n  induction xs with\n  | nil => intro p; exact entails_refl _\n  | cons x xs ih =>\n      intro p\n      refine aExists_mono (fun n => ?_)\n      exact star_mono_right _ (star_mono_right _ (ih n))"}
     ],
     pitfall:"Introducing four variables in the <code>cons</code> branch out of habit, because the previous proof did. There is no <code>r</code> here, so <code>intro ys p q r</code> takes the <i>store</i> as its fourth argument, and the first <code>refine</code> then reports an expected type with <code>r</code> standing where a store belongs: <code>Type mismatch: entails_trans (star_exists_left ?m.109 ?m.110) ?m.111 has type aExists ?m.109 ∗ ?m.110 ⊢ ?m.107 but is expected to have type ∀ (h : Heap), (lseg (x :: xs) p q ∗ listRep ys q) r h → listRep (x :: xs ++ ys) p r h</code>. The tell is the <code>∀ (h : Heap)</code>: the entailment has already been half opened, which only happens if you introduced past it. Count the binders in the statement before opening the branch.",
     variants:"State it with the two conjuncts the other way round — <code>listRep ys q ∗ lseg xs p q</code> — and it is still true and is one <code>star_comm</code> away, but the proof of the <code>cons</code> case has to commute before it can pull the existential out, because <code>star_exists_left</code> only hoists from the left. · Replace <code>lseg</code> by the variant whose <code>cons</code> clause says <code>start ≠ finish</code> and the <code>star_mono_right</code> step dies: <code>Type mismatch: star_mono_right ?m.123 ?m.126 has type ?m.123 ∗ ?m.124 ⊢ ?m.123 ∗ ?m.125 but is expected to have type (_root_.pure fun x =&gt; p ≠ q) ∗ (node p x n ∗ lsegNe xs n q) ∗ listRep ys q ⊢ (_root_.pure fun x =&gt; p ≠ 0) ∗ node p x n ∗ listRep (xs.append ys) n</code>. The single metavariable <code>?m.123</code> stands at the head of both halves of the lemma's type and would have to be <code>p ≠ q</code> and <code>p ≠ 0</code> at once; the two leading conjuncts are no longer the same term, so there is nothing to drop. · Delete the non-nullness conjunct from <code>lseg</code> entirely and this theorem becomes <i>false</i>: a bare segment may begin at address <code>0</code>, and a complete list may not. Both refutations are below."
    },

    /* =================================== the clause that had to be chosen ==== */

    {t:'sec', s:'The clause that was a choice'},

    {t:'p', h:"Go back to the line that was left unjustified. The <code>cons</code> clause of <code>lseg</code> asserts <code>start ≠ 0</code>, and the obvious reading of a segment from <code>start</code> to <code>finish</code> suggests something else entirely: a non-empty segment surely runs from one address to a <i>different</i> address, so the clause ought to be <code>start ≠ finish</code>. It looks more informative, it is exactly what the <code>nil</code> clause negates, and it is wrong."},

    {t:'code', tag:'illustration', cap:'The same definition with one symbol changed. Everything else — the existential, the node, the recursive call — is identical.',
     src:"def lsegNe : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next =>\n        pure (fun _ => start ≠ finish) ∗ node start x next ∗ lsegNe xs next finish"},

    {t:'p', h:"Run the same six lines at it. They survive <code>star_exists_left</code> and <code>aExists_mono</code> and then stop, and the goal at the point where they stop is the whole diagnosis."},

    {t:'state', cap:'After <code>aExists_mono</code>, in the <code>cons</code> branch, with the wrong definition. The seven context lines above the goal are the worked example\'s with <code>lseg</code> read as <code>lsegNe</code>, plus the <code>n</code> that <code>aExists_mono</code> adds, and are omitted.',
     src:"⊢ ((_root_.pure fun x => p ≠ q) ∗ node p x n ∗ lsegNe xs n q) ∗ lsegNe ys q r ⊢\n    (_root_.pure fun x => p ≠ r) ∗ node p x n ∗ lsegNe (xs.append ys) n r"},

    {t:'p', h:"You hold <code>p ≠ q</code> and the goal wants <code>p ≠ r</code>. The two leading conjuncts are no longer the same term, so <code>star_mono_right</code> — which drops a conjunct precisely because it is shared — cannot be applied, and Lean says so by setting its own shape against the goal: <code>Type mismatch: star_mono_right ?m.127 ?m.130 has type ?m.127 ∗ ?m.128 ⊢ ?m.127 ∗ ?m.129 but is expected to have type (_root_.pure fun x =&gt; p ≠ q) ∗ (node p x n ∗ lsegNe xs n q) ∗ lsegNe ys q r ⊢ (_root_.pure fun x =&gt; p ≠ r) ∗ node p x n ∗ lsegNe (xs.append ys) n r</code>. The same metavariable <code>?m.127</code> stands in both halves of the lemma's type and there is no assignment that makes <code>p ≠ q</code> and <code>p ≠ r</code> both equal to it. Nothing else in the algebra will bridge the gap either, and the reason is not a missing lemma. <code>q</code> is the address where the two segments meet and <code>r</code> is where the second one ends; the premise says nothing relating them, because the whole point of the half-open convention is that neither segment owns the address at its far end."},

    {t:'note', kind:'warn', title:'What the failed proof was telling you',
     h:"A condition written into a recursive assertion has to be a claim the <i>recursion preserves</i>. Under <code>start ≠ 0</code> every node in a chain makes the same claim about itself, so joining two chains joins two collections of identical claims and monotonicity discharges the lot. Under <code>start ≠ finish</code> each node makes a claim about a moving target, and joining two chains changes the target — so the claims held do not add up to the claims wanted. The condition belongs to the <i>node</i>, not to the <i>segment</i>, and the theorem is what says so."},

    {t:'p', h:"It is not only this proof that fails. The entailment is false, and the counterexample is the structure the wrong condition was supposed to exclude and does not: a lasso. Take a two-node cycle, <code>1 → 3 → 1</code>. The first node on its own is a <code>lsegNe</code> segment from <code>1</code> to <code>3</code>, since <code>1 ≠ 3</code>. The second is a segment from <code>3</code> to <code>1</code>, since <code>3 ≠ 1</code>. They own four different cells, so their <code>∗</code> is satisfied. Joining them would be a segment from <code>1</code> to <code>1</code>, which asserts <code>1 ≠ 1</code>."},

    {t:'detail', title:'The refutation, in full', tag:'aside', open:false,
     blocks:[
       {t:'p', h:"A refutation costs a witness, and here the witness is a store nobody reads and a four-cell heap. The two nodes are built as unions of singletons in the style of Unit 32; the disjointness of the two nodes needs both bridge lemmas from Unit 10, since each side is itself a union."},
       {t:'code', tag:'illustration', cap:'Compiled. The last two lines are the payoff: opening the joined segment yields its non-nullness conjunct, which here reads <code>1 ≠ 1</code>, and applying it to <code>rfl</code> closes <code>False</code>.',
        src:"example : ¬ (∀ (xs ys : List Nat) (p q r : Loc),\n    lsegNe xs p q ∗ lsegNe ys q r ⊢ lsegNe (xs ++ ys) p r) := by\n  intro hbad\n  have hn₁ : node 1 7 3 (fun _ => 0) (Heap.union (Heap.singleton 1 7) (Heap.singleton 2 3)) :=\n    ⟨Heap.singleton 1 7, Heap.singleton 2 3, singleton_disjoint 7 3 (by simp), rfl, rfl, rfl⟩\n  have hn₂ : node 3 8 1 (fun _ => 0) (Heap.union (Heap.singleton 3 8) (Heap.singleton 4 1)) :=\n    ⟨Heap.singleton 3 8, Heap.singleton 4 1, singleton_disjoint 8 1 (by simp), rfl, rfl, rfl⟩\n  have hd : Heap.disjoint (Heap.union (Heap.singleton 1 7) (Heap.singleton 2 3))\n      (Heap.union (Heap.singleton 3 8) (Heap.singleton 4 1)) :=\n    disjoint_union_left.mpr\n      ⟨disjoint_union_right.mpr ⟨singleton_disjoint 7 8 (by simp), singleton_disjoint 7 1 (by simp)⟩,\n       disjoint_union_right.mpr ⟨singleton_disjoint 3 8 (by simp), singleton_disjoint 3 1 (by simp)⟩⟩\n  have hs₁ : lsegNe [7] 1 3 (fun _ => 0) (Heap.union (Heap.singleton 1 7) (Heap.singleton 2 3)) :=\n    ⟨3, Heap.empty, _, disjoint_empty_left _, (union_empty_left _).symm, ⟨by simp [fact], rfl⟩,\n     _, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₁, ⟨rfl, rfl⟩⟩\n  have hs₂ : lsegNe [8] 3 1 (fun _ => 0) (Heap.union (Heap.singleton 3 8) (Heap.singleton 4 1)) :=\n    ⟨1, Heap.empty, _, disjoint_empty_left _, (union_empty_left _).symm, ⟨by simp [fact], rfl⟩,\n     _, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn₂, ⟨rfl, rfl⟩⟩\n  obtain ⟨n, _, _, _, _, ⟨hne, _⟩, _⟩ :=\n    hbad [7] [8] 1 3 1 (fun _ => 0) _ ⟨_, _, hd, rfl, hs₁, hs₂⟩\n  exact hne rfl"},
       {t:'p', h:"The correct definition does not refuse this heap, and does not need to. It demands <code>1 ≠ 0</code> and <code>3 ≠ 0</code>, which both hold, so the two pieces are segments under it too, and <code>lseg [7, 8] 1 1</code> — a genuine cyclic segment — demands only <code>1 ≠ 0</code>, which also holds. So the joined assertion is satisfiable and nothing false has been concluded. That is the difference: <code>start ≠ 0</code> makes a claim the join can keep, and <code>start ≠ finish</code> makes one it cannot. Excluding the lasso is <code>listRep</code>'s job, not <code>lseg</code>'s, and Unit 32 explained how it does it — the chain has to reach <code>0</code>, and every node on it is somewhere else."}
     ]},

    {t:'p', h:"That settles the second candidate and leaves the third, which is the one <code>lseg_append</code> alone would have chosen: leave the slot empty. A segment is then a chain of nodes ending wherever it was told to end, and nothing else — and <code>lseg_append</code> is <i>easier</i> for it, since with no leading conjunct there is nothing to strip off before the node. So the first theorem does not justify the clause. The second one does. A conditionless segment may begin at address <code>0</code> and a <code>listRep</code> may not, so a bare segment cannot be closed into a list: <code>lseg_listRep</code> becomes false, refuted by a single node sitting at address <code>0</code>."},

    {t:'p', h:"Three candidates, then, and two theorems between them. <code>start ≠ finish</code> loses the first theorem; nothing at all loses the second; <code>start ≠ 0</code> keeps both, because it is a claim each node makes about itself, which the recursion carries unchanged and which <code>listRep</code> makes in the same words."},

    {t:'detail', title:'The conditionless variant, and both compiled proofs', tag:'aside', open:false,
     blocks:[
       {t:'code', tag:'illustration', cap:'The conditionless variant, and the append theorem for it. The inductive step is four lines rather than six — with no leading conjunct there is nothing to strip before the node, so one re-bracketing does what two did.',
        src:"def lsegBare : List Nat → Loc → Loc → Assertion\n  | [],      start, finish => pure (fun _ => start = finish)\n  | x :: xs, start, finish =>\n      aExists fun next => node start x next ∗ lsegBare xs next finish\n\ntheorem lsegBare_append : ∀ (xs ys : List Nat) (p q r : Loc),\n    lsegBare xs p q ∗ lsegBare ys q r ⊢ lsegBare (xs ++ ys) p r := by\n  intro xs\n  induction xs with\n  | nil =>\n      intro ys p q r σ h hstar\n      obtain ⟨h₁, h₂, _, hu, ⟨hpq, he⟩, hys⟩ := hstar\n      have hpq' : p = q := hpq\n      subst hpq'\n      subst he\n      rw [hu, union_empty_left]\n      exact hys\n  | cons x xs ih =>\n      intro ys p q r\n      refine entails_trans (star_exists_left _ _) ?_\n      refine aExists_mono (fun n => ?_)\n      refine entails_trans (star_assoc_left _ _ _) ?_\n      exact star_mono_right _ (ih ys n q r)"},
       {t:'p', h:"The refutation of the second theorem costs one node rather than the lasso's four, because a single cell at the forbidden address is already a counterexample."},
       {t:'code', tag:'illustration', cap:'Compiled. Two cells at addresses 0 and 1 make a bare segment from 0 to 0 holding <code>[7]</code>, and <code>listRep [] 0</code> is satisfied by the empty heap, so the premise holds. The conclusion would be <code>listRep [7] 0</code>, which asserts <code>0 ≠ 0</code>.',
        src:"example : ¬ (∀ (xs ys : List Nat) (p q : Loc),\n    lsegBare xs p q ∗ listRep ys q ⊢ listRep (xs ++ ys) p) := by\n  intro hbad\n  have hn : node 0 7 0 (fun _ => 0) (Heap.union (Heap.singleton 0 7) (Heap.singleton 1 0)) :=\n    ⟨Heap.singleton 0 7, Heap.singleton 1 0, singleton_disjoint 7 0 (by simp), rfl, rfl, rfl⟩\n  have hseg : lsegBare [7] 0 0 (fun _ => 0)\n      (Heap.union (Heap.singleton 0 7) (Heap.singleton 1 0)) :=\n    ⟨0, _, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hn, ⟨rfl, rfl⟩⟩\n  obtain ⟨n, _, _, _, _, ⟨hne, _⟩, _⟩ :=\n    hbad [7] [] 0 0 (fun _ => 0) _\n      ⟨_, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, hseg, ⟨rfl, rfl⟩⟩\n  exact hne rfl"}
     ]},

    /* ====================================================== the null end ==== */

    {t:'sec', s:'Reaching the end'},

    {t:'p', h:"One thing is still missing before a traversal could be verified, and it is what the loop's test is for. A walk stops when <code>cur</code> is <code>0</code>. At that moment the program holds <code>listRep remaining cur</code> for some list of values it has not seen, and it needs to conclude that there is nothing left. That conclusion is a theorem, and stating it is the exercise: the statement is more interesting than the proof, and the strongest true version of it says more than you might first write."},

    {t:'ex',
     id:'x67',
     name:'listRep_null',
     why:"The termination condition of every list algorithm, as a fact about assertions rather than about programs. It is also the only proof on this page whose two cases are not two halves of one argument: one is closed by what the <code>nil</code> clause says, the other by the fact that nothing whatever satisfies the <code>cons</code> clause here. And there is a real choice in the statement — how much you are entitled to conclude — which is why this is a design exercise rather than a drill.",
     setup:"State and prove it yourself. In English: a list at the null pointer is the empty list. Decide two things before writing Lean. First, which relation the statement is — you are claiming something about every state satisfying <code>listRep xs 0</code>, so it is an entailment. Second, what goes on the right of the <code>⊢</code>: the conclusion is a proposition with no memory in it, and Unit 17 gave you two ways to embed such a thing, one of which also claims the heap is empty. Both give true theorems. One is strictly stronger, and it is true here.",
     goal:"-- Delete the line below and write your own `theorem listRep_null …`.\n-- Any correct statement of the fact will be accepted.\nexample : True := by",
     hints:[
       "Write the claim with no symbols first: <i>if a heap satisfies <code>listRep xs 0</code>, then <code>xs</code> is the empty list.</i> That is a statement about every state, which is what <code>⊢</code> quantifies over. The left-hand side is <code>listRep xs 0</code> with <code>xs</code> a variable of the theorem. The question is what stands on the right.",
       "The argument has two cases and they are settled differently. If <code>xs</code> is <code>[]</code> the conclusion is immediate — but notice what else the <code>nil</code> clause of <code>listRep</code> tells you about the heap, because that is what decides how strong your statement can be. If <code>xs</code> is a <code>cons</code>, the clause asserts that the head address is not null, and the head address here <i>is</i> null, so no state satisfies the premise at all.",
       "The statement is <code>theorem listRep_null (xs : List Nat) : listRep xs 0 ⊢ pure (fun _ => xs = [])</code>. <code>pure</code> rather than <code>fact</code>, because a list at null owns nothing and you may as well say so. Prove it by <code>cases xs with</code>, not by induction: the two cases are answered outright, and neither needs the theorem for a shorter list.",
       "The <code>nil</code> branch is <code>intro σ h hp; exact ⟨rfl, hp.2⟩</code> — the first component is the list equation and the second is the emptiness of the heap, which the premise already carries because <code>listRep [] 0</code> is itself a <code>pure</code>. The <code>cons</code> branch opens the premise with the seven-slot pattern of Unit 32 and finds a proof of <code>0 ≠ 0</code> inside it."
     ],
     sol:"theorem listRep_null (xs : List Nat) : listRep xs 0 ⊢ pure (fun _ => xs = []) := by\n  cases xs with\n  | nil => intro σ h hp; exact ⟨rfl, hp.2⟩\n  | cons x xs =>\n      intro σ h hrep\n      obtain ⟨next, h₁, h₂, _, _, ⟨hne, _⟩, _⟩ := hrep\n      exact absurd rfl hne",
     solNote:"If you stated the conclusion with <code>fact</code> instead of <code>pure</code>, that theorem is true, the <code>nil</code> branch shortens to <code>exact rfl</code>, and the editor accepts it — you have proved something slightly weaker, and the <code>variants</code> below say what you gave up. A different correct statement gets a green tick; that is what a design exercise is.",
     expl:"The two branches are not two halves of one argument, they are two different arguments. In the <code>nil</code> branch the premise is <code>pure (fun _ => 0 = 0)</code> and the conclusion is <code>pure (fun _ => [] = [])</code>; both propositions are <code>rfl</code>, and the emptiness claim travels from the premise to the conclusion because it is the same claim about the same heap. In the <code>cons</code> branch the premise cannot hold at all: the <code>cons</code> clause asserts that the starting address is not null, and the starting address is the literal <code>0</code>, so the hypothesis contains a proof of <code>0 ≠ 0</code> and the goal is irrelevant.",
     walk:[
       {tac:'cases xs with',
        h:"A case split on the data, not an induction — no branch needs the statement for a shorter list, so there is nothing for an induction hypothesis to do. The two branches are the two constructors of <code>List</code>."},
       {tac:'  | nil => intro σ h hp; exact ⟨rfl, hp.2⟩',
        h:"Premise and goal are both <code>pure</code>s here, and a <code>pure</code> is a conjunction, so the answer is a pair. The left component is <code>[] = []</code>, closed by <code>rfl</code>. The right component is <code>emp σ h</code>, and <code>hp.2</code> is exactly that, taken from the premise: <code>listRep [] 0</code> is <code>pure (fun _ => 0 = 0)</code>, whose second component says the heap is empty."},
       {tac:'      intro σ h hrep',
        h:"The <code>cons</code> branch, opened. The premise is <code>listRep (x :: xs) 0 σ h</code>, which the next line will take apart."},
       {tac:"      obtain ⟨next, h₁, h₂, _, _, ⟨hne, _⟩, _⟩ := hrep",
        h:"Seven slots: the existential witness, the two heaps, disjointness, the union equation, the <code>pure</code> conjunct split in two, and the rest. Four are discarded. What is kept is <code>hne</code>, the non-nullness claim — which, because the address here is the literal <code>0</code>, has type <code>fact (fun x => 0 ≠ 0) σ h₁</code>."},
       {tac:'      exact absurd rfl hne',
        h:"<code>hne</code> reduces to <code>0 ≠ 0</code>, which is <code>0 = 0 → False</code>, and <code>rfl</code> is a proof of the antecedent. Unit 02's <code>absurd</code> takes the two and produces anything, including the goal. Nothing about the goal was ever examined."}
     ],
     deep:[
       {t:'trace', title:'The cons branch, where the premise dies',
        start:"case cons\nx : Nat\nxs : List Nat\nσ : Store\nh : Heap\nhrep : listRep (x :: xs) 0 σ h\n⊢ _root_.pure (fun x_1 => x :: xs = []) σ h",
        steps:[
          {tac:"obtain ⟨next, h₁, h₂, _, _, ⟨hne, _⟩, _⟩ := hrep",
           state:"case cons\nx : Nat\nxs : List Nat\nσ : Store\nh : Heap\nnext : Nat\nh₁ h₂ : Heap\nleft✝¹ : h₁.disjoint h₂\nleft✝ : h = h₁.union h₂\nright✝¹ : (node 0 x next ∗ listRep xs next) σ h₂\nhne : fact (fun x => 0 ≠ 0) σ h₁\nright✝ : emp σ h₁\n⊢ _root_.pure (fun x_1 => x :: xs = []) σ h",
           h:"Read <code>hne</code>: the definition's <code>p ≠ 0</code> with <code>p</code> instantiated to the literal <code>0</code>. The goal is still the one you cannot prove — <code>x :: xs = []</code> is false — and it does not matter, because the context is now contradictory."},
          {tac:'exact absurd rfl hne',
           state:"No goals.",
           h:"A false hypothesis closes any goal. This is the shape every &ldquo;the premise is unsatisfiable&rdquo; proof takes, and Unit 12 made the general case a one-line theorem: <code>aFalse</code> entails every assertion there is. The <code>cons</code> clause at address <code>0</code> is <code>aFalse</code> wearing a disguise."}
        ],
        done:'No goals.'},
       {t:'p', h:"The <code>nil</code> branch is where the choice between <code>fact</code> and <code>pure</code> is paid for, and it costs one component. With <code>fact</code> the branch is <code>exact rfl</code>; with <code>pure</code> it is <code>exact ⟨rfl, hp.2⟩</code>, and the extra component is handed over by the premise rather than proved. Writing <code>⟨rfl, rfl⟩</code> instead does not work: <code>h</code> is a variable, not the literal <code>Heap.empty</code>, so the emptiness has to come from <code>hp</code>."}
     ],
     pitfall:"Reaching for <code>induction</code> rather than <code>cases</code>. It compiles, because an induction hypothesis you do not use costs nothing, and it obscures the argument: the theorem is not proved by descending the list, it is proved by looking at the first constructor. The tell is that the <code>cons</code> branch never mentions <code>ih</code>. Unit 20's rule applies — <code>cases</code> and <code>induction</code> are one rule with the hypothesis dropped, and dropping it is the honest choice when nothing needs it.",
     variants:"Two other correct statements, and what each buys. <b><code>listRep xs 0 ⊢ fact (fun _ => xs = [])</code></b> is true, one component shorter to prove, and strictly weaker — it says the list is empty and says nothing about the memory, so a caller who has it still cannot conclude that they own nothing. Given how it is used, that is the version you would regret. <b><code>listRep xs 0 ⊣⊢ pure (fun _ => xs = [])</code></b> is also true and is the strongest of the three: the forward half is the theorem you already have, and the converse takes the equation out of the <code>pure</code>, substitutes it, and hands back the emptiness claim — <code>intro σ h ⟨hx, he⟩</code>, <code>subst hx</code>, <code>exact ⟨rfl, he⟩</code>, compiled. It is the right statement if you want to rewrite with it inside a bigger assertion, and more than is needed if you only want to read a fact off a hypothesis. · What you cannot state is the same theorem for a segment: <code>lseg xs 0 q</code> at a non-empty <code>xs</code> is equally unsatisfiable, but at <code>xs = []</code> it says <code>0 = q</code> rather than nothing, so the conclusion has to mention <code>q</code> and stops being a fact about the list alone."
    },

    /* ==================================================== retrospective ==== */

    {t:'sec', s:'Retrospective'},

    {t:'p', h:"Three questions. The folds have the answers; try them closed first."},

    {t:'detail', title:'Why is the nil case of lseg_append the only one that touches heaps?', tag:'aside', open:false, blocks:[
      {t:'p', h:"Because it is the only case in which an assertion owning <i>nothing</i> has to be removed from the front of a heap. <code>lseg [] p q</code> is a <code>pure</code>: it contributes a proposition and an empty piece of memory. The <code>∗</code> in the premise has therefore cut the heap into an empty part and everything else, and the goal wants everything else — which is the equation <code>Heap.empty.union h₂ = h₂</code>, a fact about <code>Heap.union</code> that no lemma about <code>∗</code> states, because it is not about <code>∗</code>."},
      {t:'p', h:"Every other step relates two stars, and Unit 16 reduced that to lemma application once and for all. The general shape: heaps appear in a separation-logic proof exactly where an assertion's own definition is opened. The <code>cons</code> case never opens one; it rearranges the connectives around them."}
    ]},

    {t:'detail', title:'What would have failed first if lseg had used start ≠ finish?', tag:'aside', open:false, blocks:[
      {t:'p', h:"<code>lseg_append</code>, at the step that applies <code>star_mono_right</code> for the first time. <code>star_exists_left</code> and <code>aExists_mono</code> both succeed — they do not look at the conjuncts — and then <code>star_mono_right</code> is asked to drop a leading conjunct that is <code>p ≠ q</code> on the left and <code>p ≠ r</code> on the right. It is not a repairable failure: the entailment is false, and a two-node cycle is a heap that satisfies the premise and refutes the conclusion."},
      {t:'p', h:"<code>lseg_listRep</code> fails at the same line for the same reason, with <code>p ≠ 0</code> in the place of <code>p ≠ r</code>. Which of the two you meet first depends only on which you attempt first; what they have in common is that the failure is at the conjunct the definition invented, and not at the node, the existential or the recursion."}
    ]},

    {t:'detail', title:'Name the algebra lemmas the cons case used, in order.', tag:'aside', open:false, blocks:[
      {t:'p', h:"<code>star_exists_left</code> — hoist the quantifier out of the star. <code>aExists_mono</code> — get under it. <code>star_assoc_left</code> — re-bracket so the non-nullness conjunct is at the head of both sides. <code>star_mono_right</code> — drop it. <code>star_assoc_left</code> again, then <code>star_mono_right</code> again to drop the node. Four distinct names in six applications, glued throughout by <code>entails_trans</code>."},
      {t:'p', h:"Three of the four were proved in Units 15 and 16, before this course had a program in it, and none of them was proved with a list in mind. That is what an algebra is for: the lemmas are about <code>∗</code>, and <code>∗</code> does not know what its arguments describe."}
    ]},

    {t:'dod', h:"You can define an assertion for the part of a linked structure between two addresses, and say which cells it owns and which it deliberately does not. You can prove an entailment underneath an existential binder, and say why <code>star_exists_left</code> alone leaves you stuck. You can prove that two adjacent segments make one, by induction on the data, with the inductive step carried out entirely in the algebra — and you can say, of each of the six lines, which lemma it is and what it removed from the goal. You can prove the same theorem against a complete list and read the identity of the two proofs as evidence about the two definitions. Given a definition that looks right, you can run a proof at it, read the goal where the proof stops, diagnose which clause is wrong, and produce a heap that shows the theorem is false rather than unproved. And you can state, unaided, what a list at the null pointer is, and choose how much to claim."},

    {t:'p', h:"<code>lseg</code> describes a list with its tail removed — a structure with a hole, where the hole is described by another assertion. <i>I have given away part of my data structure, and here is how to put it back</i> is a pattern that recurs constantly, and it has a connective of its own."}

  ]
});
