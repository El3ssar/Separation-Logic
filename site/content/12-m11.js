/* M11 — The magic wand
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m11",
  "num": "M11",
  "phase": "Phase 3 · Advanced separation logic",
  "title": "The magic wand",
  "blurb": "Separating implication, and why it is the right adjoint of ∗ rather than a curiosity.",

  "orient": {
    "youWill": [
      "Write down the assertion M10 could not: what a traversal still holds after lending its current node away.",
      "Prove a wand goal with a single <code>intro</code> line that walks three definitions, and redeem a wand by handing it a disjoint heap.",
      "Prove <code>(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)</code>, then get currying, framing and monotonicity out of it without naming a heap.",
      "Break both cheaper definitions — implication in the same heap, and <code>∧</code> where <code>∗</code> should be — and name the vacuity that kills them.",
      "Derive the ramified frame rule: any small triple, plus a wand, gives a triple for whatever postcondition you want."
    ],
    "needs": [
      "The six-slot star bracket in both directions, plus <code>star_mono_left</code>, <code>star_assoc_left</code>/<code>star_assoc_right</code>, <code>star_comm</code>, <code>entails_trans</code>.",
      "<code>Heap.disjoint</code>, <code>Heap.union</code>, <code>union_comm</code>, <code>union_empty_left</code>, <code>disjoint_symm</code>.",
      "<code>node</code> and <code>listRep</code> from M10, for the section that answers M10’s question.",
      "<code>hoare_frame</code>, <code>HeapLocal</code>, <code>Preserves</code> from M8 — the closing section only."
    ],
    "payoff": "Every “I lent out part of my structure and here is how to get it back” argument is a wand: a loop invariant over a half-walked tree, an Iris continuation, a frame rule whose postcondition has already been chosen."
  },

  "blocks": [
    { "t": "h3", "s": "An assertion about a heap you do not have" },

    { "t": "p",
      "h": "You are not owed a particular heap. You are owed <i>whatever you are handed</i>, provided it is a node. So the assertion has to quantify over the incoming heap rather than name it; it has to insist that heap is separate from yours, or putting the two together means nothing; and what it claims is about the union, because the union is what you will be holding once the node comes back. Three clauses, and with the node generalised to an arbitrary <code>P</code>, they are the definition." },

    { "t": "code",
      "src": "def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')\ninfixr:54 \" -∗ \" => wand" },

    { "t": "quote",
      "h": "I hold a resource such that, <b>if you give me a separate heap satisfying <code>P</code></b>, the combination satisfies <code>Q</code>." },

    { "t": "svg",
      "src": "\n<svg viewBox=\"0 0 560 148\" role=\"img\" aria-label=\"The magic wand\">\n  <g class=\"dg\">\n    <rect x=\"14\" y=\"34\" width=\"130\" height=\"38\" rx=\"7\" class=\"dg-box\"/>\n    <text x=\"79\" y=\"58\" text-anchor=\"middle\" class=\"dg-t\">h : P −∗ Q</text>\n    <text x=\"160\" y=\"58\" class=\"dg-t\">+</text>\n    <rect x=\"184\" y=\"34\" width=\"110\" height=\"38\" rx=\"7\" class=\"dg-box a\"/>\n    <text x=\"239\" y=\"58\" text-anchor=\"middle\" class=\"dg-t\">h' : P</text>\n    <path class=\"dg-arr\" d=\"M310 53 L 356 53\"/>\n    <rect x=\"372\" y=\"34\" width=\"168\" height=\"38\" rx=\"7\" class=\"dg-box b\"/>\n    <text x=\"456\" y=\"58\" text-anchor=\"middle\" class=\"dg-t\">h ∪ h' : Q</text>\n    <text x=\"14\" y=\"104\" class=\"dg-note\">A wand is a resource-consuming promise: hand it a separate heap satisfying P</text>\n    <text x=\"14\" y=\"124\" class=\"dg-note\">and the combination satisfies Q. It is the right adjoint of ∗, not of ∧.</text>\n  </g>\n</svg>" },

    { "t": "anat",
      "src": "def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')\ninfixr:54 \" -∗ \" => wand",
      "parts": [
        { "m": "fun σ h =>",
          "h": "<code>h</code> is <b>the heap the wand itself owns</b>. A wand is not a fact about the world that happens to be indexed by a heap; it is a resource, and this is the resource it is." },
        { "m": "∀ h'",
          "h": "Every heap you might later be handed, not one particular heap. That quantifier is the difference between a promise made in advance to an unknown caller and a remark about the heap currently in front of you." },
        { "m": "Heap.disjoint h h'",
          "h": "The clause that makes <code>-∗</code> <i>separating</i>. On paper you would write “take a fresh heap and combine”; here <code>Heap.union</code> is total and left-biased, so separateness cannot be smuggled into the union and has to ride as a hypothesis <i>of the implication</i> — payable by whoever redeems the wand, not by whoever holds it." },
        { "m": "P σ h'",
          "h": "The antecedent, evaluated at the heap you <b>bring</b>. Nothing about <code>P</code> is asserted of the wand’s own heap." },
        { "m": "Q σ (Heap.union h h')",
          "h": "The conclusion, at the <b>combined</b> heap. This one choice is the whole design: <code>Q</code> gets both halves, which is exactly why redeeming a wand spends both." },
        { "m": "infixr:54",
          "h": "Below <code>∗</code> at 55, above <code>⊢</code> at 40, and right-associative like <code>→</code>." }
      ] },

    { "t": "p",
      "h": "Those three numbers settle how every statement in this chapter parses, and one of the four rows below is a theorem you did not mean to write." },

    { "t": "tbl",
      "cap": "Checked by asking Lean to print with <code>set_option pp.parens true</code>.",
      "head": ["You write", "Lean parses", "Because"],
      "rows": [
        ["<code>P ∗ Q -∗ R</code>", "<code>(P ∗ Q) -∗ R</code>", "<code>∗</code> is 55, <code>-∗</code> is 54; the tighter operator groups first."],
        ["<code>P -∗ Q -∗ R</code>", "<code>P -∗ (Q -∗ R)</code>", "<code>infixr</code> — right-associative, exactly like <code>→</code>."],
        ["<code>P ⊢ Q -∗ R</code>", "<code>P ⊢ (Q -∗ R)</code>", "<code>⊢</code> is 40, looser than both, so the adjunction needs no brackets."],
        ["<code>P -∗ Q ∗ P ⊢ Q</code>", "<code>(P -∗ (Q ∗ P)) ⊢ Q</code>", "<b>Not</b> <code>wand_elim</code>. The parentheses in <code>(P -∗ Q) ∗ P ⊢ Q</code> are load-bearing."]
      ] },

    { "t": "h3", "s": "The cheaper definition, and where it goes vacuous" },

    { "t": "p",
      "h": "There is an obvious shorter definition: implication evaluated in the heap you already have. No quantifier, no disjointness, no union, no lemma about heaps anywhere in it. It is also wrong, and wrong in a way worth watching happen." },

    { "t": "cmp",
      "left": {
        "t": "The naive version — same heap",
        "kind": "bad",
        "h": "Holds at <code>h</code> when: <i>if</i> this very heap satisfies <code>P</code>, then it satisfies <code>Q</code>. No resource enters and none is consumed.",
        "src": "def aImp (P Q : Assertion) : Assertion :=\n  fun σ h => P σ h → Q σ h"
      },
      "right": {
        "t": "The wand — a heap you have not been given yet",
        "kind": "good",
        "h": "Holds at <code>h</code> when: for <i>every</i> disjoint <code>h'</code> satisfying <code>P</code>, the union satisfies <code>Q</code>. The quantifier turns an implication into a promise; the union makes redeeming it cost something.",
        "src": "def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')"
      } },

    { "t": "p",
      "h": "Under <code>aImp</code>, modus ponens across <code>∗</code> is false. Here is the witness." },

    { "t": "code",
      "tag": "illustration",
      "cap": "Compiled against the M11 prelude. Take P = <code>0 ↦ 1</code>, Q = <code>aFalse</code>, and cut the heap as <code>Heap.empty ∪ Heap.singleton 0 1</code>.",
      "src": "def aImp (P Q : Assertion) : Assertion := fun σ h => P σ h → Q σ h\n\ntheorem aImp_elim_fails : ¬ (∀ P Q : Assertion, (aImp P Q) ∗ P ⊢ Q) := by\n  intro hcontra\n  refine hcontra (0 ↦ 1) aFalse (fun _ => 0) (Heap.singleton 0 1) ?_\n  refine ⟨Heap.empty, Heap.singleton 0 1, disjoint_empty_left _,\n          (union_empty_left _).symm, ?_, rfl⟩\n  intro hp\n  have hz : Heap.empty 0 = Heap.singleton 0 1 0 := by rw [hp]\n  rw [singleton_same] at hz\n  exact absurd hz (by simp [Heap.empty])" },

    { "t": "p",
      "h": "The mechanism is the one to remember, because the chapter’s last counterexample is the same trick. <code>aImp (0 ↦ 1) aFalse</code> is satisfied by the <i>empty</i> heap, vacuously: the empty heap does not satisfy <code>0 ↦ 1</code>, so there is nothing to discharge. The left factor of the star can therefore be empty and free, and the star as a whole says nothing. A same-heap implication is cheapest exactly where it ought to be dearest. The <code>∀ h'</code> closes the hole by making the promise answer for every possible argument, including the ones you were hoping never to be handed." },

    { "t": "detail",
      "title": "Two goal states from <code>aImp_elim_fails</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        { "t": "p",
          "h": "After <code>intro hcontra</code> and the first <code>refine</code>, four arguments have gone in — two assertions, then a store and a heap, because <code>⊢</code> unfolds to <code>∀ σ h</code>. The application already reduces to <code>False</code>, so only the hypothesis is left as a hole:" },
        { "t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\n⊢ (aImp (0 ↦ 1) aFalse ∗ 0 ↦ 1) (fun x => 0) (Heap.singleton 0 1)" },
        { "t": "p",
          "h": "One <code>refine</code> and one <code>intro</code> later, the vacuity is a goal state rather than an argument:" },
        { "t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\nhp : (0 ↦ 1) (fun x => 0) Heap.empty\n⊢ aFalse (fun x => 0) Heap.empty" },
        { "t": "p",
          "h": "You are asked for <code>False</code>, and handed <code>Heap.empty = Heap.singleton 0 1</code> to make it from. The star bought you nothing at all." }
      ] },

    { "t": "h3", "s": "Two moves" },

    { "t": "txt",
      "src": "  to PROVE  (P -∗ Q) σ h :\n      intro h' hd hp        -- name the incoming heap, its disjointness, and the P-fact\n      ⊢ Q σ (Heap.union h h')\n\n  to USE    hw : (P -∗ Q) σ h  against  hp : P σ h'  with  hd : Heap.disjoint h h' :\n      hw h' hd hp  :  Q σ (Heap.union h h')\n                     -- note the ORDER: heap, then disjointness, then the fact" },

    { "t": "p",
      "h": "Both are free, because elaboration unfolds definitions: <code>(Q -∗ R) σ h</code> displays as an application of a constant and <i>reduces</i> to a <code>∀</code>, so <code>intro</code> takes it, and a hypothesis <code>hw : (P -∗ Q) σ h</code> is already a function, so <code>hw h' hd hp</code> typechecks with nothing done to it first. In the next exercise a single <code>intro</code> line walks <code>Entails</code>, then an arrow, then <code>wand</code>, absorbing six names in a row. Three of them in, the goal is" },

    { "t": "state", "src": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ (Q -∗ R) σ hh" },

    { "t": "p",
      "h": "which is not visibly a <code>∀</code>. Ask, and it is:" },

    { "t": "code", "tag": "sketch",
      "src": "show ∀ h', Heap.disjoint hh h' → Q σ h' → R σ (Heap.union hh h')" },

    { "t": "state", "src": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ ∀ (h' : Heap), hh.disjoint h' → Q σ h' → R σ (hh.union h')" },

    { "t": "ex",
      "id": "m11-1",
      "name": "wand_intro",
      "hard": false,
      "why": "Currying, and the only way you will ever build a wand. Nobody exhibits a heap and checks the definition by hand; you name the entailment the wand curries. The list with a hole, below, is this move with <code>P</code> the tail, <code>Q</code> the node, <code>R</code> the whole list.",
      "setup": "No lemma is needed, and that is the point: the adjunction is built into <code>wand</code> rather than proved about it.",
      "goal": "theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R",
      "hints": [
        "Do not think yet — count. <code>Entails</code> unfolds to a <code>∀</code> over the store and the heap followed by an arrow; <code>wand</code> unfolds to a <code>∀</code> over the incoming heap followed by two arrows. How many names can <code>intro</code> absorb before the goal stops being a function type?",
        "Six: <code>intro σ hh hp h' hd hq</code>. The goal left over is <code>R σ (hh.union h')</code>.",
        "The hypothesis <code>h : P ∗ Q ⊢ R</code> is <code>∀ σ h, (P ∗ Q) σ h → R σ h</code>. Apply it at <code>σ</code> and at the heap <code>Heap.union hh h'</code>, and it hands you the goal in exchange for one thing.",
        "That thing is <code>(P ∗ Q) σ (Heap.union hh h')</code>. You are not being asked to choose a cut; the cut is already sitting in your context.",
        "Given a heap <code>hh</code> satisfying <code>P</code> and a disjoint <code>h'</code> satisfying <code>Q</code>, feed the pair to <code>h</code> as a star with cut <code>⟨hh, h'⟩</code> and equation <code>rfl</code>."
      ],
      "sol": "theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R := by\n  intro σ hh hp h' hd hq\n  exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
      "expl": "The heap equation is <code>rfl</code> because the goal’s heap <i>is</i> <code>Heap.union hh h'</code> — the wand’s definition put it there. <code>intro</code> hands you four of the star’s five ingredients and the fifth, the equation, is free.",
      "walk": [
        { "tac": "intro σ hh hp h' hd hq",
          "h": "Six introductions through three layers of definition. Read them off: the store, the heap you own, your proof of <code>P</code> about it, the heap you are handed, its disjointness from yours, its proof of <code>Q</code>. The first three come from <code>Entails</code>, the last three from <code>wand</code>." },
        { "tac": "exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
          "h": "<code>h σ (Heap.union hh h')</code> specialises the entailment to this store and this heap, leaving a function that wants <code>(P ∗ Q) σ (Heap.union hh h')</code>. The bracket supplies it: left piece <code>hh</code>, right piece <code>h'</code>, disjointness <code>hd</code>, heap equation <code>rfl</code>, then the two facts." }
      ],
      "deep": [
        { "t": "trace",
          "title": "wand_intro, one <code>intro</code> at a time",
          "start": "P Q R : Assertion\nh : P ∗ Q ⊢ R\n⊢ P ⊢ Q -∗ R",
          "steps": [
            { "tac": "intro σ",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\n⊢ ∀ (h : Heap), P σ h → (Q -∗ R) σ h",
              "h": "<code>Entails</code> has unfolded. Lean names the bound heap <code>h</code> in the display even though <code>h</code> is taken — the binder is not in the context yet, so there is no clash. That is why the solution introduces it as <code>hh</code>." },
            { "tac": "intro hh",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\n⊢ P σ hh → (Q -∗ R) σ hh",
              "h": "An ordinary arrow." },
            { "tac": "intro hp",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ (Q -∗ R) σ hh",
              "h": "The moment worth staring at: not a <code>∀</code>, not an arrow, not a conjunction — an application of a defined constant. Most tactics stop here." },
            { "tac": "intro h'",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\n⊢ hh.disjoint h' → Q σ h' → R σ (hh.union h')",
              "h": "<code>wand</code> unfolded silently and its <code>∀ h'</code> was consumed. What remains is the tail of the definition." },
            { "tac": "intro hd",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\nhd : hh.disjoint h'\n⊢ Q σ h' → R σ (hh.union h')",
              "h": "Disjointness is now yours. It is the ingredient the star on the next line demands, and it arrived for free." },
            { "tac": "intro hq",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\nhd : hh.disjoint h'\nhq : Q σ h'\n⊢ R σ (hh.union h')",
              "h": "End of the road. Read the context bottom-up and it is literally the contents of a star." },
            { "tac": "exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
              "h": "Assemble the star at the heap the goal is already about, and apply the hypothesis." }
          ],
          "done": "No goals." },
        { "t": "cmp",
          "left": {
            "t": "What makes the equation <code>rfl</code>",
            "kind": "good",
            "h": "The star wants <code>Heap.union hh h' = Heap.union hh h'</code>. Both sides are the same term, because the wand’s definition chose the goal’s heap to be that union in the first place."
          },
          "right": {
            "t": "Where it would not be",
            "h": "Curry the other factor — hypothesis <code>Q ∗ P ⊢ R</code> — and the cut becomes <code>⟨h', hh⟩</code>, so the equation is <code>Heap.union hh h' = Heap.union h' hh</code>. Not <code>rfl</code>: union is left-biased and commutes only given disjointness.",
            "src": "theorem wand_intro_flip {P Q R : Assertion} (h : Q ∗ P ⊢ R) : P ⊢ Q -∗ R := by\n  intro σ hh hp h' hd hq\n  exact h σ (Heap.union hh h') ⟨h', hh, disjoint_symm hd, union_comm hd, hq, hp⟩"
          } },
        { "t": "p",
          "h": "That is why the definition writes <code>Heap.union h h'</code> and not <code>Heap.union h' h</code>. The convention is chosen so that <code>wand_intro</code> — the lemma you will use hundreds of times — costs nothing; the right-hand column is what the other convention charges at every single use." }
      ],
      "pitfall": "Ordering the bracket by <i>recency</i> rather than by the statement. <code>h'</code> is the heap you were just handed, so it feels like the natural first component — but the star you owe is <code>(P ∗ Q) σ …</code> and <code>P</code> lives in <code>hh</code>. Writing <code>⟨h', hh, hd, rfl, hp, hq⟩</code> produces three errors at once: <code>The argument hd has type hh.disjoint h' but is expected to have type h'.disjoint hh</code>, the same for <code>hp</code>, and <code>rfl has type ?m = ?m but is expected to have type hh.union h' = h'.union hh</code>. <b>Three simultaneous mismatches inside one <code>⟨…⟩</code> almost always means the components are in the wrong order, not that they are the wrong components.</b>",
      "variants": "Delete <code>Heap.disjoint h h'</code> from the definition of <code>wand</code> and this proof dies at once: <code>hd</code> is the star’s third slot and there is nothing left to put there. The clause is not hygiene; it is the star’s disjointness obligation, pre-paid. Reverse the <i>conclusion</i> to <code>Q ⊢ P -∗ R</code> and the theorem stays true — but not by the same proof with <code>hp</code> and <code>hq</code> swapped, which fails on <code>hd</code> and on <code>rfl</code>. You need <code>⟨h', hh, disjoint_symm hd, union_comm hd, hp, hq⟩</code>, the same two lemma applications as <code>wand_intro_flip</code>. <code>∗</code> is commutative, so which side you curry is a free choice; it is never a free <i>proof</i>."
    },

    { "t": "ex",
      "id": "m11-2",
      "name": "wand_elim",
      "hard": false,
      "why": "Uncurrying: modus ponens for resources. The wand and its argument must sit in disjoint heaps — you cannot redeem a wand with memory you have already spent. This is the <b>counit</b> of the adjunction, and in the next exercise but one it is the only thing the hard direction needs.",
      "setup": "A star hypothesis in, a bare assertion out. Everything you need is inside the star; no heap is constructed and no M2 lemma is used.",
      "goal": "theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q",
      "hints": [
        "There is exactly one thing you ever do with a star hypothesis: take it apart into <code>⟨h₁, h₂, hd, hu, hw, hp⟩</code>. You can do that in the <code>intro</code> pattern rather than with a separate <code>obtain</code>.",
        "Read what you hold: <code>hw : (P -∗ Q) σ h₁</code>, <code>hp : P σ h₂</code>, <code>hd : h₁.disjoint h₂</code>. Redeeming the wand is <code>hw h₂ hd hp</code>.",
        "That expression has type <code>Q σ (h₁.union h₂)</code>. The goal says <code>Q σ h</code>. Those are not the same term, even with <code>hu : h = h₁.union h₂</code> sitting in the context. Fix the goal before you try to close it.",
        "Destructure the star and apply the wand to the second piece."
      ],
      "sol": "theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by\n  intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩\n  rw [hu]\n  exact hw h₂ hd hp",
      "expl": "<code>rw [hu]</code> puts the goal’s heap into the shape the wand produces, and then the wand produces it. One line of content; the rest is the star handing over a cut and a disjointness proof that <code>wand</code> was defined to accept.",
      "walk": [
        { "tac": "intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩",
          "h": "The six names are the two pieces, their disjointness, the equation <code>h = h₁ ∪ h₂</code>, and one fact per piece. <code>hw</code> lands on <code>h₁</code> and <code>hp</code> on <code>h₂</code> — the order they appear in <code>(P -∗ Q) ∗ P</code>." },
        { "tac": "rw [hu]",
          "h": "Turns <code>Q σ h</code> into <code>Q σ (h₁.union h₂)</code>. The only step with a choice in it, and the choice is forced: a wand can only produce a statement about a union." },
        { "tac": "exact hw h₂ hd hp",
          "h": "Three arguments in the order the definition binds them — the heap contributed, the proof it is disjoint from the wand’s own heap, the proof it satisfies the antecedent." }
      ],
      "deep": [
        { "t": "trace",
          "title": "wand_elim, tactic by tactic",
          "start": "P Q : Assertion\n⊢ (P -∗ Q) ∗ P ⊢ Q",
          "steps": [
            { "tac": "intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩",
              "state": "P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhw : (P -∗ Q) σ h₁\nhp : P σ h₂\n⊢ Q σ h",
              "h": "Lean collapses the three heaps onto one line because they share a type. Everything needed is present; the only problem is that the goal mentions <code>h</code> and the tools mention <code>h₁.union h₂</code>." },
            { "tac": "rw [hu]",
              "state": "P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhw : (P -∗ Q) σ h₁\nhp : P σ h₂\n⊢ Q σ (h₁.union h₂)",
              "h": "Only the goal changed. <code>hu</code> points from <code>h</code> to the union, which is the direction wanted; had <code>star</code> oriented its equation the other way this line would be <code>rw [← hu]</code>. <code>subst hu</code> also works and additionally removes <code>h</code> from the context." },
            { "tac": "exact hw h₂ hd hp",
              "h": "Exact match." }
          ],
          "done": "No goals." },
        { "t": "p",
          "h": "One thing here is not luck. <code>hd</code> arrives from the star as <code>h₁.disjoint h₂</code> — wand’s heap first, contributed heap second — which is exactly the orientation <code>wand</code> asks for. Both definitions put the owned heap on the left, and they were written to line up. Flip either convention and this proof needs a <code>disjoint_symm</code>." }
      ],
      "pitfall": "Skipping <code>rw [hu]</code> and going straight to <code>exact hw h₂ hd hp</code>, on the grounds that <code>hu</code> is in the context so Lean surely knows. It does not: <code>Type mismatch: hw h₂ hd hp has type Q σ (h₁.union h₂) but is expected to have type Q σ h</code>. <code>h</code> is an opaque local variable, and the two types are equal only <i>given</i> <code>hu</code>. This is the most common failure in the chapter, and the fix never changes: rewrite the goal into union form before applying anything.",
      "variants": "Weaken <code>∗</code> to <code>∧</code> and the theorem becomes <b>false</b> — the counterexample is at the end of this chapter, and it fails for the reason in the <code>why</code> above: under <code>∧</code> the wand and its argument share a heap, so the disjointness the wand demands can never be supplied. Swap the factors to <code>P ∗ (P -∗ Q) ⊢ Q</code> and it stays true at the cost of one step, <code>entails_trans (star_comm P (P -∗ Q)) (wand_elim P Q)</code>. Drop the antecedent — <code>(P -∗ Q) ⊢ Q</code> — and it is false for the obvious reason: a promise and nothing to pay for it."
    },

    { "t": "h3", "s": "The list with a hole" },

    { "t": "p",
      "h": "The traversal lent out <code>node p x n</code> and kept the tail. Here is what it is holding, and here is the exchange when the node comes back." },

    { "t": "code",
      "tag": "illustration",
      "cap": "Compiled against the M11 prelude. <code>listRep_plug</code> is nothing but <code>star_comm</code> followed by <code>wand_elim</code>.",
      "src": "-- you kept the tail; what you kept is a `[x] ++ xs`-list minus its head node\ntheorem listRep_hole (x : Nat) (xs : List Nat) (p n : Loc) (hp : p ≠ 0) :\n    listRep xs n ⊢ node p x n -∗ listRep (x :: xs) p := by\n  intro σ h hxs h' hd hnode\n  refine ⟨n, Heap.empty, Heap.union h h', disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩\n  exact ⟨h', h, disjoint_symm hd, union_comm hd, hnode, hxs⟩\n\n-- and handing the node back reassembles the list\ntheorem listRep_plug (x : Nat) (xs : List Nat) (p n : Loc) :\n    node p x n ∗ (node p x n -∗ listRep (x :: xs) p) ⊢ listRep (x :: xs) p :=\n  entails_trans (star_comm _ _) (wand_elim _ _)" },

    { "t": "p",
      "h": "The seven-slot <code>refine</code> is the only fiddly line, and it is fiddly for M10 reasons. After the <code>intro</code> the goal is <code>listRep (x :: xs) p σ (h.union h')</code> — one cons layer — so the tuple is the existential witness <code>n</code> followed by the six slots of the outer star: nothing on the left, everything on the right, <code>⟨hp, rfl⟩</code> for the <code>pure</code>, and a hole. What the hole leaves is <code>(node p x n ∗ listRep xs n) σ (h.union h')</code>, and the last line cuts <i>that</i> with the node’s heap first, which is why <code>union_comm hd</code> is in slot four. One <code>union_comm</code> is the whole price of the definition’s left-to-right convention." },

    { "t": "p",
      "h": "Read the statement as an accounting identity. You own the tail; you do not own the head node; and what you can still say about yourself is “a <code>node p x n</code> would make me a <code>listRep (x :: xs) p</code>”. M13’s traversal does <i>not</i> take this route — it carries the walked prefix as an <code>lseg</code> and closes with <code>lseg_listRep</code> — and it can afford not to, because for a linked list the hole happens to be shaped like another segment and already has a name. The wand is what you reach for when the remainder has no name of its own: a tree with one subtree lent out, a record with one field in someone else’s hands. That is the ordinary case, which is why wands are everywhere in Iris and only occasionally here." },

    { "t": "h3", "s": "Why it is an adjunction" },

    { "t": "p",
      "h": "The analogy with ordinary implication is exact, and so is the difference. Ordinary implication satisfies the currying adjunction" },

    { "t": "txt", "src": "  P ∧ Q → R      iff      P → (Q → R)" },

    { "t": "p",
      "h": "and <code>wand</code> is defined so that the same holds with <code>∗</code> in place of <code>∧</code>:" },

    { "t": "txt", "src": "  P ∗ Q ⊢ R      iff      P ⊢ Q -∗ R" },

    { "t": "ex",
      "id": "m11-3",
      "name": "star_wand_adjunction",
      "hard": false,
      "why": "The adjunction itself. Prove the ⟸ direction <i>from</i> the two previous lemmas rather than from scratch — that is what having them is for. Once it is on the shelf, every later wand law is a two-line rearrangement instead of an argument about heaps.",
      "setup": "<code>wand_intro</code>, <code>wand_elim</code>, <code>star_mono_left</code>, <code>entails_trans</code>. Do not <code>intro σ h</code> anywhere: if you find yourself naming a heap, you are proving it the wrong way.",
      "goal": "theorem star_wand_adjunction (P Q R : Assertion) :\n    (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)",
      "hints": [
        "<code>constructor</code>, then two <code>·</code> bullets. <code>mp</code> is the direction written first inside the <code>↔</code>: <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>.",
        "That first goal is <code>wand_intro</code>’s type with the implicits instantiated. You need no <code>intro</code> and no application: <code>exact wand_intro</code>, bare.",
        "For <code>mpr</code>: <code>intro h</code> leaves <code>h : P ⊢ Q -∗ R</code> and goal <code>P ∗ Q ⊢ R</code>. What does <code>wand_elim Q R</code> want on its left?",
        "<code>(Q -∗ R) ∗ Q</code>. So improve the left factor of <code>P ∗ Q</code> along <code>h</code> and leave the right factor alone — <code>star_mono_left Q h</code>, whose explicit argument is the factor being <i>kept</i> — then chain with <code>entails_trans</code>.",
        "⟹ is <code>wand_intro</code>. For ⟸: monotonicity gives <code>P ∗ Q ⊢ (Q -∗ R) ∗ Q</code>, and <code>wand_elim</code> finishes."
      ],
      "sol": "theorem star_wand_adjunction (P Q R : Assertion) : (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R) := by\n  constructor\n  · exact wand_intro\n  · intro h\n    refine entails_trans (star_mono_left Q h) ?_\n    exact wand_elim Q R",
      "expl": "Note what is <i>not</i> in this proof: no <code>σ</code>, no heap, no <code>Heap.union</code>, no disjointness. That absence is the sign that you have stopped working in the model and started working in the logic.",
      "walk": [
        { "tac": "constructor",
          "h": "Two goals, in the order the two sides appear inside the <code>↔</code>." },
        { "tac": "· exact wand_intro",
          "h": "The goal is <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>; <code>wand_intro</code> has type <code>∀ {P Q R}, P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>. Unification fixes the three implicits and the two types are identical." },
        { "tac": "· intro h",
          "h": "Here <code>intro</code> genuinely does something: the goal is an implication between two entailments, so <code>h : P ⊢ Q -∗ R</code> becomes a hypothesis." },
        { "tac": "refine entails_trans (star_mono_left Q h) ?_",
          "h": "Supplying the first factor determines the middle assertion: <code>star_mono_left Q h : P ∗ Q ⊢ (Q -∗ R) ∗ Q</code>, so the hole must be <code>(Q -∗ R) ∗ Q ⊢ R</code>." },
        { "tac": "exact wand_elim Q R",
          "h": "The previous exercise, instantiated at the wand’s antecedent and conclusion." }
      ],
      "deep": [
        { "t": "trace",
          "title": "star_wand_adjunction, tactic by tactic",
          "start": "P Q R : Assertion\n⊢ P ∗ Q ⊢ R ↔ P ⊢ Q -∗ R",
          "steps": [
            { "tac": "constructor",
              "state": "case mp\nP Q R : Assertion\n⊢ P ∗ Q ⊢ R → P ⊢ Q -∗ R\n\ncase mpr\nP Q R : Assertion\n⊢ P ⊢ Q -∗ R → P ∗ Q ⊢ R",
              "h": "Notice how little bracketing the printed goals need: <code>⊢</code> at 40 is looser than <code>→</code>, so <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code> really does mean <code>(P ∗ Q ⊢ R) → (P ⊢ Q -∗ R)</code>." },
            { "tac": "· exact wand_intro",
              "h": "Closed by a bare lemma name." },
            { "tac": "· intro h",
              "state": "case mpr\nP Q R : Assertion\nh : P ⊢ Q -∗ R\n⊢ P ∗ Q ⊢ R",
              "h": "The case tag survives into the focused goal, so you can tell at a glance which half you are in." },
            { "tac": "refine entails_trans (star_mono_left Q h) ?_",
              "state": "case mpr\nP Q R : Assertion\nh : P ⊢ Q -∗ R\n⊢ (Q -∗ R) ∗ Q ⊢ R",
              "h": "What remains is <code>wand_elim</code> verbatim. The previous exercise was designed to be exactly the hole this step leaves." },
            { "tac": "exact wand_elim Q R", "h": "Done." }
          ],
          "done": "No goals." },
        { "t": "cmp",
          "left": {
            "t": "Proving ⟸ from the algebra",
            "kind": "good",
            "h": "Two lemma applications and a composition. No heap appears. Change the resource model — fractional permissions, say — and this proof does not move.",
            "src": "intro h\nrefine entails_trans (star_mono_left Q h) ?_\nexact wand_elim Q R"
          },
          "right": {
            "t": "Proving ⟸ from the model",
            "h": "Also short, and it compiles — but it reaches past the two lemmas into the definitions of <code>star</code> and <code>wand</code>, and it is tied to this representation of heaps.",
            "src": "theorem adjunction_mpr_by_hand (P Q R : Assertion) (h : P ⊢ Q -∗ R) :\n    P ∗ Q ⊢ R := by\n  intro σ hh ⟨h₁, h₂, hd, hu, hp, hq⟩\n  rw [hu]\n  exact h σ h₁ hp h₂ hd hq"
          } }
      ],
      "pitfall": "Bullets in the wrong order. Put the <code>entails_trans</code> proof first and the informative error is <code>Type mismatch: wand_intro has type ?m.14 ∗ ?m.15 ⊢ ?m.16 → ?m.14 ⊢ ?m.15 -∗ ?m.16 but is expected to have type P ⊢ Q -∗ R → P ∗ Q ⊢ R</code>. The numbers mean nothing; what carries information is that <code>?m.14</code> occurs on <i>both</i> sides of the arrow, and likewise the other two — those are the unsolved implicits, and the repetition is the shape unification was trying to match. A subtler slip: <code>star_mono_left</code>’s explicit argument is the factor you are <i>keeping</i>. Reach for <code>star_mono_right</code> and you get <code>star_mono_right Q h has type Q ∗ P ⊢ Q ∗ (Q -∗ R)</code>, with the factors on the wrong sides.",
      "variants": "This <code>↔</code> is an equivalence of <i>provability</i>: two <code>Prop</code>s about entailment, not an assertion-level <code>⊣⊢</code>. Replace <code>∗</code> by <code>∧</code> and <code>-∗</code> by the naive <code>aImp</code> and the theorem is <b>still true</b> in both directions — which is not a defect but the point. BI has two conjunctions and two implications and they pair off: <code>∧</code> with <code>aImp</code>, <code>∗</code> with <code>-∗</code>. What breaks is <i>crossing</i> the pairing, and this chapter’s two counterexamples are precisely the two crossed counits. Note also how little each direction costs: ⟹ uses no lemma at all, ⟸ uses exactly one. With <code>wand</code> defined as it is, the adjunction rests on nothing but monotonicity of <code>∗</code> in its left argument — no associativity, no commutativity, no unit."
    },

    { "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "<code>-∗</code> is the <b>right adjoint</b> of <code>∗</code>. Assertions with <code>(∗, emp, -∗)</code> form a closed symmetric monoidal category — a <i>BI algebra</i> — and separation logic is its internal logic. The laws below are then not things to memorise; they are the standard consequences of an adjunction." },

    { "t": "p",
      "h": "Two M4 lemmas stop looking lucky. Left adjoints preserve colimits, so <code>(− ∗ R)</code> had to distribute over <code>∨</code> and over <code>∃</code>: <code>star_or_left</code> and <code>star_exists_left</code> were forced by the definition of <code>∗</code> before anyone thought to prove them. Dually the right adjoint preserves limits, which is <code>P -∗ (aAnd Q R) ⊣⊢ aAnd (P -∗ Q) (P -∗ R)</code>. Monotonicity comes from the same place, and it is the last thing to prove by hand." },

    { "t": "ex",
      "id": "m11-4",
      "name": "wand_mono",
      "hard": false,
      "why": "Contravariant on the left, covariant on the right — exactly like a function type, for exactly the same reason. This is what lets you weaken a wand you are holding, by strengthening what you promise to accept or weakening what you promise to deliver, without unfolding the definition again.",
      "setup": "Two entailments in, one out. As in <code>wand_intro</code>, <code>intro</code> does all the structural work and the remaining line is a composition of three functions.",
      "goal": "theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q')",
      "hints": [
        "Same opening as <code>wand_intro</code>: six names, three from <code>Entails</code> and three from the <code>P' -∗ Q'</code> you are constructing.",
        "You hold <code>hw : (P -∗ Q) σ h</code>, <code>hd : h.disjoint h'</code>, <code>hp' : P' σ h'</code>, and the goal is <code>Q' σ (h.union h')</code>. The wand wants a <code>P</code> at <code>h'</code> and you have a <code>P'</code>. Convert.",
        "<code>hp σ h' hp' : P σ h'</code>. Feed that to the wand: <code>hw h' hd (hp σ h' hp') : Q σ (h.union h')</code>. One conversion left, and it is the same trick with <code>hq</code>.",
        "Compose: turn the given <code>P'</code>-heap into a <code>P</code>-heap with <code>hp</code>, apply the wand, then push the result along <code>hq</code>."
      ],
      "sol": "theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q') := by\n  intro σ h hw h' hd hp'\n  exact hq σ _ (hw h' hd (hp σ h' hp'))",
      "expl": "If the variance surprises you, look at the definition: <code>P</code> occurs to the left of an arrow and <code>Q</code> to the right. The proof is a three-fold composition read right to left, which is the term you would write for the same statement about function types.",
      "walk": [
        { "tac": "intro σ h hw h' hd hp'",
          "h": "Worth noting which definition each name comes from: <code>σ</code>, <code>h</code>, <code>hw</code> from <code>Entails</code> — so <code>hw</code> is the wand being handed to you — and <code>h'</code>, <code>hd</code>, <code>hp'</code> from the wand you must produce." },
        { "tac": "exact hq σ _ (hw h' hd (hp σ h' hp'))",
          "h": "Innermost first: <code>hp σ h' hp'</code> upgrades <code>hp'</code> to <code>P σ h'</code>, which is what the wand demands; <code>hw h' hd (…)</code> redeems it and yields <code>Q σ (h.union h')</code>; <code>hq σ _ (…)</code> pushes that to <code>Q'</code>. The <code>_</code> can only be <code>Heap.union h h'</code>, because that is the heap of the term being passed in." }
      ],
      "deep": [
        { "t": "trace",
          "title": "wand_mono, with the <code>intro</code> split so you can see the halfway point",
          "start": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\n⊢ P -∗ Q ⊢ P' -∗ Q'",
          "steps": [
            { "tac": "intro σ h hw",
              "state": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\nσ : Store\nh : Heap\nhw : (P -∗ Q) σ h\n⊢ (P' -∗ Q') σ h",
              "h": "The clearest statement of what the theorem says: <i>the same heap</i> <code>h</code> that satisfies the old wand must satisfy the new one. Weakening a wand creates and destroys no resource." },
            { "tac": "intro h' hd hp'",
              "state": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\nσ : Store\nh : Heap\nhw : (P -∗ Q) σ h\nh' : Heap\nhd : h.disjoint h'\nhp' : P' σ h'\n⊢ Q' σ (h.union h')",
              "h": "Now the variance is in the context rather than asserted. <code>hp'</code> is a <code>P'</code>-fact pointing <i>into</i> the proof, so <code>hp</code> must run from <code>P'</code> to <code>P</code>; the goal is a <code>Q'</code>-fact pointing <i>out</i>, so <code>hq</code> must run from <code>Q</code> to <code>Q'</code>." },
            { "tac": "exact hq σ _ (hw h' hd (hp σ h' hp'))",
              "h": "The three-fold composition." }
          ],
          "done": "No goals." },
        { "t": "detail",
          "title": "Naming the middle step, and what it does to the error message",
          "tag": "aside",
          "open": false,
          "blocks": [
            { "t": "p", "h": "This version compiles and shows the intermediate type explicitly:" },
            { "t": "code", "tag": "illustration",
              "src": "theorem wand_mono_explicit {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q') := by\n  intro σ h hw h' hd hp'\n  have step : Q σ (Heap.union h h') := hw h' hd (hp σ h' hp')\n  exact hq σ _ step" },
            { "t": "p", "h": "Write <code>hq σ h step</code> instead — the naive guess — and you get <code>Application type mismatch: The argument step has type Q σ (h.union h') but is expected to have type Q σ h</code>. Make the same mistake in the one-line version and Lean has no name to use, so it prints the whole term: <code>The argument hw h' hd (hp σ h' hp') has type …</code>. Identical mismatch, much worse label. That is the everyday argument for <code>have</code> — not that it changes the proof, but that it changes the error." }
          ] },
        { "t": "p",
          "h": "Get the variance backwards and the statement is false, so here is the witness rather than the assertion:" },
        { "t": "code",
          "tag": "illustration",
          "cap": "<code>P = 0 ↦ 1</code>, <code>P' = aTrue</code>, <code>Q = 0 ↦ 1</code>, at the empty heap. The empty heap does hold <code>(0 ↦ 1) -∗ (0 ↦ 1)</code>. It does not hold <code>aTrue -∗ (0 ↦ 1)</code>, because that wand can be redeemed at the empty heap itself — disjoint from everything and <code>aTrue</code> for free — which would demand <code>Heap.empty = Heap.singleton 0 1</code>.",
          "src": "theorem wand_mono_needs_contravariance :\n    ¬ (∀ P P' Q : Assertion, (P ⊢ P') → ((P -∗ Q) ⊢ (P' -∗ Q))) := by\n  intro hcontra\n  have hw : ((0 ↦ 1) -∗ (0 ↦ 1)) (fun _ => 0) Heap.empty := by\n    intro h' _ hp\n    rw [union_empty_left]\n    exact hp\n  have hbad := hcontra (0 ↦ 1) aTrue (0 ↦ 1) (fun _ _ _ => trivial) (fun _ => 0) Heap.empty hw\n  have hgot := hbad Heap.empty (disjoint_empty_left _) trivial\n  rw [union_empty_left] at hgot\n  have hz : Heap.empty 0 = Heap.singleton 0 1 0 := by rw [hgot]\n  rw [singleton_same] at hz\n  exact absurd hz (by simp [Heap.empty])" },
        { "t": "p",
          "h": "The mechanism is the <code>∀ h'</code> again. Widening the antecedent widens the set of heaps the promise must answer for, and a promise good for one cell need not be good for every heap. Widening the <i>conclusion</i> costs nothing, because the conclusion is what the promise produces. That asymmetry is the whole of the variance." }
      ],
      "pitfall": "Writing <code>hq σ h (…)</code> instead of <code>hq σ _ (…)</code>, because <code>h</code> is the heap you have been thinking about. The heap in the goal is <code>h.union h'</code>, and Lean says so: <code>Application type mismatch: the argument hw h' hd (hp σ h' hp') has type Q σ (h.union h') but is expected to have type Q σ h</code>. When an entailment is applied at a heap, the heap is whatever the fact you are converting is about — in a wand proof, essentially always the union. The <code>_</code> is not laziness; there is exactly one heap that can go there.",
      "variants": "Reverse <code>hp</code> to <code>P ⊢ P'</code> and the theorem is <b>false</b>, and you can name the point of failure from the goal state: you hold <code>hp' : P' σ h'</code>, the wand demands <code>P σ h'</code>, and the reversed hypothesis runs the wrong way. Reverse <code>hq</code> to <code>Q' ⊢ Q</code> and it fails symmetrically at the last step. Drop <code>hp</code> and keep <code>hq</code> and you get the useful special case <code>(P -∗ Q) ⊢ (P -∗ Q')</code>, which is <code>wand_mono (entails_refl P) hq</code> — the same manoeuvre that produced <code>star_mono_left</code> and <code>star_mono_right</code> out of <code>star_mono</code>."
    },

    { "t": "h3", "s": "Consequences, for free" },

    { "t": "p",
      "h": "None of the three proofs below mentions a heap, a store, or <code>Heap.union</code>. Each is <code>wand_intro</code> applied to something already in hand: a reflexivity, or a rearrangement of stars. That is what “right adjoint of <code>∗</code>” means operationally — a wand goal is a star goal in disguise, and <code>wand_intro</code> is the disguise coming off." },

    { "t": "code",
      "tag": "illustration",
      "cap": "Three standard laws, each from the adjunction plus M4. Compiled against the M11 prelude.",
      "src": "-- the unit of the adjunction\ntheorem wand_unit (P Q : Assertion) : P ⊢ Q -∗ (P ∗ Q) :=\n  wand_intro (entails_refl (P ∗ Q))\n\n-- currying, twice\ntheorem wand_curry (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R) :=\n  wand_intro (wand_intro (entails_trans (star_assoc_left _ _ _) (wand_elim (P ∗ Q) R)))\n\n-- a wand may be framed, just like a triple\ntheorem wand_frame (P Q R : Assertion) : (P -∗ Q) ⊢ (P ∗ R) -∗ (Q ∗ R) :=\n  wand_intro (entails_trans (star_assoc_right _ _ _) (star_mono_left R (wand_elim P Q)))" },

    { "t": "p",
      "h": "<code>wand_curry</code> is four moves. Two <code>wand_intro</code>s reduce the goal to <code>(((P ∗ Q) -∗ R) ∗ P) ∗ Q ⊢ R</code>; <code>star_assoc_left</code> reassociates the right-hand pair into <code>P ∗ Q</code>; <code>wand_elim</code> closes it. The semantic proof also works, and has to assemble <code>Heap.disjoint h (Heap.union h₁ h₂)</code> out of <code>disjoint_union_left</code> and <code>disjoint_union_right</code> and then repair the goal with <code>union_assoc</code>. Only one of the two is still a two-line proof after you change the resource model." },

    { "t": "h4", "s": "And one that fails" },

    { "t": "p",
      "h": "The <code>∗</code> in <code>wand_elim</code> does not weaken to <code>∧</code>." },

    { "t": "code",
      "tag": "illustration",
      "cap": "The witness is <code>Heap.singleton 0 1</code>, which satisfies both conjuncts at once. <code>rw [hp] at hd</code> rewrites the incoming heap away inside the hypothesis only, leaving <code>hd : (Heap.singleton 0 1).disjoint (Heap.singleton 0 1)</code> — already absurd, so the goal is never touched; <code>hd 0</code> applies it at location <code>0</code>, and the two branches of the <code>∨</code> are literally the same proposition, which is why one chained script closes both.",
      "src": "theorem wand_and_elim_fails :\n    ¬ (∀ P Q : Assertion, aAnd (P -∗ Q) P ⊢ Q) := by\n  intro hcontra\n  refine hcontra (0 ↦ 1) aFalse (fun _ => 0) (Heap.singleton 0 1) ⟨?_, rfl⟩\n  intro h' hd hp\n  rw [hp] at hd\n  rcases hd 0 with hx | hx <;> rw [singleton_same] at hx <;> exact absurd hx (by simp)" },

    { "t": "p",
      "h": "A single cell satisfies <code>0 ↦ 1</code>. Does it satisfy <code>(0 ↦ 1) -∗ aFalse</code>? The wand quantifies over heaps <b>disjoint</b> from it that satisfy <code>0 ↦ 1</code>, and there are none: any such heap would be <code>Heap.singleton 0 1</code>, which overlaps. So the promise is kept vacuously — it commits you to producing <code>False</code> in a situation that cannot arise. Under <code>∧</code> you then hold both conjuncts on that one heap and derive nothing. Under <code>∗</code> you cannot, because the star insists the two conjuncts live on disjoint pieces, which is exactly the hypothesis the wand needs. <b>The separating conjunction is not a convenience in <code>wand_elim</code>; it is the entire content of the rule.</b>" },

    { "t": "h3", "s": "The frame rule with its postcondition already chosen" },

    { "t": "p",
      "h": "<code>hoare_frame</code> carries an arbitrary <code>R</code> across a command. Take <code>R</code> to be a wand. The postcondition becomes <code>Q ∗ (Q -∗ S)</code>, and <code>wand_elim</code> collapses that to <code>S</code> — so a triple with a small footprint, plus a wand, is a triple for whatever postcondition you name." },

    { "t": "code",
      "tag": "illustration",
      "cap": "Compiled against the M11 prelude. The literature calls the second one the <i>ramified</i> frame rule; Iris’s proof mode is largely this rule applied over and over.",
      "src": "theorem heapOnly_wand {P Q : Assertion} (hp : HeapOnly P) (hq : HeapOnly Q) :\n    HeapOnly (P -∗ Q) := by\n  intro σ σ' h hw h' hd hp'\n  exact hq σ σ' _ (hw h' hd (hp σ' σ h' hp'))\n\ntheorem hoare_ramified_frame {P Q S : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c (Q -∗ S)) :\n    Hoare (P ∗ (Q -∗ S)) c S :=\n  hoare_consequence (entails_refl _) (hoare_frame hc hlocal hpres)\n    (entails_trans (star_comm Q (Q -∗ S)) (wand_elim Q S))" },

    { "t": "p",
      "h": "The <code>Preserves</code> obligation is the same one M8 and M9 always charge, and the same two helpers pay it: <code>heapOnly_wand</code> when both ends of the wand are heap-only, <code>preserves_of_storeStable</code> for a write or a free. Note that <code>heapOnly_wand</code> uses <code>hp</code> at <code>σ'</code> and <code>σ</code> — in that order — because the antecedent is contravariant, exactly as in <code>wand_mono</code>." },

    { "t": "p",
      "h": "What the rule does not hand you is the small triple. <code>P ∗ (Q -∗ S)</code> is a precondition parametrised by its own postcondition — a function from assertions to assertions — but <code>P</code> and <code>Q</code> are still yours to invent, and every precondition in this workbook so far was found by knowing the answer before writing the proof. Different choices give different preconditions, all of them sound, some of them stronger than they need to be. Nothing proved here says which is weakest, or whether a weakest one exists. M12 stops choosing and starts computing." },

    { "t": "dod",
      "h": "You read <code>-∗</code> as the right adjoint of <code>∗</code> rather than as a second implication; you build wands by naming the entailment they curry; and you can say what goes vacuous in each of the two cheaper definitions." }
  ]
});
