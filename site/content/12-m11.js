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
      "Read <code>P -∗ Q</code> off its definition and say exactly which heap it owns, which heap it asks for, and which heap the conclusion is about.",
      "Prove a wand goal by <code>intro</code> — six binders through three layers of definition — and use a wand hypothesis by feeding it a <i>disjoint</i> heap.",
      "State and prove the adjunction <code>(P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)</code>, and then derive currying, framing and monotonicity <i>from it</i> instead of from the model.",
      "Say why <code>-∗</code> cannot be replaced by pointwise implication, and read the machine-checked counterexample that kills the naive definition line by line, rather than taking it on trust."
    ],
    "needs": [
      "M4: the definition of <code>∗</code> and its two mechanical moves — supply <code>⟨h₁, h₂, hd, hu, hP, hQ⟩</code> to prove a star, <code>obtain</code> the same tuple to use one.",
      "M4 again, as a toolbox: <code>star_mono_left</code>, <code>star_assoc_left</code> / <code>star_assoc_right</code>, <code>star_comm</code>, <code>entails_trans</code>. The adjunction proof is built entirely out of these.",
      "M2: <code>Heap.disjoint</code>, <code>Heap.union</code>, <code>union_comm</code>, <code>union_assoc</code>, and the fact that <code>union</code> is <i>total</i> and does not check disjointness for you.",
      "M0: the anonymous constructor <code>⟨…⟩</code>, and the habit of asking how many things <code>intro</code> can take before you have to think."
    ],
    "payoff": "Every “I gave away part of my structure and here is how to put it back” argument — a loop invariant over a half-traversed list, an Iris-style continuation, the frame rule read backwards — is a wand. Without it you can describe what you own and nothing else."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "Every connective so far says what you own <i>now</i>. <code>l ↦ v</code> says you own a cell. <code>P ∗ Q</code> says you own two disjoint things at once. <code>aExists</code> says you own something whose shape you have not pinned down. What none of them says is what you would own <b>if someone handed you something</b>."
    },
    {
      "t": "p",
      "h": "That gap is not academic. The moment you lend one node of a linked list to a subroutine, the assertion describing what you kept is not a list, and it is not a sub-list either: it is a list <i>minus a node</i>. Nothing in the M4 vocabulary means “minus”. The connective that does is <b>separating implication</b>, written <code>-∗</code> and pronounced <i>magic wand</i>."
    },
    {
      "t": "code",
      "src": "def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')\ninfixr:54 \" -∗ \" => wand"
    },
    {
      "t": "quote",
      "h": "I hold a resource such that, <b>if you give me a separate heap satisfying <code>P</code></b>, the combination satisfies <code>Q</code>."
    },
    {
      "t": "svg",
      "src": "\n<svg viewBox=\"0 0 560 148\" role=\"img\" aria-label=\"The magic wand\">\n  <g class=\"dg\">\n    <rect x=\"14\" y=\"34\" width=\"130\" height=\"38\" rx=\"7\" class=\"dg-box\"/>\n    <text x=\"79\" y=\"58\" text-anchor=\"middle\" class=\"dg-t\">h : P −∗ Q</text>\n    <text x=\"160\" y=\"58\" class=\"dg-t\">+</text>\n    <rect x=\"184\" y=\"34\" width=\"110\" height=\"38\" rx=\"7\" class=\"dg-box a\"/>\n    <text x=\"239\" y=\"58\" text-anchor=\"middle\" class=\"dg-t\">h' : P</text>\n    <path class=\"dg-arr\" d=\"M310 53 L 356 53\"/>\n    <rect x=\"372\" y=\"34\" width=\"168\" height=\"38\" rx=\"7\" class=\"dg-box b\"/>\n    <text x=\"456\" y=\"58\" text-anchor=\"middle\" class=\"dg-t\">h ∪ h' : Q</text>\n    <text x=\"14\" y=\"104\" class=\"dg-note\">A wand is a resource-consuming promise: hand it a separate heap satisfying P</text>\n    <text x=\"14\" y=\"124\" class=\"dg-note\">and the combination satisfies Q. It is the right adjoint of ∗, not of ∧.</text>\n  </g>\n</svg>"
    },
    {
      "t": "anat",
      "src": "def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')\ninfixr:54 \" -∗ \" => wand",
      "parts": [
        {
          "m": "fun σ h =>",
          "h": "An <code>Assertion</code> is a <code>Store → Heap → Prop</code> (M3), so defining one means saying, for every store <code>σ</code> and heap <code>h</code>, what is being claimed. Here <code>h</code> is <b>the heap the wand itself owns</b>. A wand is not a fact about the world; it is a resource, and this is the resource it is."
        },
        {
          "m": "∀ h'",
          "h": "Quantified over <i>every</i> heap you might later be handed, not one particular heap. That is what makes a wand a promise made in advance to an unknown caller. It is also why a wand is a genuinely stronger claim than “here is <code>Q</code> for the heap I happen to be looking at”."
        },
        {
          "m": "Heap.disjoint h h'",
          "h": "The heap you hand over must not overlap the one the wand already holds. This is the clause that makes <code>-∗</code> <i>separating</i> rather than ordinary implication, and it is the clause the counterexample below removes. On paper you would write “take a fresh heap and combine”; Lean cannot, because <code>Heap.union</code> is a total function that silently prefers its left argument (M2). So disjointness has to be an explicit hypothesis of the implication, supplied at the point of use."
        },
        {
          "m": "P σ h'",
          "h": "The antecedent, evaluated at <code>h'</code> — the heap you <b>bring</b> — not at <code>h</code>. Nothing about <code>P</code> is asserted of the wand's own heap. Read the two together: <code>h'</code> is disjoint from <code>h</code> and satisfies <code>P</code>."
        },
        {
          "m": "Q σ (Heap.union h h')",
          "h": "The conclusion, evaluated at the <b>combined</b> heap. This one choice is the whole design. <code>Q</code> gets both halves, which is exactly why using a wand consumes both: the wand's heap is gone into the result, and so is yours."
        },
        {
          "m": "infixr:54",
          "h": "Precedence 54 — below <code>∗</code> at 55, above <code>⊢</code> at 40 — and right-associative, like <code>→</code>. The table below is what that actually means when you read a statement."
        }
      ]
    },
    {
      "t": "tbl",
      "cap": "Verified by asking Lean to print with <code>set_option pp.parens true</code>. Getting these wrong is the single most common way to misread a wand statement.",
      "head": ["You write", "Lean parses", "Because"],
      "rows": [
        ["<code>P ∗ Q -∗ R</code>", "<code>(P ∗ Q) -∗ R</code>", "<code>∗</code> is 55, <code>-∗</code> is 54; the tighter operator groups first."],
        ["<code>P -∗ Q -∗ R</code>", "<code>P -∗ (Q -∗ R)</code>", "<code>infixr</code> — right-associative, exactly like <code>→</code>."],
        ["<code>P ⊢ Q -∗ R</code>", "<code>P ⊢ (Q -∗ R)</code>", "<code>⊢</code> is 40, looser than both. So the adjunction statement needs no brackets."],
        ["<code>P -∗ Q ∗ P ⊢ Q</code>", "<code>(P -∗ (Q ∗ P)) ⊢ Q</code>", "<b>Not</b> <code>wand_elim</code>. The parentheses in <code>(P -∗ Q) ∗ P ⊢ Q</code> are load-bearing; drop them and you have written a different theorem."]
      ]
    },
    {
      "t": "p",
      "h": "The analogy with ordinary implication is exact, and so is the difference. Ordinary implication satisfies the currying adjunction"
    },
    {
      "t": "txt",
      "src": "  P ∧ Q → R      iff      P → (Q → R)"
    },
    {
      "t": "p",
      "h": "and the wand is defined so that the same holds with <code>∗</code> in place of <code>∧</code>:"
    },
    {
      "t": "txt",
      "src": "  P ∗ Q ⊢ R      iff      P ⊢ Q -∗ R"
    },
    {
      "t": "note",
      "h": "<code>-∗</code> is the <b>right adjoint</b> of <code>∗</code>. That single sentence is the whole milestone. Assertions with <code>(∗, emp, -∗)</code> form a closed symmetric monoidal category — technically, a <i>BI algebra</i> — and separation logic is the internal logic of that structure. Once you know this, the laws below are not things to memorise; they are the standard consequences of an adjunction.",
      "title": "The one thing to remember",
      "kind": "key"
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "the counit",
          "h": "<code>(P -∗ Q) ∗ P ⊢ Q</code>. Every adjunction has one; here it is <code>wand_elim</code>, exercise 2. In logical dress it is modus ponens; in resource dress it is “spend the wand and its argument, receive the conclusion”."
        },
        {
          "k": "the unit",
          "h": "<code>P ⊢ Q -∗ (P ∗ Q)</code>. You get it for free by applying <code>wand_intro</code> to <code>entails_refl</code>. Read it as: owning <code>P</code> <i>entitles</i> you to a promise to produce <code>P ∗ Q</code> once someone supplies the <code>Q</code>. Only one direction, note — the converse <code>(Q -∗ (P ∗ Q)) ⊢ P</code> is false, as you can see by taking <code>Q = aFalse</code>, which makes the wand vacuously true at every heap while <code>P</code> may be false at all of them."
        },
        {
          "k": "right adjoints preserve limits",
          "h": "<code>P -∗ (aAnd Q R) ⊣⊢ aAnd (P -∗ Q) (P -∗ R)</code>, and dually the left adjoint <code>(− ∗ R)</code> preserves colimits — which is precisely <code>star_or_left</code> and <code>star_exists_left</code> from M4. Those two lemmas were not lucky; they were forced. (M4 states them in the hard direction only; the converses are just monotonicity, so nothing is being hidden.)"
        },
        {
          "k": "adjoints are monotone",
          "h": "<code>wand_mono</code>, exercise 4 — contravariant in the argument, covariant in the result. Same statement as for function types, same proof."
        },
        {
          "k": "adjoints compose",
          "h": "<code>((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R)</code>. Currying twice. Proved below in one line by applying <code>wand_intro</code> twice and reassociating."
        }
      ]
    },
    {
      "t": "p",
      "h": "The practical reading: a wand is a <b>promise that consumes resources</b>. Ordinary implication <code>Q → R</code> can be used any number of times because assumptions are free. A wand can be used once, because using it consumes the heap you fed it. That is what makes it the right tool for “I have given away part of my data structure and here is how to put it back”."
    },
    {
      "t": "h3",
      "s": "Why not ordinary implication?"
    },
    {
      "t": "p",
      "h": "This is the design decision of the chapter, so it is worth breaking the alternative rather than asserting that it fails. The obvious cheaper definition is implication evaluated in the <i>same</i> heap — no <code>∀ h'</code>, no disjointness, no union. It is shorter, it needs no lemmas from M2, and it is wrong."
    },
    {
      "t": "cmp",
      "left": {
        "t": "The naive version — same heap",
        "kind": "bad",
        "h": "<code>aImp P Q</code> holds at <code>h</code> when: <i>if</i> this very heap satisfies <code>P</code>, then it satisfies <code>Q</code>. No new resource enters, nothing is consumed. It is an ordinary implication that happens to be indexed by a heap.",
        "src": "def aImp (P Q : Assertion) : Assertion :=\n  fun σ h => P σ h → Q σ h"
      },
      "right": {
        "t": "The wand — a heap you have not been given yet",
        "kind": "good",
        "h": "<code>wand P Q</code> holds at <code>h</code> when: for <i>every</i> disjoint <code>h'</code> satisfying <code>P</code>, the union satisfies <code>Q</code>. The quantifier is what turns an implication into a promise, and the union is what makes redeeming it cost something.",
        "src": "def wand (P Q : Assertion) : Assertion :=\n  fun σ h => ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')"
      }
    },
    {
      "t": "p",
      "h": "With <code>aImp</code>, modus ponens across <code>∗</code> is <b>false</b>. Here is the witness, machine-checked against the M11 prelude:"
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "Take P = <code>0 ↦ 1</code>, Q = <code>aFalse</code>, and split the heap as <code>Heap.empty ∪ Heap.singleton 0 1</code>.",
      "src": "def aImp (P Q : Assertion) : Assertion := fun σ h => P σ h → Q σ h\n\ntheorem aImp_elim_fails : ¬ (∀ P Q : Assertion, (aImp P Q) ∗ P ⊢ Q) := by\n  intro hcontra\n  refine hcontra (0 ↦ 1) aFalse (fun _ => 0) (Heap.singleton 0 1) ?_\n  refine ⟨Heap.empty, Heap.singleton 0 1, disjoint_empty_left _,\n          (union_empty_left _).symm, ?_, rfl⟩\n  intro hp\n  have hz : Heap.empty 0 = Heap.singleton 0 1 0 := by rw [hp]\n  rw [singleton_same] at hz\n  exact absurd hz (by simp [Heap.empty])"
    },
    {
      "t": "p",
      "h": "The mechanism is worth naming, because it is the same trap every time. <code>aImp (0 ↦ 1) aFalse</code> is satisfied by the <i>empty</i> heap, <b>vacuously</b>: the empty heap does not satisfy <code>0 ↦ 1</code>, so the implication has nothing to discharge. So the left factor of the star can be empty and free, and the star as a whole tells you nothing. A same-heap implication is cheapest exactly where it should be most expensive. The <code>∀ h'</code> in <code>wand</code> closes the hole by demanding the promise hold for <i>all</i> possible arguments, including the ones you were hoping never to be given."
    },
    {
      "t": "detail",
      "title": "Reading a counterexample: <code>aImp_elim_fails</code> line by line",
      "tag": "aside",
      "open": false,
      "blocks": [
        {"t": "p", "h": "All three counterexamples in this chapter have the same shape — refute a <code>∀</code>, instantiate it at a bad heap, then grind out a contradiction about <code>Heap.empty</code> and <code>Heap.singleton</code>. Decode this one and the other two read themselves. Every state below is Lean's."},
        {"t": "steps", "items": [
          {"k": "<code>intro hcontra</code>", "h": [
            {"t": "p", "h": "The goal is <code>¬ (∀ P Q, …)</code>, and <code>¬ A</code> <i>is</i> <code>A → False</code> — not equivalent to it, definitionally equal — so <code>intro</code> applies with no unfolding tactic. (<code>intro</code> works on any goal that <i>reduces</i> to a binder, not only on goals that already look like one. The next section has the aside; this is the first of the two places in this proof where it matters, the other being <code>intro hp</code> below.)"},
            {"t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\n⊢ False"}
          ]},
          {"k": "<code>refine hcontra (0 ↦ 1) aFalse (fun _ => 0) (Heap.singleton 0 1) ?_</code>", "h": [
            {"t": "p", "h": "Four arguments before the hole: two assertions, then a store and a heap, because <code>⊢</code> unfolds to <code>∀ σ h, …</code>. The store <code>fun _ => 0</code> is arbitrary — nothing in this argument reads a program variable. What the application returns is <code>aFalse (fun _ => 0) (Heap.singleton 0 1)</code>, which reduces to <code>False</code>, so it matches the goal and only the hypothesis is left over as a hole:"},
            {"t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\n⊢ (aImp (0 ↦ 1) aFalse ∗ 0 ↦ 1) (fun x => 0) (Heap.singleton 0 1)"},
            {"t": "p", "h": "Two things to notice in that display. Lean writes the store back as <code>fun x => 0</code>, having named the ignored binder; and it needs no parentheses around the right-hand <code>0 ↦ 1</code>, because <code>↦</code> is precedence 60 and binds tighter than <code>∗</code> at 55."}
          ]},
          {"k": "<code>refine ⟨Heap.empty, Heap.singleton 0 1, …, ?_, rfl⟩</code>", "h": [
            {"t": "p", "h": "Prove that star by choosing the cut: nothing on the left, everything on the right. Slot 3 is <code>disjoint_empty_left _</code>; slot 4 is <code>(union_empty_left _).symm</code>, and the <code>.symm</code> is there because the star wants <code>h = h₁ ∪ h₂</code> while the lemma proves <code>∅ ∪ h = h</code>. Slot 6 is <code>rfl</code>, because <code>(0 ↦ 1) σ (Heap.singleton 0 1)</code> unfolds to <code>Heap.singleton 0 1 = Heap.singleton 0 1</code>. Slot 5 is the hole:"},
            {"t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\n⊢ aImp (0 ↦ 1) aFalse (fun x => 0) Heap.empty"}
          ]},
          {"k": "<code>intro hp</code>", "h": [
            {"t": "p", "h": "That hole is an implication in disguise, so <code>intro</code> walks into it too. This is the vacuity, now visible as a goal state: you are asked for <code>False</code>, and you have been handed an absurd hypothesis to make it from."},
            {"t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\nhp : (0 ↦ 1) (fun x => 0) Heap.empty\n⊢ aFalse (fun x => 0) Heap.empty"},
            {"t": "p", "h": "Lean prints <code>hp</code> folded, as <code>(0 ↦ 1) (fun x => 0) Heap.empty</code>. You may read it unfolded — it is <code>Heap.empty = Heap.singleton 0 1</code> — and you may use it as such, which is exactly what the next line does."}
          ]},
          {"k": "the last three lines", "h": [
            {"t": "p", "h": "<code>have hz : Heap.empty 0 = Heap.singleton 0 1 0 := by rw [hp]</code> is the move that turns a heap equation into a value equation: <code>rw [hp]</code> rewrites <code>Heap.empty</code> to <code>Heap.singleton 0 1</code> on the left, leaving <code>Heap.singleton 0 1 0 = Heap.singleton 0 1 0</code>, which <code>rw</code> closes by <code>rfl</code> on its own — that automatic <code>rfl</code> attempt is why the tactic block needs no second line. Then <code>rw [singleton_same] at hz</code> evaluates the right-hand side:"},
            {"t": "state", "src": "hcontra : ∀ (P Q : Assertion), aImp P Q ∗ P ⊢ Q\nhp : (0 ↦ 1) (fun x => 0) Heap.empty\nhz : Heap.empty 0 = some 1\n⊢ aFalse (fun x => 0) Heap.empty"},
            {"t": "p", "h": "<code>absurd hz (by simp [Heap.empty])</code> finishes. <code>absurd</code> takes a proof and a proof of its negation and returns anything at all, so it produces the <code>False</code> the goal wants. The <code>simp [Heap.empty]</code> proves <code>¬ (Heap.empty 0 = some 1)</code>: naming <code>Heap.empty</code> in the bracket list tells <code>simp</code> to unfold that definition to <code>fun _ => none</code>, after which the goal is <code>¬ (none = some 1)</code> and <code>simp</code> discharges it because <code>none</code> and <code>some</code> are distinct constructors."}
          ]}
        ]}
      ]
    },
    {
      "t": "h3",
      "s": "How to prove a wand, and how to use one"
    },
    {
      "t": "p",
      "h": "As with <code>∗</code> in M4, there are exactly two moves, and knowing them is most of the chapter."
    },
    {
      "t": "txt",
      "src": "  to PROVE  (P -∗ Q) σ h :\n      intro h' hd hp        -- name the incoming heap, its disjointness, and the P-fact\n      ⊢ Q σ (Heap.union h h')\n\n  to USE    hw : (P -∗ Q) σ h  against  hp : P σ h'  with  hd : Heap.disjoint h h' :\n      hw h' hd hp  :  Q σ (Heap.union h h')\n                     -- note the ORDER: heap, then disjointness, then the fact"
    },
    {
      "t": "steps",
      "title": "Proving a wand goal, in four moves",
      "items": [
        {
          "k": "Get past the entailment",
          "h": [
            {"t": "p", "h": "<code>P ⊢ Q -∗ R</code> is <code>Entails P (Q -∗ R)</code>, and <code>Entails</code> is <code>∀ σ h, P σ h → …</code>. So three <code>intro</code>s just to reach the wand. The state below is taken from <code>wand_intro</code> — that is where the spare hypothesis <code>h : P ∗ Q ⊢ R</code> comes from; it is riding along in the context and plays no part until the last line."},
            {"t": "state", "src": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ (Q -∗ R) σ hh"}
          ]
        },
        {
          "k": "Look inside",
          "h": [
            {"t": "p", "h": "The goal <i>displays</i> as <code>(Q -∗ R) σ hh</code>, which is not visibly a <code>∀</code>. It reduces to one. If you want to see it, ask — <code>show</code> costs nothing logically and makes the goal readable (M0):"},
            {"t": "code", "tag": "sketch", "src": "show ∀ h', Heap.disjoint hh h' → Q σ h' → R σ (Heap.union hh h')"},
            {"t": "state", "src": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ ∀ (h' : Heap), hh.disjoint h' → Q σ h' → R σ (hh.union h')"},
            {"t": "p", "h": "Note how Lean prints it back: <code>hh.disjoint h'</code> and <code>hh.union h'</code>, in dot notation, where the source says <code>Heap.disjoint hh h'</code> and <code>Heap.union hh h'</code>. Same terms. You will see this in every goal state below; do not go looking for a lemma that turns one into the other."}
          ]
        },
        {
          "k": "Take the three arguments",
          "h": "<code>intro h' hd hq</code>. You now hold the incoming heap, a proof it is disjoint from yours, and the antecedent — and the goal is a bare statement about the union."
        },
        {
          "k": "You are back in the model",
          "h": "The goal is <code>R σ (hh.union h')</code>, an ordinary assertion at an ordinary heap. From here it is M4 work: build whatever <code>R</code> needs out of <code>hp</code>, <code>hq</code> and <code>hd</code>. Every wand proof in this chapter has this shape, and the only step with any content is the last one."
        }
      ]
    },
    {
      "t": "detail",
      "title": "Why <code>intro</code> works on a goal that is not visibly a <code>∀</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {"t": "p", "h": "This is the one genuinely Lean-specific thing in the chapter, and it will save you a lot of confusion. <code>intro</code> does not require the goal to <i>look</i> like a function type or a <code>∀</code>. It requires the goal to <b>reduce</b> to one — Lean puts the goal in weak-head normal form first, unfolding definitions at the head until it finds a binder."},
        {"t": "p", "h": "<code>(Q -∗ R) σ hh</code> is <code>wand Q R σ hh</code>; unfolding <code>wand</code> once and applying it to <code>σ</code> and <code>hh</code> yields <code>∀ h', …</code>. So <code>intro h'</code> succeeds. The same thing happens one layer up: <code>P ⊢ Q -∗ R</code> is <code>Entails P (Q -∗ R)</code>, which unfolds to a <code>∀</code>, which is why <code>intro σ</code> works on it. In <code>wand_intro</code> a single <code>intro</code> line walks through <b>three</b> definitions — <code>Entails</code>, then an arrow, then <code>wand</code> — without comment."},
        {"t": "p", "h": "Two ways to make the unfolding visible if you want it. <code>unfold wand</code> rewrites the goal and shows the <code>∀</code>; <code>show &lt;the unfolded statement&gt;</code> does the same by asserting the definitionally-equal form. Both produce the identical goal state shown above. Neither is necessary — but when a proof of someone else's is doing something you cannot follow, inserting a <code>show</code> is usually how you find out what."},
        {"t": "p", "h": "The mirror-image fact is just as useful. A hypothesis <code>hw : (P -∗ Q) σ h</code> can be <i>applied</i> directly — <code>hw h' hd hp</code> typechecks with no unfolding tactic, because application also works up to definitional unfolding. You never need to massage a wand hypothesis before using it."}
      ]
    },
    {
      "t": "note",
      "h": "Where you meet wands in practice: <i>partial ownership</i>. If you hand out one node of a linked list to a subroutine, what remains is not a list — it is “a list with a hole”, which is exactly <code>node p x n -∗ listRep xs p</code>. Iris makes heavy use of this pattern under the name <i>magic wand as a continuation</i>.",
      "title": "Why anyone cares",
      "kind": "info"
    },
    {
      "t": "p",
      "h": "That sentence deserves to be made real, because it is the reason the connective exists. Here is the list-with-a-hole, against the <code>listRep</code> of M10:"
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "Compiled against the M11 prelude. <code>listRep_hole</code> builds the hole; <code>listRep_plug</code> fills it, and is nothing but <code>star_comm</code> followed by <code>wand_elim</code>.",
      "src": "-- you kept the tail; what you kept is a `[x] ++ xs`-list minus its head node\ntheorem listRep_hole (x : Nat) (xs : List Nat) (p n : Loc) (hp : p ≠ 0) :\n    listRep xs n ⊢ node p x n -∗ listRep (x :: xs) p := by\n  intro σ h hxs h' hd hnode\n  refine ⟨n, Heap.empty, Heap.union h h', disjoint_empty_left _,\n          (union_empty_left _).symm, ⟨hp, rfl⟩, ?_⟩\n  exact ⟨h', h, disjoint_symm hd, union_comm hd, hnode, hxs⟩\n\n-- and handing the node back reassembles the list\ntheorem listRep_plug (x : Nat) (xs : List Nat) (p n : Loc) :\n    node p x n ∗ (node p x n -∗ listRep (x :: xs) p) ⊢ listRep (x :: xs) p :=\n  entails_trans (star_comm _ _) (wand_elim _ _)"
    },
    {
      "t": "p",
      "h": "The seven-component <code>refine</code> is the only fiddly part, and it is fiddly for M10 reasons rather than M11 ones. After <code>intro σ h hxs h' hd hnode</code> the goal is <code>listRep (x :: xs) p σ (h.union h')</code>, and <code>listRep</code> at a cons unfolds to <code>aExists fun next => pure (fun _ => p ≠ 0) ∗ node p x next ∗ listRep xs next</code>. So the tuple is: the existential witness <code>n</code>; then the six components of the outer star, whose cut puts nothing on the left (<code>Heap.empty</code>) and everything on the right (<code>Heap.union h h'</code>), with <code>⟨hp, rfl⟩</code> discharging the <code>pure</code> — <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so it wants the fact <code>p ≠ 0</code> and the proof that its heap is empty; and finally the hole. What the hole leaves is <code>(node p x n ∗ listRep xs n) σ (h.union h')</code>, and the last line cuts it as <code>⟨h', h⟩</code> — the node's heap first — which is why <code>union_comm hd</code> appears in slot four. That is the one place in this proof where you pay for the definition's left-to-right convention."
    },
    {
      "t": "p",
      "h": "Read <code>listRep_hole</code>'s statement as an accounting identity. You own the tail. You do <b>not</b> own the head node — you lent it out. What you can still say about yourself is: “give me back a <code>node p x n</code> and I am a <code>listRep (x :: xs) p</code>”. That is the general shape of a list-traversal loop invariant: carry the part you have walked past as a promise to reassemble it, and cash the promise in when the walk ends. Worth being precise about where this does and does not get used downstream. M13's traversal capstone does <i>not</i> take this route — it carries the visited prefix as an <code>lseg</code> and closes with <code>lseg_listRep</code> — and it can afford not to, because for a linked list the hole happens to be shaped like another segment, so a named predicate exists for it. The wand is what you reach for when no such predicate exists: a tree with one subtree lent out, a record with one field in someone else's hands, any remainder that has no name of its own. That is the situation a general-purpose system is in almost all the time, which is why wands are everywhere in Iris and only occasionally here."
    },
    {
      "t": "sec",
      "s": "Exercises"
    },
    {
      "t": "ex",
      "id": "m11-1",
      "name": "wand_intro",
      "hard": false,
      "why": "Currying. Half of the adjunction — and the half you will actually use, because it is how every wand ever gets built. You never construct a wand by exhibiting a heap and verifying the definition by hand; you construct it by naming the entailment it curries. <code>listRep_hole</code> above is this move with <code>P</code> = the tail, <code>Q</code> = the node, <code>R</code> = the whole list.",
      "setup": "In scope: everything from M4 (<code>star</code> and its laws) and the definition of <code>wand</code> above. You need no lemma at all — this is pure definition-chasing, and that is the point: it shows that the adjunction is built into the definition rather than proved about it.",
      "goal": "theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R",
      "hints": [
        "Do not think yet — count. <code>Entails</code> unfolds to a <code>∀</code> over the store and the heap followed by an arrow; <code>wand</code> unfolds to a <code>∀</code> over the incoming heap followed by two arrows. How many names can <code>intro</code> absorb before the goal stops being a function type?",
        "Six: <code>intro σ hh hp h' hd hq</code>. If you do not believe <code>intro</code> can walk through <code>wand</code>, insert <code>show ∀ h', Heap.disjoint hh h' → Q σ h' → R σ (Heap.union hh h')</code> after the first three and watch nothing change.",
        "Now compare what you have with what you want. The goal is <code>R σ (hh.union h')</code>. The hypothesis <code>h : P ∗ Q ⊢ R</code> is <code>∀ σ h, (P ∗ Q) σ h → R σ h</code> — so apply it at the store <code>σ</code> and the heap <code>Heap.union hh h'</code>, and it will hand you the goal in exchange for one thing.",
        "That one thing is <code>(P ∗ Q) σ (Heap.union hh h')</code>. Proving a star means choosing the cut (M4) — and you are not being asked to choose anything, because the cut is already sitting in front of you.",
        "Given a heap <code>hh</code> satisfying <code>P</code> and a disjoint <code>h'</code> satisfying <code>Q</code>, feed the pair to <code>h</code> as a star with cut <code>⟨hh, h'⟩</code> and equation <code>rfl</code>."
      ],
      "sol": "theorem wand_intro {P Q R : Assertion} (h : P ∗ Q ⊢ R) : P ⊢ Q -∗ R := by\n  intro σ hh hp h' hd hq\n  exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
      "expl": "The heap equation is <code>rfl</code> because the goal’s heap <i>is</i> <code>Heap.union hh h'</code> — the wand’s definition puts it there. This is the cleanest possible instance of “choose the cut and everything follows”. Two lines, and the second one is a single term: <code>intro</code> hands you all four ingredients of a star (two heaps, their disjointness, and the two facts), and the fifth ingredient — the heap equation — is free.",
      "walk": [
        {
          "tac": "intro σ hh hp h' hd hq",
          "h": "Six introductions through three layers of definition, with no tactic in between. <code>σ</code> and <code>hh</code> and <code>hp</code> come from <code>Entails</code>; <code>h'</code>, <code>hd</code> and <code>hq</code> come from <code>wand</code>. Read them as: the store, the heap you own, your proof of <code>P</code> about it, the heap you are handed, its disjointness from yours, and its proof of <code>Q</code>. The goal left over is <code>R σ (hh.union h')</code> — an ordinary assertion at an ordinary heap."
        },
        {
          "tac": "exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
          "h": "<code>h σ (Heap.union hh h')</code> specialises the entailment to this store and this heap, leaving a function that wants <code>(P ∗ Q) σ (Heap.union hh h')</code>. The <code>⟨…⟩</code> supplies it: left piece <code>hh</code>, right piece <code>h'</code>, disjointness <code>hd</code>, heap equation <code>rfl</code>, then <code>hp : P σ hh</code> and <code>hq : Q σ h'</code>. Six components, because <code>star</code>'s body is <code>∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code> — two existentials and a four-way conjunction, 2 + 4 = 6 — and the anonymous constructor flattens nested structure (M0): <code>⟨a, b, c, d, e, f⟩</code> means <code>⟨a, ⟨b, ⟨c, ⟨d, ⟨e, f⟩⟩⟩⟩⟩</code>. If you ever lose count, the reliable move is to write <code>refine … ⟨?_, ?_, ?_, ?_, ?_, ?_⟩</code> and read the goals back: the first two come out as bare <code>⊢ Heap</code>, and the remaining four are stated in terms of them, as <code>⊢ Heap.disjoint ?refine_1 ?refine_2</code>, <code>⊢ hh.union h' = Heap.union ?refine_1 ?refine_2</code>, <code>⊢ P σ ?refine_1</code>, <code>⊢ Q σ ?refine_2</code>. That is the anatomy of the tuple, printed by Lean rather than remembered."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "wand_intro, one <code>intro</code> at a time",
          "start": "P Q R : Assertion\nh : P ∗ Q ⊢ R\n⊢ P ⊢ Q -∗ R",
          "steps": [
            {
              "tac": "intro σ",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\n⊢ ∀ (h : Heap), P σ h → (Q -∗ R) σ h",
              "h": "<code>Entails</code> has unfolded. Notice that Lean names the bound heap <code>h</code> in the display even though <code>h</code> is already taken by the hypothesis — the binder is not yet in the context, so there is no clash. This is why the solution introduces it as <code>hh</code>."
            },
            {
              "tac": "intro hh",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\n⊢ P σ hh → (Q -∗ R) σ hh",
              "h": "An ordinary arrow now. Nothing exotic yet."
            },
            {
              "tac": "intro hp",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\n⊢ (Q -∗ R) σ hh",
              "h": "This is the moment worth staring at. The goal is not a <code>∀</code>, not an arrow, not a conjunction — it is an application of a defined constant. Most tactics would stop here. <code>intro</code> does not."
            },
            {
              "tac": "intro h'",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\n⊢ hh.disjoint h' → Q σ h' → R σ (hh.union h')",
              "h": "<code>wand</code> unfolded silently and its <code>∀ h'</code> was consumed. What is left is exactly the tail of the definition, printed in dot notation: <code>hh.disjoint h'</code> is <code>Heap.disjoint hh h'</code> and <code>hh.union h'</code> is <code>Heap.union hh h'</code>."
            },
            {
              "tac": "intro hd",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\nhd : hh.disjoint h'\n⊢ Q σ h' → R σ (hh.union h')",
              "h": "Disjointness is now a hypothesis you hold. It is the ingredient the star in the next line will demand, and it arrived for free."
            },
            {
              "tac": "intro hq",
              "state": "P Q R : Assertion\nh : P ∗ Q ⊢ R\nσ : Store\nhh : Heap\nhp : P σ hh\nh' : Heap\nhd : hh.disjoint h'\nhq : Q σ h'\n⊢ R σ (hh.union h')",
              "h": "The end of the road for <code>intro</code>. Read the context bottom-up and you have literally the contents of a star: two heaps, a disjointness proof, a <code>P</code> and a <code>Q</code>."
            },
            {
              "tac": "exact h σ (Heap.union hh h') ⟨hh, h', hd, rfl, hp, hq⟩",
              "h": "Assemble the star at the heap the goal is already about, and apply the hypothesis."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "What makes the equation <code>rfl</code>",
            "kind": "good",
            "h": "The star wants <code>Heap.union hh h' = Heap.union hh h'</code>. Both sides are the <i>same term</i>, because the wand's definition chose the goal's heap to be <code>Heap.union hh h'</code> in the first place. So <code>rfl</code> — the proof that a term equals itself — is enough, with no computation."
          },
          "right": {
            "t": "Where it would not be",
            "h": "Curry in the other order — hypothesis <code>Q ∗ P ⊢ R</code> instead of <code>P ∗ Q ⊢ R</code> — and the cut has to be <code>⟨h', hh⟩</code>, so the equation becomes <code>Heap.union hh h' = Heap.union h' hh</code>. That is <i>not</i> <code>rfl</code>: <code>Heap.union</code> is left-biased and only commutes given disjointness. You must pass <code>union_comm hd</code>.",
            "src": "theorem wand_intro_flip {P Q R : Assertion} (h : Q ∗ P ⊢ R) : P ⊢ Q -∗ R := by\n  intro σ hh hp h' hd hq\n  exact h σ (Heap.union hh h') ⟨h', hh, disjoint_symm hd, union_comm hd, hq, hp⟩"
          }
        },
        {
          "t": "p",
          "h": "That contrast is the whole reason the definition puts <code>Heap.union h h'</code> and not <code>Heap.union h' h</code> in the conclusion. It is a convention, and the convention is chosen so that <code>wand_intro</code> — the lemma you will use hundreds of times — costs nothing. The right-hand column above is what you would pay every single time under the other convention."
        }
      ],
      "pitfall": "Ordering the anonymous constructor by <i>recency</i> rather than by the statement. <code>h'</code> is the heap you were just handed, so it feels like the natural first component; but the star you must supply is <code>(P ∗ Q) σ …</code>, and <code>P</code> lives in <code>hh</code>. Writing <code>⟨h', hh, hd, rfl, hp, hq⟩</code> produces three errors at once, and they are worth learning to read: <code>The argument hd has type hh.disjoint h' but is expected to have type h'.disjoint hh</code>, the same for <code>hp</code>, and <code>rfl has type ?m = ?m but is expected to have type hh.union h' = h'.union hh</code>. <b>Three simultaneous mismatches inside one <code>⟨…⟩</code> almost always means the components are in the wrong order, not that they are the wrong components.</b>",
      "variants": "Delete <code>Heap.disjoint h h'</code> from the definition of <code>wand</code> and this proof breaks immediately: <code>hd</code> is the third slot of the star, and with the clause gone there is nothing to put there — the incoming heap might overlap yours, so <code>hh</code> and <code>h'</code> need not be a legal cut of anything. The disjointness clause is not decoration; it is the star's disjointness obligation, pre-paid. Reverse the hypothesis to <code>Q ∗ P ⊢ R</code> and the theorem stays true but the proof gains two lemma applications (see the comparison above). Reverse the <i>conclusion</i> to <code>Q ⊢ P -∗ R</code> and it is still true — but, and this is worth checking rather than assuming, <b>not</b> by the same proof with <code>hp</code> and <code>hq</code> swapped. Swapping alone gives two errors, on <code>hd</code> and on <code>rfl</code>, because the cut is now <code>⟨h', hh⟩</code> and so you owe <code>h'.disjoint hh</code> and <code>hh.union h' = h'.union hh</code>. The proof that works is <code>exact h σ (Heap.union hh h') ⟨h', hh, disjoint_symm hd, union_comm hd, hp, hq⟩</code> — the same two lemma applications as <code>wand_intro_flip</code> above, for the same reason. <code>∗</code> is commutative, so which side you curry is a free choice; it is just never a free <i>proof</i>."
    },
    {
      "t": "ex",
      "id": "m11-2",
      "name": "wand_elim",
      "hard": false,
      "why": "Uncurrying, i.e. <i>modus ponens for resources</i>. Note that the wand and its argument must be in disjoint heaps — you cannot apply a wand to memory you have already spent. This is the <b>counit</b> of the adjunction, and in the next exercise it is the only thing the backward direction needs.",
      "setup": "You are given a star hypothesis and asked for a bare assertion. Everything you need is inside the star; no M2 lemma is required, and no heap is constructed.",
      "goal": "theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q",
      "hints": [
        "The hypothesis is a star, and there is exactly one thing you ever do with a star hypothesis (M4): take it apart into <code>⟨h₁, h₂, hd, hu, hw, hp⟩</code>. You can do that directly in the <code>intro</code> pattern rather than with a separate <code>obtain</code>.",
        "Now read what you hold: <code>hw : (P -∗ Q) σ h₁</code>, <code>hp : P σ h₂</code>, <code>hd : h₁.disjoint h₂</code>. Applying the wand is <code>hw h₂ hd hp</code> — heap, then disjointness, then the fact, in the order the definition binds them.",
        "That expression has type <code>Q σ (h₁.union h₂)</code>. Your goal says <code>Q σ h</code>. Those are not the same term, even though <code>hu : h = h₁.union h₂</code> is sitting in the context. Fix the goal before you try to close it.",
        "Destructure the star and apply the wand to the second piece."
      ],
      "sol": "theorem wand_elim (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by\n  intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩\n  rw [hu]\n  exact hw h₂ hd hp",
      "expl": "<code>rw [hu]</code> turns the goal’s heap into <code>Heap.union h₁ h₂</code>, which is precisely the shape the wand produces. One line of content. Everything else is bookkeeping: the star hands you a cut and a disjointness proof, and the wand was defined to accept exactly those.",
      "walk": [
        {
          "tac": "intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩",
          "h": "Three <code>intro</code>s, the third of which is a destructuring pattern rather than a name — <code>intro</code> accepts an anonymous-constructor pattern wherever it accepts an identifier, and it takes the hypothesis apart on the way in. The pattern flattens <code>star</code>'s body — <code>∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>, two existentials and a four-way conjunction — into six names: the two pieces, their disjointness, the equation <code>h = h₁ ∪ h₂</code>, and one fact per piece. Note <code>hw</code> lands on <code>h₁</code> and <code>hp</code> on <code>h₂</code> — the order in which they appear in <code>(P -∗ Q) ∗ P</code>."
        },
        {
          "tac": "rw [hu]",
          "h": "Rewrites <code>h</code> to <code>h₁.union h₂</code> everywhere in the goal, turning <code>Q σ h</code> into <code>Q σ (h₁.union h₂)</code>. This is the only step with a choice in it, and it is forced: the wand can only produce a statement about a union, so the goal has to be put in that shape first."
        },
        {
          "tac": "exact hw h₂ hd hp",
          "h": "Apply the wand. Three arguments in the order the definition binds them — the heap being contributed, the proof it is disjoint from the wand's own heap, and the proof it satisfies the antecedent. The result is <code>Q σ (h₁.union h₂)</code>, which is now literally the goal."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "wand_elim, tactic by tactic",
          "start": "P Q : Assertion\n⊢ (P -∗ Q) ∗ P ⊢ Q",
          "steps": [
            {
              "tac": "intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩",
              "state": "P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhw : (P -∗ Q) σ h₁\nhp : P σ h₂\n⊢ Q σ h",
              "h": "Lean collapses <code>h</code>, <code>h₁</code>, <code>h₂</code> onto one line because they share a type. The hypotheses are exactly the six components of the pattern, in order. Everything needed is present; the only problem is that the goal mentions <code>h</code> and the tools mention <code>h₁.union h₂</code>."
            },
            {
              "tac": "rw [hu]",
              "state": "P Q : Assertion\nσ : Store\nh h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhu : h = h₁.union h₂\nhw : (P -∗ Q) σ h₁\nhp : P σ h₂\n⊢ Q σ (h₁.union h₂)",
              "h": "Only the goal changed. <code>rw</code> rewrites left-to-right, and <code>hu</code> points from <code>h</code> to the union, which is the direction you want. (Had the star been defined with the equation the other way round, this line would be <code>rw [← hu]</code>.)"
            },
            {
              "tac": "exact hw h₂ hd hp",
              "h": "Exact match."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "<code>rw [hu]</code> versus <code>subst hu</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {"t": "p", "h": "<code>subst hu</code> also works here, and does slightly more: it eliminates <code>h</code> from the context entirely, replacing every occurrence with <code>h₁.union h₂</code> and deleting both <code>h</code> and <code>hu</code>. <code>rw [hu]</code> only touches the goal and leaves the hypothesis behind."},
            {"t": "code", "tag": "illustration", "src": "theorem wand_elim_by_subst (P Q : Assertion) : (P -∗ Q) ∗ P ⊢ Q := by\n  intro σ h ⟨h₁, h₂, hd, hu, hw, hp⟩\n  subst hu\n  exact hw h₂ hd hp"},
            {"t": "p", "h": "<code>subst</code> requires one side of the equation to be a local variable that nothing else depends on — <code>h</code> qualifies. When it applies it is usually the better move, which is why M4's <code>star_assoc_left</code> uses it. Here the two are interchangeable, and the workbook's proof uses <code>rw</code> because it makes the trace above easier to read: you can see the goal change and nothing else."}
          ]
        },
        {
          "t": "p",
          "h": "One further thing to notice: <code>hd : h₁.disjoint h₂</code> arrives from the star with exactly the orientation the wand wants — the wand's heap first, the contributed heap second. That is not luck. Both <code>star</code> and <code>wand</code> put the owned heap on the left, and the two definitions were written to line up. Reverse either convention and this proof needs a <code>disjoint_symm</code>."
        }
      ],
      "pitfall": "Skipping <code>rw [hu]</code> and going straight to <code>exact hw h₂ hd hp</code>, on the grounds that <code>hu</code> is in the context so Lean surely knows. It does not. The error is <code>Type mismatch: hw h₂ hd hp has type Q σ (h₁.union h₂) but is expected to have type Q σ h</code>. <code>h</code> is an opaque local variable; <code>Q σ h</code> and <code>Q σ (h₁.union h₂)</code> are equal only <i>given</i> <code>hu</code>, and giving it is your job. This is the single most common failure in the whole chapter, and the fix is always the same: rewrite the goal into union form before applying anything.",
      "variants": "Weaken <code>∗</code> to <code>∧</code> and the theorem becomes <b>false</b>: <code>aAnd (P -∗ Q) P ⊢ Q</code> has a counterexample, given at the end of this chapter. The reason is exactly the one in the <code>why</code> above — with <code>∧</code>, the wand and its argument live in the <i>same</i> heap, so the disjointness the wand demands is unavailable and the promise can never be redeemed. Swap the factors to <code>P ∗ (P -∗ Q) ⊢ Q</code> and it stays true, but the proof needs a step: <code>entails_trans (star_comm P (P -∗ Q)) (wand_elim P Q)</code>. Drop the antecedent entirely — <code>(P -∗ Q) ⊢ Q</code> — and it is false for the obvious reason: you are holding a promise and nothing to pay for it."
    },
    {
      "t": "ex",
      "id": "m11-3",
      "name": "star_wand_adjunction",
      "hard": false,
      "why": "The adjunction itself. Prove the ⟸ direction <i>from</i> the two previous lemmas rather than from scratch — that is the whole point of having them. Once this is on the shelf, every later wand law is a two-line rearrangement instead of a semantic argument about heaps, and the last section of this chapter is three worked examples of that.",
      "setup": "You may use <code>wand_intro</code> and <code>wand_elim</code> from the previous two exercises, plus <code>star_mono_left</code> and <code>entails_trans</code> from M4. Do not <code>intro σ h</code> anywhere — if you find yourself naming a heap, you are proving it the wrong way.",
      "goal": "theorem star_wand_adjunction (P Q R : Assertion) :\n    (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R)",
      "hints": [
        "Start with <code>constructor</code>, which splits an <code>↔</code> into its two implications. Lean names them <code>case mp</code> and <code>case mpr</code> — <i>modus ponens</i> and its reverse — in the order they appear in the <code>↔</code>. So <code>mp</code> is left-to-right: <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>. Address them with <code>·</code> bullets, in that order.",
        "The <code>mp</code> goal is <code>wand_intro</code>'s type with the implicit arguments instantiated. You do not need <code>intro</code> and you do not need to apply it to anything: <code>exact wand_intro</code>, bare.",
        "For <code>mpr</code>: <code>intro h</code> gives you <code>h : P ⊢ Q -∗ R</code> with goal <code>P ∗ Q ⊢ R</code>. You want to get from <code>P ∗ Q</code> to something <code>wand_elim</code> recognises. What does <code>wand_elim Q R</code> take as its left-hand side?",
        "<code>(Q -∗ R) ∗ Q</code>. So improve the left factor of <code>P ∗ Q</code> using <code>h</code>, leaving the right factor alone — that is <code>star_mono_left Q h</code>, whose explicit argument is the factor being <i>kept</i>. Then chain the two entailments with <code>entails_trans</code>.",
        "⟹ is <code>wand_intro</code>. For ⟸: from <code>P ⊢ Q -∗ R</code>, monotonicity gives <code>P ∗ Q ⊢ (Q -∗ R) ∗ Q</code>, and then <code>wand_elim</code> finishes."
      ],
      "sol": "theorem star_wand_adjunction (P Q R : Assertion) : (P ∗ Q ⊢ R) ↔ (P ⊢ Q -∗ R) := by\n  constructor\n  · exact wand_intro\n  · intro h\n    refine entails_trans (star_mono_left Q h) ?_\n    exact wand_elim Q R",
      "expl": "The backward direction is two lemma applications composed with <code>entails_trans</code>. In categorical language you have just verified that <code>(− ∗ Q)</code> is left adjoint to <code>(Q -∗ −)</code>, with <code>wand_elim</code> as the counit. Note what is <i>not</i> in this proof: no <code>σ</code>, no heap, no <code>Heap.union</code>, no disjointness. That is the sign that you have stopped working in the model and started working in the logic.",
      "walk": [
        {
          "tac": "constructor",
          "h": "Splits the <code>↔</code> into two goals, <code>case mp</code> (left-to-right) and <code>case mpr</code> (right-to-left). <code>Iff</code> is a structure with two fields, so <code>constructor</code> is just “build the pair”, and the two fields become the two goals."
        },
        {
          "tac": "· exact wand_intro",
          "h": "The bullet <code>·</code> focuses the first goal. The goal is <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>, and <code>wand_intro</code> is a term of type <code>∀ {P Q R}, P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>. Lean instantiates the three implicit arguments by unification and the two types are identical. No <code>intro</code>, no application."
        },
        {
          "tac": "· intro h",
          "h": "The second bullet. Here <code>intro</code> genuinely does something — the goal is an implication between two entailments, and <code>h : P ⊢ Q -∗ R</code> becomes a hypothesis, leaving <code>P ∗ Q ⊢ R</code>."
        },
        {
          "tac": "refine entails_trans (star_mono_left Q h) ?_",
          "h": "<code>entails_trans</code> composes two entailments through an unnamed middle assertion. Supplying the first factor determines the middle: <code>star_mono_left Q h : P ∗ Q ⊢ (Q -∗ R) ∗ Q</code>, so the hole <code>?_</code> must be <code>(Q -∗ R) ∗ Q ⊢ R</code>. <code>refine</code> rather than <code>exact</code> precisely because of that hole (M4)."
        },
        {
          "tac": "exact wand_elim Q R",
          "h": "Which is the previous exercise, instantiated. The two explicit arguments are the wand's antecedent and conclusion, in that order."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "star_wand_adjunction, tactic by tactic",
          "start": "P Q R : Assertion\n⊢ P ∗ Q ⊢ R ↔ P ⊢ Q -∗ R",
          "steps": [
            {
              "tac": "constructor",
              "state": "case mp\nP Q R : Assertion\n⊢ P ∗ Q ⊢ R → P ⊢ Q -∗ R\n\ncase mpr\nP Q R : Assertion\n⊢ P ⊢ Q -∗ R → P ∗ Q ⊢ R",
              "h": "Two goals, tagged with the field names of <code>Iff</code>. Notice how little bracketing the printed goals need: <code>⊢</code> at precedence 40 is looser than <code>→</code>, so <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code> really does mean <code>(P ∗ Q ⊢ R) → (P ⊢ Q -∗ R)</code>."
            },
            {
              "tac": "· exact wand_intro",
              "h": "First goal closed by a bare lemma name. Nothing to show — the state after this is simply the second goal."
            },
            {
              "tac": "· intro h",
              "state": "case mpr\nP Q R : Assertion\nh : P ⊢ Q -∗ R\n⊢ P ∗ Q ⊢ R",
              "h": "The case tag survives into the focused goal, which is how you can tell at a glance which half you are in."
            },
            {
              "tac": "refine entails_trans (star_mono_left Q h) ?_",
              "state": "case mpr\nP Q R : Assertion\nh : P ⊢ Q -∗ R\n⊢ (Q -∗ R) ∗ Q ⊢ R",
              "h": "The middle assertion has been chosen for you by the first argument. What remains is <code>wand_elim</code> verbatim — which is the payoff: the second exercise was designed to be exactly the hole this first step leaves."
            },
            {
              "tac": "exact wand_elim Q R",
              "h": "Done."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "Proving ⟸ from the algebra",
            "kind": "good",
            "h": "Two lemma applications and a composition. No heap ever appears. If you later change the <i>model</i> of heaps — partial maps to fractional permissions, say — this proof does not move.",
            "src": "intro h\nrefine entails_trans (star_mono_left Q h) ?_\nexact wand_elim Q R"
          },
          "right": {
            "t": "Proving ⟸ from the model",
            "h": "Also short — but it reaches past the two lemmas into the definitions of <code>star</code> and <code>wand</code>, and it is tied to this particular representation of heaps. It compiles; it is just the wrong habit.",
            "src": "theorem adjunction_mpr_by_hand (P Q R : Assertion) (h : P ⊢ Q -∗ R) :\n    P ∗ Q ⊢ R := by\n  intro σ hh ⟨h₁, h₂, hd, hu, hp, hq⟩\n  rw [hu]\n  exact h σ h₁ hp h₂ hd hq"
          }
        },
        {
          "t": "detail",
          "title": "Why <code>exact wand_intro</code> works with no arguments",
          "tag": "aside",
          "open": false,
          "blocks": [
            {"t": "p", "h": "<code>wand_intro</code>'s full type, as Lean prints it for <code>#check @wand_intro</code>, is <code>∀ {P Q R : Assertion}, P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>. With the implicits left to be inferred, the term <code>wand_intro</code> <i>is</i> a function from one entailment to another. The <code>mp</code> goal is a function from one entailment to another. They unify, and unification fixes <code>P</code>, <code>Q</code>, <code>R</code>."},
            {"t": "p", "h": "Beginners usually write <code>intro hh</code> followed by <code>exact wand_intro hh</code>, which also compiles and is not wrong. The point-free version is shorter and, more importantly, makes visible that <code>mp</code> is not a new fact — it is the previous exercise wearing different brackets."},
            {"t": "p", "h": "You can see this from the failure mode too. Put the bullets in the wrong order and Lean shows you the metavariables directly: <code>wand_intro has type ?m.14 ∗ ?m.15 ⊢ ?m.16 → ?m.14 ⊢ ?m.15 -∗ ?m.16 but is expected to have type P ⊢ Q -∗ R → P ∗ Q ⊢ R</code>. The numbers will differ in your session and mean nothing; what carries information is that <code>?m.14</code> occurs on <i>both</i> sides of the arrow, and likewise <code>?m.15</code> and <code>?m.16</code>. Those three are the unsolved implicit arguments, and the repetition is the shape unification was trying to match. It could not, because the arrow points the other way."}
          ]
        }
      ],
      "pitfall": "Getting the two bullets the wrong way round. <code>constructor</code> produces <code>mp</code> first, and <code>mp</code> is the direction written first inside the <code>↔</code> — here <code>P ∗ Q ⊢ R → P ⊢ Q -∗ R</code>, the <code>wand_intro</code> direction. If you put the <code>entails_trans</code> proof first, you get two errors, the informative one being <code>Type mismatch: wand_intro has type ?m.14 ∗ ?m.15 ⊢ ?m.16 → ?m.14 ⊢ ?m.15 -∗ ?m.16 but is expected to have type P ⊢ Q -∗ R → P ∗ Q ⊢ R</code>. A second, subtler slip: <code>star_mono_left</code>'s explicit argument is the factor you are <i>keeping</i>, not the one you are improving — write <code>star_mono_right</code> and you get <code>star_mono_right Q h has type Q ∗ P ⊢ Q ∗ (Q -∗ R)</code>, with the factors on the wrong sides.",
      "variants": "The <code>↔</code> here is an equivalence of <i>provability</i>, at the meta level — it says two <code>Prop</code>s about entailment are equivalent. It is not an assertion-level <code>⊣⊢</code>, and there is no assertion whose truth it expresses; that distinction is why the statement lives in <code>Prop</code> and not in <code>Assertion</code>. Replace <code>∗</code> by <code>∧</code> and <code>-∗</code> by the naive <code>aImp</code> and the theorem is <b>still true</b>, both directions, by an easy argument — that is not a defect, it is the point. BI has <i>two</i> conjunctions and <i>two</i> implications, and they pair off: <code>∧ ⊣ aImp</code> and <code>∗ ⊣ -∗</code>. What breaks is <b>crossing the pairing</b>, and the two counterexamples in this chapter are exactly the two crossed counits: <code>aImp_elim_fails</code> kills <code>(aImp P Q) ∗ P ⊢ Q</code>, and <code>wand_and_elim_fails</code> kills <code>aAnd (P -∗ Q) P ⊢ Q</code>. Note also how little each direction consumes. ⟹ uses no lemma at all: it is <code>wand_intro</code>, which is definition-chasing. ⟸ uses exactly one, <code>star_mono_left</code>. So with <code>wand</code> defined as it is above, the adjunction rests on nothing but monotonicity of <code>∗</code> in its left argument — no associativity, no commutativity, no unit."
    },
    {
      "t": "ex",
      "id": "m11-4",
      "name": "wand_mono",
      "hard": false,
      "why": "Contravariant on the left, covariant on the right — exactly like a function type, and for exactly the same reason. This is the lemma that lets you weaken a wand you are holding: strengthen what you promise to accept, or weaken what you promise to deliver, without ever unfolding the definition again.",
      "setup": "Two entailments in, one entailment out. As in <code>wand_intro</code>, <code>intro</code> does all the structural work; the single remaining line is a composition of three functions.",
      "goal": "theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q')",
      "hints": [
        "Same opening as <code>wand_intro</code>: <code>intro</code> until the goal is a bare assertion at a union. Six names again — three from <code>Entails</code>, three from the <code>P' -∗ Q'</code> you are constructing.",
        "You now hold <code>hw : (P -∗ Q) σ h</code>, <code>hd : h.disjoint h'</code> and <code>hp' : P' σ h'</code>, and the goal is <code>Q' σ (h.union h')</code>. The wand wants a <code>P</code> at <code>h'</code>; you have a <code>P'</code>. Convert.",
        "<code>hp σ h' hp' : P σ h'</code>. Feed that to the wand: <code>hw h' hd (hp σ h' hp') : Q σ (h.union h')</code>. One more conversion to go, and it is the same trick with <code>hq</code>.",
        "Compose: turn the given <code>P'</code>-heap into a <code>P</code>-heap with <code>hp</code>, apply the wand, then push the result along <code>hq</code>."
      ],
      "sol": "theorem wand_mono {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q') := by\n  intro σ h hw h' hd hp'\n  exact hq σ _ (hw h' hd (hp σ h' hp'))",
      "expl": "If this variance surprises you, look at the definition: <code>P</code> occurs to the left of an arrow, <code>Q</code> to the right. Everything else follows. The proof is a three-fold composition read right to left — convert the incoming fact along <code>hp</code>, run it through the wand, convert the result along <code>hq</code> — which is precisely the term you would write for <code>(f ∘ −) ∘ (− ∘ g)</code> on function types.",
      "walk": [
        {
          "tac": "intro σ h hw h' hd hp'",
          "h": "Six again, and worth pausing on which definition each comes from: <code>σ</code>, <code>h</code>, <code>hw</code> from <code>Entails</code> — so <code>hw</code> is the wand you are being handed — and <code>h'</code>, <code>hd</code>, <code>hp'</code> from the wand you are being asked to produce. The goal is <code>Q' σ (h.union h')</code>."
        },
        {
          "tac": "exact hq σ _ (hw h' hd (hp σ h' hp'))",
          "h": "Innermost first: <code>hp σ h' hp'</code> upgrades <code>hp' : P' σ h'</code> to <code>P σ h'</code>, which is what the wand demands. Then <code>hw h' hd (…)</code> redeems the wand and yields <code>Q σ (h.union h')</code>. Finally <code>hq σ _ (…)</code> pushes that to <code>Q' σ (h.union h')</code>. The <code>_</code> is the heap argument of <code>hq</code>, left for Lean to infer — it can only be <code>Heap.union h h'</code>, because that is the heap of the term being passed in."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "wand_mono, with the <code>intro</code> split in two so you can see the halfway point",
          "start": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\n⊢ P -∗ Q ⊢ P' -∗ Q'",
          "steps": [
            {
              "tac": "intro σ h hw",
              "state": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\nσ : Store\nh : Heap\nhw : (P -∗ Q) σ h\n⊢ (P' -∗ Q') σ h",
              "h": "The halfway state, and the clearest statement of what the theorem says: <i>the same heap</i> <code>h</code> that satisfies the old wand must be shown to satisfy the new one. No resource is created or destroyed by weakening a wand."
            },
            {
              "tac": "intro h' hd hp'",
              "state": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\nσ : Store\nh : Heap\nhw : (P -∗ Q) σ h\nh' : Heap\nhd : h.disjoint h'\nhp' : P' σ h'\n⊢ Q' σ (h.union h')",
              "h": "Now the variance is visible in the context rather than asserted. <code>hp'</code> is a <code>P'</code>-fact and points <i>into</i> the proof — so <code>hp</code> must run from <code>P'</code> to <code>P</code>. The goal is a <code>Q'</code>-fact and points <i>out</i> — so <code>hq</code> must run from <code>Q</code> to <code>Q'</code>. Contravariant left, covariant right, read straight off the goal state."
            },
            {
              "tac": "exact hq σ _ (hw h' hd (hp σ h' hp'))",
              "h": "The three-fold composition."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "What the <code>_</code> is, and how to make it visible",
          "tag": "aside",
          "open": false,
          "blocks": [
            {"t": "p", "h": "<code>hq : Q ⊢ Q'</code> unfolds to <code>∀ σ h, Q σ h → Q' σ h</code>, so it takes a store, a heap, and a fact. The heap is written <code>_</code> because it is determined by the third argument: <code>hw h' hd (…)</code> has type <code>Q σ (h.union h')</code>, so the heap must be <code>Heap.union h h'</code>. Lean solves that by unification and you never have to type it."},
            {"t": "p", "h": "If you want to see it rather than trust it, name the intermediate result. This version compiles and shows the middle type explicitly:"},
            {"t": "code", "tag": "illustration", "src": "theorem wand_mono_explicit {P P' Q Q' : Assertion} (hp : P' ⊢ P) (hq : Q ⊢ Q') :\n    (P -∗ Q) ⊢ (P' -∗ Q') := by\n  intro σ h hw h' hd hp'\n  have step : Q σ (Heap.union h h') := hw h' hd (hp σ h' hp')\n  exact hq σ _ step"},
            {"t": "state", "src": "P P' Q Q' : Assertion\nhp : P' ⊢ P\nhq : Q ⊢ Q'\nσ : Store\nh : Heap\nhw : (P -∗ Q) σ h\nh' : Heap\nhd : h.disjoint h'\nhp' : P' σ h'\nstep : Q σ (h.union h')\n⊢ Q' σ (h.union h')"},
            {"t": "p", "h": "With <code>step</code> in the context, the last line is visibly nothing but an application of <code>hq</code> at one point. Writing <code>hq σ h step</code> instead — the naive guess — fails with <code>Application type mismatch: The argument step has type Q σ (h.union h') but is expected to have type Q σ h</code>, which is the same lesson as <code>wand_elim</code>'s pitfall in a new costume. Note that the error names <code>step</code>. Make the same mistake in the one-line version and Lean has no name to use, so it prints the whole term — <code>The argument hw h' hd (hp σ h' hp') has type …</code> — which is the identical mismatch wearing a much worse label. That is the everyday argument for <code>have</code>: not that it changes the proof, but that it changes the error message."}
          ]
        },
        {
          "t": "p",
          "h": "Finally, the variance is not a stylistic choice — get it backwards and the statement is false. Here is the witness, so that “contravariant on the left” is something you have seen fail rather than something you have been told:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "cap": "<code>P = 0 ↦ 1</code>, <code>P' = aTrue</code>, <code>Q = 0 ↦ 1</code>, at the empty heap. The empty heap does hold <code>(0 ↦ 1) -∗ (0 ↦ 1)</code>; it does not hold <code>aTrue -∗ (0 ↦ 1)</code>, because feeding that wand the empty heap would demand <code>Heap.empty = Heap.singleton 0 1</code>. Two pieces of syntax here are Lean rather than mathematics. <code>fun _ _ _ => trivial</code> is a term-mode proof of <code>(0 ↦ 1) ⊢ aTrue</code>: <code>Entails</code> unfolds to <code>∀ σ h, P σ h → Q σ h</code>, so it wants three arguments and ignores all three, and <code>trivial</code> is the constant proof of <code>True</code>, which is what <code>aTrue</code> is at every store and heap. And <code>hbad Heap.empty (disjoint_empty_left _) trivial</code> is the wand being redeemed at the worst possible argument — the empty heap, which is disjoint from everything and satisfies <code>aTrue</code> for free.",
          "src": "theorem wand_mono_needs_contravariance :\n    ¬ (∀ P P' Q : Assertion, (P ⊢ P') → ((P -∗ Q) ⊢ (P' -∗ Q))) := by\n  intro hcontra\n  have hw : ((0 ↦ 1) -∗ (0 ↦ 1)) (fun _ => 0) Heap.empty := by\n    intro h' _ hp\n    rw [union_empty_left]\n    exact hp\n  have hbad := hcontra (0 ↦ 1) aTrue (0 ↦ 1) (fun _ _ _ => trivial) (fun _ => 0) Heap.empty hw\n  have hgot := hbad Heap.empty (disjoint_empty_left _) trivial\n  rw [union_empty_left] at hgot\n  have hz : Heap.empty 0 = Heap.singleton 0 1 0 := by rw [hgot]\n  rw [singleton_same] at hz\n  exact absurd hz (by simp [Heap.empty])"
        },
        {
          "t": "p",
          "h": "The mechanism is the <code>∀ h'</code> in the definition. Widening the antecedent from <code>0 ↦ 1</code> to <code>aTrue</code> widens the set of heaps the promise must handle, and a promise that held for one cell need not hold for every heap. Widening the <i>conclusion</i> costs nothing, because the conclusion is what the promise produces. That asymmetry is the whole of the variance."
        }
      ],
      "pitfall": "Writing <code>hq σ h (…)</code> instead of <code>hq σ _ (…)</code>, because <code>h</code> is the heap you have been thinking about. The heap in the goal is <code>h.union h'</code>, not <code>h</code>, and Lean says so: <code>Application type mismatch: the argument hw h' hd (hp σ h' hp') has type Q σ (h.union h') but is expected to have type Q σ h</code>. When an entailment is applied at a heap, the heap is whatever the fact you are converting is about — which in a wand proof is essentially always the union. Leaving <code>_</code> is not laziness; it is the correct move, because there is exactly one heap that can go there.",
      "variants": "Reverse <code>hp</code> to <code>P ⊢ P'</code> and the theorem is <b>false</b>. You can name the exact point of failure from the goal state above: you hold <code>hp' : P' σ h'</code> and the wand demands <code>P σ h'</code>, so you must travel from <code>P'</code> to <code>P</code> — the wrong way along the reversed hypothesis. The counterexample in the panel above makes that concrete with <code>P = 0 ↦ 1</code>, <code>P' = aTrue</code>, <code>Q = 0 ↦ 1</code>. Reverse <code>hq</code> to <code>Q' ⊢ Q</code> and it fails symmetrically at the last step instead. Drop <code>hp</code> and keep only <code>hq</code> and you get the useful special case <code>(P -∗ Q) ⊢ (P -∗ Q')</code>, which is <code>wand_mono (entails_refl P) hq</code> — the same trick that produced <code>star_mono_left</code> and <code>star_mono_right</code> from <code>star_mono</code> in M4."
    },
    {
      "t": "sec",
      "s": "Consequences, for free"
    },
    {
      "t": "p",
      "h": "This is where the milestone pays. Everything below is a standard law of separating implication, and none of the proofs mentions a heap, a store, or <code>Heap.union</code>. Each is <code>wand_intro</code> applied to something you already have: a reflexivity in the first case, a rearrangement of stars in the other two. That is what “<code>-∗</code> is the right adjoint of <code>∗</code>” means operationally — every wand goal is really a star goal in disguise, and <code>wand_intro</code> is the disguise coming off."
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "Three standard laws, each derived from the adjunction plus M4. All compile against the M11 prelude.",
      "src": "-- the unit of the adjunction\ntheorem wand_unit (P Q : Assertion) : P ⊢ Q -∗ (P ∗ Q) :=\n  wand_intro (entails_refl (P ∗ Q))\n\n-- currying, twice\ntheorem wand_curry (P Q R : Assertion) : ((P ∗ Q) -∗ R) ⊢ P -∗ (Q -∗ R) :=\n  wand_intro (wand_intro (entails_trans (star_assoc_left _ _ _) (wand_elim (P ∗ Q) R)))\n\n-- a wand may be framed, just like a triple\ntheorem wand_frame (P Q R : Assertion) : (P -∗ Q) ⊢ (P ∗ R) -∗ (Q ∗ R) :=\n  wand_intro (entails_trans (star_assoc_right _ _ _) (star_mono_left R (wand_elim P Q)))"
    },
    {
      "t": "p",
      "h": "Read <code>wand_curry</code> as a chain and it is four moves. Two <code>wand_intro</code>s reduce the goal to <code>(((P ∗ Q) -∗ R) ∗ P) ∗ Q ⊢ R</code>; <code>star_assoc_left</code> reassociates it to <code>((P ∗ Q) -∗ R) ∗ (P ∗ Q)</code>; <code>wand_elim</code> closes it. Compare the effort with the semantic proof, which has to assemble <code>Heap.disjoint h (Heap.union h₁ h₂)</code> out of <code>disjoint_union_left</code> and <code>disjoint_union_right</code> and then repair the goal with <code>union_assoc</code>. Both work; only one of them is still a two-line proof when you change the resource model."
    },
    {
      "t": "h4",
      "s": "And one that fails"
    },
    {
      "t": "p",
      "h": "The <code>∗</code> in <code>wand_elim</code> cannot be weakened to <code>∧</code>. It is worth having the counterexample in your hands rather than in your memory, because it is the same phenomenon as the <code>aImp</code> failure earlier and it explains why every wand law is phrased with <code>∗</code>."
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "The witnessing heap is <code>Heap.singleton 0 1</code>, which satisfies both conjuncts at once — and therefore satisfies neither usefully. Three details: <code>⟨?_, rfl⟩</code> is the pair that <code>aAnd</code> wants, with the <code>0 ↦ 1</code> half already closed by <code>rfl</code>; <code>rw [hp] at hd</code> rewrites the incoming heap away <i>inside the hypothesis only</i>, turning <code>hd</code> into <code>(Heap.singleton 0 1).disjoint (Heap.singleton 0 1)</code>, which is already absurd, so the goal never has to be touched; and <code>hd 0</code> applies that disjointness at location <code>0</code>, since <code>Heap.disjoint</code> unfolds to a <code>∀ l</code>. <code>rcases … with hx | hx</code> splits the <code>∨</code> it returns, and here the two branches are literally the same proposition, which is why one <code>&lt;;&gt;</code>-chained script closes both.",
      "src": "theorem wand_and_elim_fails :\n    ¬ (∀ P Q : Assertion, aAnd (P -∗ Q) P ⊢ Q) := by\n  intro hcontra\n  refine hcontra (0 ↦ 1) aFalse (fun _ => 0) (Heap.singleton 0 1) ⟨?_, rfl⟩\n  intro h' hd hp\n  rw [hp] at hd\n  rcases hd 0 with hx | hx <;> rw [singleton_same] at hx <;> exact absurd hx (by simp)"
    },
    {
      "t": "p",
      "h": "The heap is a single cell, so it satisfies <code>0 ↦ 1</code>. Does it satisfy <code>(0 ↦ 1) -∗ aFalse</code>? The wand quantifies over heaps <code>h'</code> that are <b>disjoint</b> from it and satisfy <code>0 ↦ 1</code> — and there are none, because any such <code>h'</code> would have to be <code>Heap.singleton 0 1</code>, which overlaps. So the promise is <i>vacuously</i> kept: it commits you to producing <code>False</code> in a situation that cannot arise. Under <code>∧</code> you may then hold both conjuncts on that one heap and derive nothing. Under <code>∗</code> you may not, because the star insists that the two conjuncts live on disjoint pieces, which is exactly the hypothesis the wand needs. <b>The separating conjunction is not a convenience in <code>wand_elim</code>; it is the entire content of the rule.</b>"
    },
    {
      "t": "p",
      "h": "One forward pointer before the summary. M12 defines <code>wp c Q</code>, the weakest precondition, and observes that <code>Hoare P c Q</code> and <code>P ⊢ wp c Q</code> are the same statement. Wands and <code>wp</code> are the two ways of saying “what I would need in order to get <code>Q</code>” — one about resources, one about programs — and in a full system such as Iris they are combined, with a wand inside the postcondition of a <code>wp</code> serving as the continuation. You have now built one of the two halves."
    },
    {
      "t": "dod",
      "h": "You understand <code>∗</code> and <code>-∗</code> as an adjoint pair, not as two unrelated symbols, and you can prove the standard laws from the adjunction rather than from the model."
    }
  ]
});
