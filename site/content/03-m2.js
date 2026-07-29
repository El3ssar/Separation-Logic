/* M2 — Disjointness, union, and the resource monoid
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m2",
  "num": "M2",
  "phase": "Phase 1 · Semantic foundations",
  "title": "Disjointness, union, and the resource monoid",
  "blurb": "The algebraic structure that makes separating conjunction possible: a partial commutative monoid.",

  "orient": {
    "youWill": [
      "State and prove that <code>(Heap, Heap.union, Heap.empty)</code> is a partial commutative monoid — unit, associativity, and commutativity-under-disjointness.",
      "Case on an <code>Option</code> while keeping the equation, with <code>cases hl : h l with | none =&gt; … | some v =&gt; …</code>, and know why the equation is the whole point.",
      "Use <code>left</code>/<code>right</code>, <code>rcases … with h | h</code>, <code>intro ⟨ha, hb⟩</code>, <code>refine ⟨…, ?_⟩</code>, <code>obtain</code>, <code>subst</code>, <code>absurd</code> and <code>.mp</code>/<code>.mpr</code> without stopping to think.",
      "Split a disjointness fact across a union and rebuild it again — the two lemmas you will reach for in every remaining chapter.",
      "Say precisely why <code>union_assoc</code> needs no hypothesis and <code>union_comm</code> does, and exhibit the heaps that break the second one."
    ],
    "needs": [
      "M1: a heap is <code>Loc → Option Val</code>, and the six lookup lemmas (<code>singleton_same</code>, <code>singleton_other</code>, …) are already proved.",
      "<code>funext</code> followed by case analysis on the location as the standard way to prove two heaps equal (M0, M1).",
      "The anonymous constructor <code>⟨…⟩</code> for <code>∧</code> and <code>∃</code>, and the fact that it nests and flattens (M0)."
    ],
    "payoff": "Separating conjunction in M4 is <i>defined</i> by quantifying over the two heaps a heap splits into, so every law it satisfies is one of the nine facts proved here with a store and an assertion payload carried alongside. <code>star_comm</code>’s proof is <code>splits_comm</code>’s; <code>star_assoc_left</code>’s is <code>splits_assoc</code>’s. Do the work now and M4 is bookkeeping."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "Separation logic needs one thing from its model: a way to say <i>“this resource splits into these two independent pieces”</i>. For heaps that means two definitions."
    },
    {
      "t": "code",
      "src": "def Heap.disjoint (h₁ h₂ : Heap) : Prop :=\n  ∀ l, h₁ l = none ∨ h₂ l = none\n\ndef Heap.union (h₁ h₂ : Heap) : Heap :=\n  fun l =>\n    match h₁ l with\n    | some v => some v\n    | none   => h₂ l\n\ndef Heap.splits (whole left right : Heap) : Prop :=\n  Heap.disjoint left right ∧ whole = Heap.union left right"
    },
    {
      "t": "svg",
      "src": "\n<svg viewBox=\"0 0 560 172\" role=\"img\" aria-label=\"Splitting a heap into two disjoint parts\">\n  <g class=\"dg\">\n    <rect x=\"20\" y=\"26\" width=\"220\" height=\"60\" rx=\"8\" class=\"dg-box\"/>\n    <text x=\"130\" y=\"62\" text-anchor=\"middle\" class=\"dg-t\">h</text>\n    <text x=\"130\" y=\"18\" text-anchor=\"middle\" class=\"dg-lab\">one heap</text>\n    <path class=\"dg-arr\" d=\"M250 56 L 300 56\"/>\n    <rect x=\"312\" y=\"20\" width=\"106\" height=\"34\" rx=\"7\" class=\"dg-box a\"/>\n    <text x=\"365\" y=\"42\" text-anchor=\"middle\" class=\"dg-t\">h₁</text>\n    <rect x=\"430\" y=\"20\" width=\"106\" height=\"34\" rx=\"7\" class=\"dg-box b\"/>\n    <text x=\"483\" y=\"42\" text-anchor=\"middle\" class=\"dg-t\">h₂</text>\n    <text x=\"424\" y=\"76\" text-anchor=\"middle\" class=\"dg-note\">disjoint: domains never overlap</text>\n    <text x=\"424\" y=\"94\" text-anchor=\"middle\" class=\"dg-note\">h = h₁ ∪ h₂</text>\n    <g class=\"dg-cells\">\n      <rect x=\"36\" y=\"112\" width=\"34\" height=\"26\" rx=\"4\" class=\"a\"/>\n      <rect x=\"76\" y=\"112\" width=\"34\" height=\"26\" rx=\"4\" class=\"b\"/>\n      <rect x=\"116\" y=\"112\" width=\"34\" height=\"26\" rx=\"4\" class=\"a\"/>\n      <rect x=\"156\" y=\"112\" width=\"34\" height=\"26\" rx=\"4\" class=\"b\"/>\n      <rect x=\"196\" y=\"112\" width=\"34\" height=\"26\" rx=\"4\" class=\"a\"/>\n    </g>\n    <text x=\"130\" y=\"158\" text-anchor=\"middle\" class=\"dg-note\">every allocated cell belongs to exactly one side</text>\n  </g>\n</svg>"
    },
    {
      "t": "p",
      "h": "Two remarks about the definition of <code>union</code>, both important."
    },
    {
      "t": "ul",
      "items": [
        "It is <b>left-biased</b> and therefore total: <code>union h₁ h₂</code> exists for <i>any</i> two heaps. If they overlap, the left one wins. This is a convenience — a genuinely partial operation is painful in a total type theory.",
        "Because of that convenience you must be disciplined: separation logic only ever uses <code>union</code> <i>accompanied by a disjointness proof</i>. Every lemma below that needs disjointness says so explicitly, and the ones that do not (associativity!) are worth noticing."
      ]
    },

    {
      "t": "h4",
      "s": "Reading the three definitions"
    },
    {
      "t": "p",
      "h": "Three Lean-specific things are happening in those eleven lines, and none of them is about mathematics. Take them one at a time."
    },
    {
      "t": "anat",
      "src": "def Heap.disjoint (h₁ h₂ : Heap) : Prop :=\n  ∀ l, h₁ l = none ∨ h₂ l = none",
      "parts": [
        {
          "m": ": Prop",
          "h": "This is a <code>def</code>, not a <code>theorem</code>: it does not prove anything, it <i>names a proposition</i>. <code>Heap.disjoint h₁ h₂</code> is a term of type <code>Prop</code>, and it is <b>definitionally equal</b> to the body. That single fact drives every proof in this chapter."
        },
        {
          "m": "∀ l,",
          "h": "Because the body is a <code>∀</code>, and because the definition unfolds definitionally, a goal that reads <code>Heap.disjoint h₁ h₂</code> can be attacked directly with <code>intro l</code> — no <code>unfold</code> needed. Symmetrically, a hypothesis <code>hd : Heap.disjoint h₁ h₂</code> is a <i>function</i>: <code>hd l</code> is already a proof of the disjunction at <code>l</code>."
        },
        {
          "m": "h₁ l = none ∨ h₂ l = none",
          "h": "“At every location, at least one of the two is undefined.” Note what is <i>not</i> said: nothing forbids both being <code>none</code>. Disjointness is about domains not overlapping, not about the two heaps together covering anything."
        }
      ]
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "Lean will print this back to you as <code>h₁.disjoint h₂</code>",
      "h": "Every goal state in this chapter uses <b>generalised field notation</b>: because the first explicit argument of <code>Heap.disjoint</code> has type <code>Heap</code>, Lean displays <code>Heap.disjoint h₁ h₂</code> as <code>h₁.disjoint h₂</code>, and <code>Heap.union h₁ h₂</code> as <code>h₁.union h₂</code>. It is the same term. You may type either form. Expect the printer to rewrite what you wrote."
    },
    {
      "t": "state",
      "src": "h₁ h₂ : Heap\n⊢ h₁.disjoint h₂ → h₂.disjoint h₁",
      "cap": "The opening goal of the first exercise, exactly as Lean prints it. The source says <code>Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁</code>."
    },
    {
      "t": "anat",
      "src": "def Heap.union (h₁ h₂ : Heap) : Heap :=\n  fun l =>\n    match h₁ l with\n    | some v => some v\n    | none   => h₂ l",
      "parts": [
        {
          "m": "fun l =>",
          "h": "The result is a <code>Heap</code>, which is a function, so the body is a lambda. There is no data structure here and nothing is allocated; <code>union</code> builds a new function pointwise, exactly like <code>Heap.write</code> in M1."
        },
        {
          "m": "match h₁ l with",
          "h": "The scrutinee is <code>h₁ l</code> — the <i>left</i> heap. This asymmetry is invisible mathematically and extremely visible in Lean: a <code>match</code> reduces only when its scrutinee is literally a constructor. <code>Heap.empty l</code> reduces to <code>none</code>, so it computes; an opaque <code>h l</code> does not, so it does not. That is the whole reason <code>union_empty_left</code> is one <code>rfl</code> and <code>union_empty_right</code> is a case split."
        },
        {
          "m": "| some v => some v",
          "h": "Left-biased: if the left heap has a value at <code>l</code>, that value is the answer, and the right heap is never consulted. Under a disjointness hypothesis this branch can only fire where the right heap is <code>none</code>, so the bias is unobservable — but Lean does not know that, and neither does <code>rfl</code>."
        },
        {
          "m": "| none   => h₂ l",
          "h": "Otherwise defer to the right heap. Note this returns <code>h₂ l</code> whatever it is, including <code>none</code>; the union of two heaps undefined at <code>l</code> is undefined at <code>l</code>."
        }
      ]
    },
    {
      "t": "cmp",
      "left": {
        "t": "What a mathematician writes",
        "kind": "good",
        "h": "“Let <code>h₁</code> and <code>h₂</code> be disjoint heaps and define their union <code>h₁ ⊎ h₂</code>.” The operation is <i>partial</i>: <code>h₁ ⊎ h₂</code> simply does not exist when the domains overlap, and no statement about it can even be formed in that case."
      },
      "right": {
        "t": "What Lean needs",
        "h": "A function must be total. If disjointness lives in the <i>type</i> of <code>union</code>, then every occurrence of a union carries a proof term, two unions that are propositionally equal may have different proofs inside them, and every rewrite has to transport those proofs. So: <code>union</code> is defined for all pairs, left-biased, and disjointness becomes an ordinary hypothesis supplied at the point of use.",
        "src": "def Heap.union (h₁ h₂ : Heap) : Heap :=\n  fun l =>\n    match h₁ l with\n    | some v => some v\n    | none   => h₂ l"
      }
    },
    {
      "t": "p",
      "h": "That is why every lemma below carries an explicit <code>hd : Heap.disjoint h₁ h₂</code> argument that on paper would be invisible — and why the lemmas that <i>omit</i> it (associativity, and both halves of <code>disjoint_union_left</code>) are worth a second look: they are true of the total, biased operation, unconditionally."
    },
    {
      "t": "detail",
      "title": "What breaks if you put the proof in the type",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "Here is the dependent version. It is a legal definition — the problem is not that Lean rejects it, the problem is what its <i>statements</i> look like."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "def unionD (h₁ h₂ : Heap) (_ : Heap.disjoint h₁ h₂) : Heap :=\n  Heap.union h₁ h₂\n\ntheorem unionD_assoc (h₁ h₂ h₃ : Heap)\n    (d₁₂ : Heap.disjoint h₁ h₂)\n    (d₁₂₃ : Heap.disjoint (unionD h₁ h₂ d₁₂) h₃)\n    (d₂₃ : Heap.disjoint h₂ h₃)\n    (d₁₂₃' : Heap.disjoint h₁ (unionD h₂ h₃ d₂₃)) :\n    unionD (unionD h₁ h₂ d₁₂) h₃ d₁₂₃ = unionD h₁ (unionD h₂ h₃ d₂₃) d₁₂₃' :=\n  union_assoc h₁ h₂ h₃"
        },
        {
          "t": "p",
          "h": "Four disjointness arguments are needed merely to <i>state</i> associativity, two of them mentioning the operation being defined. The proof is still one line, because <code>unionD a b _</code> is definitionally <code>Heap.union a b</code> — but every later lemma would have to be threaded through this, and every rewrite would have to produce the right proof term in the right position. Compare the statement you will actually prove: <code>union_assoc (h₁ h₂ h₃ : Heap)</code>, no hypotheses at all."
        },
        {
          "t": "p",
          "h": "The trade is standard in mechanised mathematics: make the operation total and junk-valued outside its intended domain, and carry the domain condition as a side hypothesis. The discipline you lose is the discipline you must now supply yourself."
        }
      ]
    },
    {
      "t": "defn",
      "term": "Heap.splits whole left right",
      "h": "<code>left</code> and <code>right</code> are disjoint, <b>and</b> <code>whole</code> is their union. Note the direction of the equation: <code>whole = Heap.union left right</code>, with the whole on the left. A proof is a pair <code>⟨hd, he⟩</code>, and every proof in the splitting section begins by making that pair or taking it apart.",
      "cap": "This three-place relation is the entire content of separating conjunction."
    },
    {
      "t": "p",
      "h": "One warning, because it is easy to expect otherwise: <code>Heap.splits</code> is used in this chapter and then never again. M4 does not build <code>∗</code> on top of it. It writes the two conjuncts out:"
    },
    {
      "t": "code",
      "cap": "M4’s definition. The middle two components are exactly <code>Heap.splits h h₁ h₂</code>, unbundled.",
      "src": "def star (P Q : Assertion) : Assertion :=\n  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂"
    },
    {
      "t": "p",
      "h": "The reason is ergonomic: with everything flat, one pattern <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code> takes an entire separating conjunction apart in a single <code>intro</code>. Had M4 used <code>Heap.splits</code>, that pattern would need an extra layer of brackets at every use. So <code>splits</code> earns its keep <i>here</i>, as the name under which you prove the laws in the small; from M4 on you meet the same laws with the pair spread out."
    },

    {
      "t": "h4",
      "s": "The algebra"
    },
    {
      "t": "p",
      "h": "What we are about to prove is that heaps form a <b>partial commutative monoid</b> (PCM): a set with a partial binary operation <code>·</code> and a unit <code>e</code> such that, whenever both sides are defined, <code>(a·b)·c = a·(b·c)</code>, <code>a·b = b·a</code>, and <code>e·a = a</code>."
    },
    {
      "t": "note",
      "h": "This is the actual foundation of the subject. Separating conjunction is not “a connective about heaps”; it is <b>the connective induced by any PCM</b>. Swap heaps for file handles, permissions, tokens, ghost state, or fractional ownership, and every law you prove in M4 still holds verbatim. That is why one framework (Iris) can talk about all of them at once.",
      "title": "The one thing to remember",
      "kind": "key"
    },
    {
      "t": "p",
      "h": "Definitions of the three PCM ingredients, in our model: the unit is <code>Heap.empty</code>; the operation is <code>Heap.union</code>; and “defined” means <code>Heap.disjoint</code>."
    },
    {
      "t": "tbl",
      "head": ["PCM law", "In this model", "Lean name", "Needs <code>disjoint</code>?"],
      "rows": [
        ["<code>e · a = a</code>", "<code>∅ ∪ h = h</code>", "<code>union_empty_left</code>", "no"],
        ["<code>a · e = a</code>", "<code>h ∪ ∅ = h</code>", "<code>union_empty_right</code>", "no"],
        ["<code>(a·b)·c = a·(b·c)</code>", "<code>(h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃)</code>", "<code>union_assoc</code>", "<b>no</b> — this is the surprise"],
        ["<code>a · b = b · a</code>", "<code>h₁ ∪ h₂ = h₂ ∪ h₁</code>", "<code>union_comm</code>", "<b>yes</b> — and it is false without it"],
        ["<code>a # b ⟹ b # a</code>", "definedness is symmetric", "<code>disjoint_symm</code>", "—"],
        ["<code>e # a</code>", "the unit is compatible with everything", "<code>disjoint_empty_left</code> / <code>_right</code>", "—"],
        ["<code>(a·b) # c ⟺ a # c ∧ b # c</code>", "definedness distributes over the operation", "<code>disjoint_union_left</code> / <code>_right</code>", "—"]
      ],
      "cap": "The nine exercises below are exactly this table. Nothing else about heaps is used after M4."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "left / right",
          "h": "Pick a side of a goal <code>A ∨ B</code>. <code>left</code> leaves you proving <code>A</code>, <code>right</code> leaves <code>B</code>. Introduced in <code>singleton_disjoint</code>."
        },
        {
          "k": "rcases h with a | b",
          "h": "Case on a hypothesis that <i>is</i> a disjunction. The bar separates one pattern per constructor of <code>Or</code>. You may use the same name in both branches; it stands for a different fact in each, and the case labels <code>inl</code>/<code>inr</code> tell you which."
        },
        {
          "k": "cases hl : e with | none =&gt; … | some v =&gt; …",
          "h": "The workhorse of this chapter. Case on the <i>value</i> of an expression rather than on a hypothesis, and — this is what the <code>hl :</code> prefix buys — record which case you are in as a hypothesis <code>hl : e = none</code> / <code>hl : e = some v</code>. Plain <code>cases e</code> substitutes the constructor into the goal wherever <code>e</code> appears syntactically and then forgets, which is useless here: the occurrence you care about is buried inside <code>Heap.union</code>, where <code>cases</code> cannot see it, and the saved equation is the only handle on it. Assume the <code>hl :</code> is mandatory."
        },
        {
          "k": "intro ⟨ha, hb⟩",
          "h": "<code>intro</code> with a pattern: introduce the hypothesis and destructure it in one move, so the conjunction never appears in the context. <code>obtain ⟨ha, hb⟩ := h</code> does the same to something already in scope."
        },
        {
          "k": "refine ⟨…, ?_⟩",
          "h": "Like <code>exact</code>, but every <code>?_</code> becomes a new goal. Use it when you know the shape of the answer and only some pieces are real work. The goals are labelled <code>refine_1</code>, <code>refine_2</code>, … in the order they appear."
        },
        {
          "k": "h.mp / h.mpr",
          "h": "The two directions of <code>h : A ↔ B</code>: <code>h.mp : A → B</code> and <code>h.mpr : B → A</code>. To <i>prove</i> an <code>↔</code>, <code>constructor</code> splits it into goals named <code>mp</code> and <code>mpr</code>."
        },
        {
          "k": "subst h",
          "h": "Given <code>h : x = e</code> where <code>x</code> is a local variable not occurring in <code>e</code>, delete <code>x</code> and replace it everywhere by <code>e</code>. Stronger than <code>rw [h] at *</code>: afterwards the variable does not exist, so nothing can reintroduce it."
        },
        {
          "k": "absurd h hn",
          "h": "From <code>h : A</code> and <code>hn : ¬A</code>, produce a term of any type at all. Used here to kill goals once you have manufactured <code>some v = none</code>."
        },
        {
          "k": "rwa [e] at h",
          "h": "<code>rw [e] at h</code> followed by <code>exact h</code>. The trailing <code>a</code> is for <i>assumption</i>."
        },
        {
          "k": "tac &lt;;&gt; · tacs",
          "h": "<code>&lt;;&gt;</code> runs its right-hand side on <i>every</i> goal the left-hand side produced. The focus dot <code>·</code> groups several tactics into one block so that the block can be that right-hand side."
        }
      ],
      "cap": "Nine pieces of tactic vocabulary, all new in this chapter. Each is explained again where it is first used."
    },

    {
      "t": "sec",
      "s": "Exercises · disjointness"
    },
    {
      "t": "ex",
      "id": "m2-1",
      "name": "disjoint_symm",
      "hard": false,
      "why": "The shortest proof in the chapter, and the first place a <code>def</code> returning <code>Prop</code> is silently unfolded — the move that makes every later proof possible. Symmetry of disjointness is also the workhorse of the derive-don’t-reprove habit: <code>disjoint_union_right</code> and half of <code>splits_comm</code> are this lemma applied twice.",
      "goal": "theorem disjoint_symm {h₁ h₂ : Heap} :\n    Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁",
      "hints": [
        "The goal is an implication whose conclusion is, once unfolded, a <code>∀</code>. So there are two things to introduce, not one — and you may introduce both without touching the definition.",
        "After <code>intro hd l</code> you have <code>hd : Heap.disjoint h₁ h₂</code> and <code>l : Loc</code>. What is <code>hd l</code>? It is a proof of <code>h₁ l = none ∨ h₂ l = none</code>, because <code>hd</code> is definitionally a function.",
        "The goal at <code>l</code> is the same disjunction with the sides swapped. Flipping a disjunction is <code>Or.symm</code>. Dot notation lets you write it as <code>(hd l).symm</code> — note the parentheses."
      ],
      "hint": "<code>Or.symm</code> applied pointwise. Two lines.",
      "sol": "theorem disjoint_symm {h₁ h₂ : Heap} : Heap.disjoint h₁ h₂ → Heap.disjoint h₂ h₁ := by\n  intro hd l\n  exact (hd l).symm",
      "expl": "<code>hd l : h₁ l = none ∨ h₂ l = none</code> and <code>Or.symm</code> flips it. The whole proof is that the definition is symmetric by construction.",
      "walk": [
        {
          "tac": "intro hd l",
          "h": "Two introductions in one tactic. The first, <code>hd</code>, is the antecedent of the arrow. The second, <code>l</code>, is the bound location — legal because the remaining goal <code>Heap.disjoint h₂ h₁</code> <i>is</i> <code>∀ l, h₂ l = none ∨ h₁ l = none</code> by definitional unfolding. Notice in the trace below that the goal changes from the folded form to the unfolded disjunction at exactly this step."
        },
        {
          "tac": "exact (hd l).symm",
          "h": "<code>hd l</code> instantiates the hypothesis at the location now in scope, giving <code>h₁ l = none ∨ h₂ l = none</code>. <code>.symm</code> resolves to <code>Or.symm</code> — dot notation looks up the head symbol of the <i>type</i>, which is <code>Or</code> — and produces the swapped disjunction, which is the goal."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "disjoint_symm, tactic by tactic",
          "start": "h₁ h₂ : Heap\n⊢ h₁.disjoint h₂ → h₂.disjoint h₁",
          "steps": [
            {
              "tac": "intro hd l",
              "state": "h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\n⊢ h₂ l = none ∨ h₁ l = none",
              "h": "This is the step worth staring at. The goal was displayed as <code>h₂.disjoint h₁</code>, an opaque-looking application. After <code>intro l</code> it is a plain disjunction about <code>h₂ l</code> and <code>h₁ l</code>. Nothing was rewritten: <code>intro</code> puts the goal into weak head normal form first, which unfolds the <code>def</code>, finds a <code>∀</code>, and introduces its binder. The hypothesis <code>hd</code> stays folded, because nothing forced it to unfold."
            },
            {
              "tac": "exact (hd l).symm",
              "h": "<code>@Or.symm : ∀ {a b : Prop}, a ∨ b → b ∨ a</code>. Applying it to <code>hd l</code> yields exactly the goal."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why <code>(hd l).symm</code> and not <code>hd.symm l</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Dot notation is resolved from the <i>head constant of the type</i> of the thing before the dot. The type of <code>hd</code> is <code>∀ (l : Loc), h₁ l = none ∨ h₂ l = none</code>, whose head is the function arrow, so <code>hd.symm</code> looks for <code>Function.symm</code>:"
            },
            {
              "t": "state",
              "src": "error: Invalid field `symm`: The environment does not contain `Function.symm`, so it is not possible to project the field `symm` from an expression\n  hd\nof type\n  ∀ (l : Loc), h₁ l = none ∨ h₂ l = none"
            },
            {
              "t": "p",
              "h": "Apply first, then project: <code>hd l</code> has type <code>… ∨ …</code>, head constant <code>Or</code>, so <code>.symm</code> finds <code>Or.symm</code>. The parentheses are load-bearing — <code>hd l.symm</code> would parse as <code>hd (l.symm)</code>."
            }
          ]
        }
      ],
      "pitfall": "Trying to flip the disjunction before introducing the location. <code>apply Or.symm</code> on the goal <code>Heap.disjoint h₂ h₁</code> fails, because at that point the goal is a <code>∀</code>, not an <code>∨</code>. The order is forced: introduce <code>l</code> first, then work with the disjunction. Equally common is writing <code>exact hd l</code> — that is the disjunction with the sides in the <i>wrong</i> order, and the error message compares two disjunctions that look confusingly similar.",
      "variants": "The statement is an implication, but it may as well be an <code>↔</code>: <code>⟨disjoint_symm, disjoint_symm⟩</code> proves <code>Heap.disjoint h₁ h₂ ↔ Heap.disjoint h₂ h₁</code>, since a symmetric relation is its own converse. Contrast this with <code>union_comm</code> later: that statement is also symmetric in <code>h₁</code> and <code>h₂</code>, but its <i>proof</i> genuinely needs a hypothesis. Symmetry of <code>disjoint</code> is free because the body is a symmetric disjunction; symmetry of <code>union</code> is not free because the body is a biased <code>match</code>."
    },
    {
      "t": "ex",
      "id": "m2-2",
      "name": "disjoint_empty_left / right",
      "hard": false,
      "why": "The unit of a PCM has to be compatible with everything, and this is that axiom. Concretely, you need it every time you have to manufacture a splitting one of whose halves owns nothing — <code>splits_empty_left</code> below, then M4’s <code>star_emp_left_intro</code> and <code>star_pure_right</code>, M7’s <code>hoare_load</code>, and M10’s concrete linked list. It is also the cleanest example in the course of a proof written as a <i>term</i>, with no tactics at all.",
      "goal": "theorem disjoint_empty_left  (h : Heap) : Heap.disjoint Heap.empty h\ntheorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty",
      "hints": [
        "There is nothing to case on. At every location the empty heap is undefined, so the same disjunct works everywhere. That means the proof is a constant function <code>fun _ =&gt; …</code>.",
        "<code>@Or.inl : ∀ {a b : Prop}, a → a ∨ b</code> builds the left disjunct; <code>Or.inr</code> builds the right. Which one you need depends on which argument of <code>Heap.disjoint</code> the empty heap is.",
        "What proves <code>Heap.empty l = none</code>? Look at the definition: <code>Heap.empty</code> is <code>fun _ =&gt; none</code>, so <code>Heap.empty l</code> <i>reduces</i> to <code>none</code>. Both sides are then literally the same term, so <code>rfl</code> typechecks.",
        "Left: <code>fun _ =&gt; Or.inl rfl</code>. Right: the same with <code>Or.inr</code>."
      ],
      "hint": "Give the term directly: <code>fun _ => Or.inl rfl</code>.",
      "sol": "theorem disjoint_empty_left (h : Heap) : Heap.disjoint Heap.empty h :=\n  fun _ => Or.inl rfl\n\ntheorem disjoint_empty_right (h : Heap) : Heap.disjoint h Heap.empty :=\n  fun _ => Or.inr rfl",
      "expl": "<code>Heap.empty l</code> <i>is</i> <code>none</code> by definition, so <code>rfl</code> proves it. No tactic needed.",
      "walk": [
        {
          "tac": ":=",
          "h": "The line that is not there is the interesting one: there is no <code>by</code>. The proof is a term, given directly. This is legal for every theorem — tactics are only a way of <i>constructing</i> such a term — and it is worth doing once so that the identification of proofs with terms stops being a slogan."
        },
        {
          "tac": "fun _ =>",
          "h": "The statement <code>Heap.disjoint Heap.empty h</code> unfolds to <code>∀ l, Heap.empty l = none ∨ h l = none</code>, and a proof of a <code>∀</code> is a function. The binder is written <code>_</code> because the body does not mention the location."
        },
        {
          "tac": "Or.inl rfl",
          "h": "The left disjunct is <code>Heap.empty l = none</code>, so we prove that and inject on the left. Lean infers the implicit <code>b</code> of <code>Or.inl</code> from the goal."
        },
        {
          "tac": "rfl",
          "h": "The argument of <code>Or.inl</code>, on its own. <code>rfl : a = a</code>. Here it is asked to have type <code>Heap.empty l = none</code>. Lean checks that by unfolding <code>Heap.empty</code> to <code>fun _ =&gt; none</code> and beta-reducing, giving <code>none = none</code>. Definitional equality does that silently; there is no rewriting step to see."
        },
        {
          "tac": "fun _ => Or.inr rfl",
          "h": "The mirror image. In <code>disjoint_empty_right</code> the empty heap is the <i>second</i> argument, so the disjunct that is provable is the right one. Same <code>rfl</code>, different injection."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "The same proof, driven by tactics, so you can see the goals",
          "start": "h : Heap\n⊢ Heap.empty.disjoint h",
          "steps": [
            {
              "tac": "intro l",
              "state": "h : Heap\nl : Loc\n⊢ Heap.empty l = none ∨ h l = none",
              "h": "The <code>∀</code> hidden inside the definition, introduced. This is the tactic counterpart of writing <code>fun _ =&gt;</code>."
            },
            {
              "tac": "left",
              "state": "h : Heap\nl : Loc\n⊢ Heap.empty l = none",
              "h": "<code>left</code> commits to the first disjunct and discards the second — the tactic counterpart of <code>Or.inl</code>. There is no going back: if you choose wrong you must undo."
            },
            {
              "tac": "rfl",
              "h": "Closes the goal by definitional unfolding of <code>Heap.empty</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "Term proof",
            "kind": "good",
            "h": "One line, no goal states, and it says what the mathematics is: <i>constantly, choose the left disjunct, which is true by computation</i>.",
            "src": "fun _ => Or.inl rfl",
            "tag": "verified"
          },
          "right": {
            "t": "Tactic proof",
            "h": "Three tactics, and <code>simp [Heap.disjoint, Heap.empty]</code> closes it in one. Both work. The term version is preferred here because it is shorter than the goal state it would print.",
            "src": "theorem disjoint_empty_left' (h : Heap) : Heap.disjoint Heap.empty h := by\n  simp [Heap.disjoint, Heap.empty]",
            "tag": "illustration"
          }
        }
      ],
      "pitfall": "Picking the wrong injection. <code>disjoint_empty_right</code> with <code>Or.inl rfl</code> asks Lean to prove <code>h l = none</code> for an arbitrary heap <code>h</code>, which is false, and the error appears at <code>rfl</code> rather than at <code>Or.inl</code> — so the message points at the innocent half of the term. Read the statement, find which side the empty heap is on, and choose the matching injection.",
      "variants": "Reverse the roles and ask when a heap is disjoint from <i>itself</i>: <code>Heap.disjoint h h</code> forces <code>h = Heap.empty</code>, since <code>h l = none ∨ h l = none</code> gives <code>h l = none</code> at every <code>l</code>. So <code>empty</code> is not merely <i>a</i> self-disjoint heap, it is the only one. Spell out the consequence carefully, because it is the reason <code>∗</code> is substructural: if <code>P</code> holds of exactly one heap <code>h₀</code> — as <code>l ↦ v</code> and <code>emp</code> do — then <code>P ∗ P</code> demands a splitting into two heaps each satisfying <code>P</code>, so both are <code>h₀</code>, so <code>h₀ ⊥ h₀</code>, so <code>h₀</code> is empty. For any exact assertion that owns anything at all, <code>P ∗ P</code> is unsatisfiable. Ownership does not duplicate, and this one-line lemma is the whole reason.<br><br>The proof, for reference: <code>funext l; rcases hd l with hl | hl &lt;;&gt; exact hl</code> — both disjuncts are the same statement, so the same tactic finishes both, and <code>Heap.empty l</code> is <code>none</code> definitionally, so no rewriting is needed to match."
    },
    {
      "t": "ex",
      "id": "m2-3",
      "name": "singleton_disjoint (and its converse)",
      "hard": false,
      "why": "The ⟸ direction is easy. The ⟹ direction is the first time you see <b>separation implying non-aliasing</b> — the fact that owning two cells separately <i>proves</i> they are different. It is a small lemma with a large moral.",
      "goal": "theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂)\n\ntheorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂",
      "hints": [
        "For the easy direction: fix a location <code>x</code> and ask whether <code>x = l₁</code>. In each of the two cases, one of the two singletons is provably undefined at <code>x</code> — say which, then pick that disjunct with <code>left</code> or <code>right</code>.",
        "In the branch <code>hx : x = l₁</code> you must show <code>Heap.singleton l₂ v₂ x = none</code>, i.e. apply <code>singleton_other l₂ x v₂</code> to a proof of <code>x ≠ l₂</code>. You do not have one — derive it: rewriting <code>x</code> to <code>l₁</code> with <code>hx</code> turns the goal <code>x ≠ l₂</code> into <code>l₁ ≠ l₂</code>, which is <code>hne</code>.",
        "For the <code>↔</code>: <code>constructor</code> splits it into <code>mp</code> and <code>mpr</code>. The <code>mpr</code> half is just the theorem you already proved. For <code>mp</code>, the conclusion <code>l₁ ≠ l₂</code> unfolds to <code>l₁ = l₂ → False</code>, so <code>intro hd heq</code> gives you both hypotheses and a goal of <code>False</code>.",
        "With <code>heq : l₁ = l₂</code> in hand, <code>subst heq</code> makes the two singletons live at the same location. Then <code>hd l₁</code> is a disjunction that says one of them is <code>none</code> there — and <code>singleton_same</code> says both are <code>some _</code>. <code>rcases hd l₁ with h | h</code> names the two cases; both die the same way, so <code>&lt;;&gt;</code> plus a focus dot handles them together."
      ],
      "hint": "For ⟸: split on <code>x = l₁</code>. For ⟹: assume <code>l₁ = l₂</code>, substitute, and instantiate the disjointness at <code>l₁</code>; both disjuncts contradict <code>singleton_same</code>.",
      "sol": "theorem singleton_disjoint {l₁ l₂ : Loc} (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) := by\n  intro x\n  by_cases hx : x = l₁\n  · right\n    have : x ≠ l₂ := by rw [hx]; exact hne\n    exact singleton_other l₂ x v₂ this\n  · left\n    exact singleton_other l₁ x v₁ hx\n\ntheorem singleton_disjoint_iff {l₁ l₂ : Loc} (v₁ v₂ : Val) :\n    Heap.disjoint (Heap.singleton l₁ v₁) (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂ := by\n  constructor\n  · intro hd heq\n    subst heq\n    rcases hd l₁ with h | h <;>\n      · rw [singleton_same] at h; exact absurd h (by simp)\n  · exact singleton_disjoint v₁ v₂",
      "expl": "In the forward direction, after <code>subst heq</code> both singletons live at the same location, so <code>hd l₁</code> claims one of them is <code>none</code> there — but <code>singleton_same</code> says both are <code>some _</code>. The <code>&lt;;&gt; ·</code> block applies the same three-step contradiction to both disjuncts.",
      "walk": [
        {
          "tac": "intro x",
          "h": "Unfolds the definition and introduces the location. The goal becomes the disjunction at <code>x</code>."
        },
        {
          "tac": "by_cases hx : x = l₁",
          "h": "Two goals, labelled <code>pos</code> and <code>neg</code>, differing only in whether <code>hx : x = l₁</code> or <code>hx : ¬x = l₁</code> is in context. <code>Loc</code> is <code>Nat</code>, which has decidable equality, so no classical axiom is invoked here."
        },
        {
          "tac": "· right",
          "h": "In the <code>pos</code> branch <code>x</code> is <code>l₁</code>, so the <i>left</i> singleton is defined there and only the right disjunct is provable. <code>right</code> commits to it, discarding <code>Heap.singleton l₁ v₁ x = none</code> — which is just as well, since it is false here."
        },
        {
          "tac": "have : x ≠ l₂ := by rw [hx]; exact hne",
          "h": "An <i>anonymous</i> <code>have</code>: no name is given, so the fact enters the context as <code>this</code>. Inside, the goal is <code>x ≠ l₂</code>, which is the application <code>Ne x l₂</code>; <code>x</code> sits there as an ordinary argument, so <code>rw [hx]</code> replaces it by <code>l₁</code> and leaves <code>l₁ ≠ l₂</code>, which is exactly <code>hne</code>. This one line is where non-aliasing enters the proof."
        },
        {
          "tac": "exact singleton_other l₂ x v₂ this",
          "h": "<code>singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) : Heap.singleton l v x = none</code>. Read the argument order carefully: <b>first</b> the location the singleton lives at, <b>then</b> the location being probed. Here the singleton is at <code>l₂</code> and we are probing <code>x</code>."
        },
        {
          "tac": "· left",
          "h": "The <code>neg</code> branch. Now <code>x ≠ l₁</code>, so the left singleton is undefined at <code>x</code> and the left disjunct is the provable one."
        },
        {
          "tac": "exact singleton_other l₁ x v₁ hx",
          "h": "<code>hx : ¬x = l₁</code> is accepted where <code>x ≠ l₁</code> is wanted, with no conversion step. <code>Ne</code> is not notation, it is a definition — <code>@[reducible] def Ne a b := ¬a = b</code> — but it is a <i>reducible</i> one, so <code>exact</code> unfolds it without being asked. What the printer shows you is not a reliable guide to which of the two forms is written in the term: <code>by_cases</code> produces <code>¬x = l₁</code>, the lemma statement says <code>x ≠ l</code>, and they are the same thing."
        },
        {
          "tac": "constructor",
          "h": "Second theorem. On an <code>↔</code> goal, <code>constructor</code> applies <code>Iff.intro</code>, producing two goals named <code>mp</code> (forwards) and <code>mpr</code> (backwards)."
        },
        {
          "tac": "· intro hd heq",
          "h": "Two introductions again, but for a subtler reason: the goal <code>l₁ ≠ l₂</code> <i>is</i> <code>l₁ = l₂ → False</code>. So after taking the disjointness hypothesis <code>hd</code> we may keep going and take the equation <code>heq</code>, leaving the goal <code>False</code>."
        },
        {
          "tac": "subst heq",
          "h": "<code>heq : l₁ = l₂</code> with <code>l₂</code> a local variable, so <code>l₂</code> is eliminated and every occurrence becomes <code>l₁</code>. The context shrinks by one variable: look at the trace and see <code>l₂</code> disappear, and <code>hd</code> become a claim about two singletons at the <i>same</i> location."
        },
        {
          "tac": "rcases hd l₁ with h | h <;>",
          "h": "Instantiate the disjointness at the shared location and split the resulting <code>∨</code>. Two goals, <code>inl</code> and <code>inr</code>; in the first <code>h : Heap.singleton l₁ v₁ l₁ = none</code>, in the second the same for <code>v₂</code>. The trailing <code>&lt;;&gt;</code> says: run what follows on both of them."
        },
        {
          "tac": "· rw [singleton_same] at h",
          "h": "The focus dot here is not selecting a goal — it is <i>grouping</i>. <code>&lt;;&gt;</code> takes a single tactic on its right, so to hand it a two-tactic block you wrap the block in <code>·</code>. Inside, <code>rw … at h</code> rewrites in the hypothesis rather than the goal, turning <code>h</code> into <code>some v₁ = none</code> (respectively <code>some v₂ = none</code>)."
        },
        {
          "tac": "exact absurd h (by simp)",
          "h": "<code>@absurd : a → ¬a → b</code>: given a proof and a refutation, conclude anything. The refutation of <code>some v₁ = none</code> is supplied by a nested <code>by simp</code>, which knows that distinct constructors of <code>Option</code> are unequal. The result type <code>b</code> is inferred as <code>False</code>, the current goal."
        },
        {
          "tac": "· exact singleton_disjoint v₁ v₂",
          "h": "The <code>mpr</code> half. The hypothesis <code>l₁ ≠ l₂</code> is still to be introduced, but <code>singleton_disjoint v₁ v₂</code> is already a function expecting exactly that, so it <i>is</i> the proof. The implicit locations are determined by unification with the goal."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "singleton_disjoint — both branches",
          "start": "l₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\n⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)",
          "steps": [
            {
              "tac": "intro x",
              "state": "l₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\n⊢ Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none",
              "h": "The definition has unfolded and the location is fixed."
            },
            {
              "tac": "by_cases hx : x = l₁",
              "state": "case pos\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx : x = l₁\n⊢ Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none",
              "h": "First of the two goals. The header <code>case pos</code> is Lean telling you which branch of the decision you are in; <code>neg</code> is waiting behind it."
            },
            {
              "tac": "right",
              "state": "case pos\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx : x = l₁\n⊢ Heap.singleton l₂ v₂ x = none",
              "h": "The disjunction is gone and only the right side remains to prove."
            },
            {
              "tac": "have : x ≠ l₂ := by rw [hx]; exact hne",
              "state": "case pos\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx : x = l₁\nthis : x ≠ l₂\n⊢ Heap.singleton l₂ v₂ x = none",
              "h": "The anonymous <code>have</code> has added <code>this : x ≠ l₂</code>. The goal is untouched; only the context grew."
            },
            {
              "tac": "exact singleton_other l₂ x v₂ this",
              "h": "Closes the <code>pos</code> goal, and Lean moves to <code>neg</code>."
            },
            {
              "tac": "(the second bullet)",
              "state": "case neg\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx : ¬x = l₁\n⊢ Heap.singleton l₁ v₁ x = none ∨ Heap.singleton l₂ v₂ x = none",
              "h": "Note how <code>by_cases</code> writes the negative hypothesis: <code>¬x = l₁</code>, not <code>x ≠ l₁</code>. They are the same term; the printer prefers the explicit <code>¬</code>."
            },
            {
              "tac": "left",
              "state": "case neg\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx : ¬x = l₁\n⊢ Heap.singleton l₁ v₁ x = none",
              "h": "And <code>singleton_other l₁ x v₁ hx</code> finishes. <code>hne</code> was never used in this branch — non-aliasing only matters where the cells actually collide."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "singleton_disjoint_iff — the forward direction",
          "start": "l₁ l₂ : Loc\nv₁ v₂ : Val\n⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂) ↔ l₁ ≠ l₂",
          "steps": [
            {
              "tac": "constructor",
              "state": "case mp\nl₁ l₂ : Loc\nv₁ v₂ : Val\n⊢ (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂) → l₁ ≠ l₂",
              "h": "Two goals, <code>mp</code> and <code>mpr</code>. This is the first."
            },
            {
              "tac": "intro hd heq",
              "state": "case mp\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)\nheq : l₁ = l₂\n⊢ False",
              "h": "Two <code>intro</code>s where the statement shows only one arrow, because <code>l₁ ≠ l₂</code> unfolds to <code>l₁ = l₂ → False</code>. The goal <code>False</code> is the giveaway that you are now doing a proof by contradiction."
            },
            {
              "tac": "subst heq",
              "state": "case mp\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\n⊢ False",
              "h": "<code>l₂</code> is gone from the context entirely, and <code>hd</code> now says two singletons <i>at the same location</i> are disjoint. Everything after this is squeezing the contradiction out."
            },
            {
              "tac": "rcases hd l₁ with h | h",
              "state": "case mp.inl\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\nh : Heap.singleton l₁ v₁ l₁ = none\n⊢ False",
              "h": "The first of the two disjuncts. The case name <code>mp.inl</code> records the whole path: forward direction, left injection."
            },
            {
              "tac": "rw [singleton_same] at h",
              "state": "case mp.inl\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\nh : some v₁ = none\n⊢ False",
              "h": "The hypothesis is now visibly absurd. <code>exact absurd h (by simp)</code> closes it."
            },
            {
              "tac": "(the same block, on the other disjunct)",
              "state": "case mp.inr\nl₁ : Loc\nv₁ v₂ : Val\nhd : (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₁ v₂)\nh : Heap.singleton l₁ v₂ l₁ = none\n⊢ False",
              "h": "Identical in shape, with <code>v₂</code> for <code>v₁</code>. That the two goals are the same shape is exactly the licence to write <code>&lt;;&gt;</code> instead of two bullets."
            },
            {
              "tac": "(the mpr goal)",
              "state": "case mpr\nl₁ l₂ : Loc\nv₁ v₂ : Val\n⊢ l₁ ≠ l₂ → (Heap.singleton l₁ v₁).disjoint (Heap.singleton l₂ v₂)",
              "h": "Which is literally the type of <code>singleton_disjoint v₁ v₂</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The moral, in three lines",
          "items": [
            {
              "k": "Separation is a claim, not an observation",
              "h": "<code>Heap.disjoint (singleton l₁ v₁) (singleton l₂ v₂)</code> is not “these happen not to overlap”. It is a hypothesis you are handed, and the <code>mp</code> direction shows you can <i>cash it in</i> for <code>l₁ ≠ l₂</code>."
            },
            {
              "k": "That is where aliasing information comes from",
              "h": "In M4 the assertion <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂)</code> unfolds to a splitting of the heap into two singletons, and this lemma is what lets you conclude <code>l₁ ≠ l₂</code> from it — for free, with no side condition written anywhere in the specification. That theorem is <code>two_cells_distinct</code>, and after the destructuring its proof is one line: <code>exact (singleton_disjoint_iff v₁ v₂).mp hd</code>. M10 then gets <code>p ≠ p + 1</code> for a list node by instantiating it."
            },
            {
              "k": "Compare the alternative",
              "h": "In a Hoare logic without <code>∗</code>, non-aliasing has to be stated by hand in every precondition, and forgotten exactly once per program. Separation logic makes it a consequence of the syntax. This eight-line lemma is where that starts."
            }
          ]
        }
      ],
      "pitfall": "Argument order in <code>singleton_other (l x : Loc) (v : Val) (hne : x ≠ l)</code>. The heap’s own location comes first, the probed location second — so it is <code>singleton_other l₂ x v₂</code>, not <code>singleton_other x l₂ v₂</code>. Since <code>Loc</code> is <code>Nat</code>, both orders typecheck up to the last argument, and the error surfaces only at the disequality, pointing at <code>this</code>. Related: the disequality must read <code>x ≠ l₂</code>, matching the <code>if x = l</code> in the definition of <code>singleton</code>; if you have it the other way round, insert <code>Ne.symm</code>.",
      "variants": "Drop <code>hne</code> and the theorem is false, at exactly the point you would expect. Two singletons at the same location are never disjoint:<br><br><code>example : ¬ Heap.disjoint (Heap.singleton 0 1) (Heap.singleton 0 2) := by intro hd; rcases hd 0 with h | h &lt;;&gt; · rw [singleton_same] at h; exact absurd h (by simp)</code><br><br>Note that the values <code>1</code> and <code>2</code> play no role: <code>Heap.singleton 0 1</code> and <code>Heap.singleton 0 1</code> are not disjoint either. Disjointness is about domains, so equal values do not rescue it — which is precisely why <code>P ∗ P</code> fails and <code>P ∧ P</code> does not."
    },

    {
      "t": "sec",
      "s": "Exercises · union laws"
    },
    {
      "t": "p",
      "h": "First, three tiny lookup lemmas. They are not in the original syllabus; add them, because without them every later proof drowns in <code>match</code> expressions."
    },
    {
      "t": "code",
      "src": "theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  simp [Heap.union, hl]\n\ntheorem union_of_some {h₁ : Heap} (h₂ : Heap) {l : Loc} {v : Val} (hl : h₁ l = some v) :\n    Heap.union h₁ h₂ l = some v := by\n  simp [Heap.union, hl]\n\ntheorem union_eq_none {h₁ h₂ : Heap} {l : Loc} :\n    Heap.union h₁ h₂ l = none ↔ h₁ l = none ∧ h₂ l = none := by\n  constructor\n  · intro h\n    cases hl : h₁ l with\n    | none   => exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩\n    | some v => rw [union_of_some h₂ hl] at h; exact absurd h (by simp)\n  · intro ⟨ha, hb⟩\n    rw [union_of_none h₂ ha]; exact hb"
    },
    {
      "t": "p",
      "h": "These are the interface to <code>union</code>, in the same sense that <code>write_same</code> and <code>write_other</code> were the interface to <code>write</code>: after this point you should never see the word <code>match</code> again. Two details in their statements are worth a minute each."
    },
    {
      "t": "anat",
      "src": "theorem union_of_none {h₁ : Heap} (h₂ : Heap) {l : Loc} (hl : h₁ l = none) :\n    Heap.union h₁ h₂ l = h₂ l := by\n  simp [Heap.union, hl]",
      "parts": [
        {
          "m": "{h₁ : Heap} (h₂ : Heap) {l : Loc}",
          "h": "Braces mean <i>implicit</i>: Lean must infer the argument. <code>h₁</code> and <code>l</code> can be read off the type of <code>hl</code>, so they are implicit. <code>h₂</code> cannot — <code>hl</code> says nothing about it — so it is explicit. That is why every call site below reads <code>union_of_none h₂ hl</code>: one visible heap argument, then the equation. It looks arbitrary until you notice it is forced."
        },
        {
          "m": "simp [Heap.union, hl]",
          "h": "Two things in the simp set. <code>Heap.union</code> unfolds the definition, exposing the <code>match</code>. <code>hl : h₁ l = none</code> is used as a left-to-right rewrite rule, replacing the scrutinee <code>h₁ l</code> by the constructor <code>none</code> — at which point the <code>match</code> can finally reduce, to <code>h₂ l</code>."
        }
      ],
      "cap": "The pattern <i>unfold, rewrite the scrutinee to a constructor, let the match compute</i> is the whole trick, and it recurs in every proof in this section."
    },
    {
      "t": "p",
      "h": "It is worth seeing what the goal looks like in between. Unfolding alone leaves a stuck <code>match</code>:"
    },
    {
      "t": "state",
      "src": "h₁ h₂ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (match h₁ l with\n    | some v => some v\n    | none => h₂ l) =\n    h₂ l",
      "cap": "After <code>simp only [Heap.union]</code>. The match cannot fire because <code>h₁ l</code> is an opaque application, not a constructor. Supplying <code>hl</code> is what unsticks it."
    },
    {
      "t": "detail",
      "title": "<code>union_eq_none</code>, walked through",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "This is the only one of the three with a real proof, and it introduces two tactics you will meet again. Read it once; you will use its <code>.mp</code> and <code>.mpr</code> constantly."
        },
        {
          "t": "trace",
          "title": "union_eq_none",
          "steps": [
            {
              "tac": "constructor · intro h",
              "state": "case mp\nh₁ h₂ : Heap\nl : Loc\nh : h₁.union h₂ l = none\n⊢ h₁ l = none ∧ h₂ l = none",
              "h": "The forward direction. We know the union is undefined at <code>l</code> and must conclude both halves are."
            },
            {
              "tac": "cases hl : h₁ l with | none => …",
              "state": "case mp.none\nh₁ h₂ : Heap\nl : Loc\nh : h₁.union h₂ l = none\nhl : h₁ l = none\n⊢ none = none ∧ h₂ l = none",
              "h": "Look at what <code>cases hl : h₁ l</code> did to the <i>goal</i>: the occurrence of <code>h₁ l</code> was replaced by the constructor <code>none</code>, which is why the first conjunct is now <code>rfl</code>. It also saved the equation as <code>hl</code>, which is what lets you rewrite the hypothesis <code>h</code>."
            },
            {
              "tac": "exact ⟨rfl, by rwa [union_of_none h₂ hl] at h⟩",
              "h": "The pair: <code>rfl</code> for the first conjunct, and for the second, <code>rwa</code> — rewrite <code>h</code> using <code>union_of_none h₂ hl : Heap.union h₁ h₂ l = h₂ l</code>, turning <code>h</code> into <code>h₂ l = none</code>, then close the goal with it."
            },
            {
              "tac": "| some v => …",
              "state": "case mp.some\nh₁ h₂ : Heap\nl : Loc\nh : h₁.union h₂ l = none\nv : Val\nhl : h₁ l = some v\n⊢ some v = none ∧ h₂ l = none",
              "h": "The impossible branch. The goal itself is now absurd, but it is easier to refute the hypothesis."
            },
            {
              "tac": "rw [union_of_some h₂ hl] at h",
              "state": "case mp.some\nh₁ h₂ : Heap\nl : Loc\nv : Val\nh : some v = none\nhl : h₁ l = some v\n⊢ some v = none ∧ h₂ l = none",
              "h": "<code>h</code> is now nonsense, and <code>exact absurd h (by simp)</code> produces the goal out of it."
            },
            {
              "tac": "· intro ⟨ha, hb⟩",
              "state": "case mpr\nh₁ h₂ : Heap\nl : Loc\nha : h₁ l = none\nhb : h₂ l = none\n⊢ h₁.union h₂ l = none",
              "h": "The backward direction. Note the pattern in <code>intro</code>: the conjunction is destructured on the way in, so <code>ha</code> and <code>hb</code> appear directly."
            },
            {
              "tac": "rw [union_of_none h₂ ha]",
              "state": "case mpr\nh₁ h₂ : Heap\nl : Loc\nha : h₁ l = none\nhb : h₂ l = none\n⊢ h₂ l = none",
              "h": "And that is <code>hb</code>."
            }
          ],
          "done": "No goals."
        }
      ]
    },
    {
      "t": "ex",
      "id": "m2-4",
      "name": "union_empty_left / right",
      "hard": false,
      "why": "<code>Heap.empty</code> is the unit of the monoid. Note the asymmetry in the proofs: the left law is <code>rfl</code> pointwise because <code>union</code> is defined by matching on its <i>first</i> argument; the right law needs a case split.",
      "goal": "theorem union_empty_left  (h : Heap) : Heap.union Heap.empty h = h\ntheorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h",
      "hints": [
        "Both sides of both statements are heaps, i.e. functions, so both proofs open with <code>funext l</code>. After that you are comparing two <code>Option Val</code>s.",
        "For the left law, ask whether the <code>match</code> can compute. Its scrutinee is <code>Heap.empty l</code>, which unfolds to the constructor <code>none</code> — so it can, and the two sides become the same term.",
        "For the right law the scrutinee is <code>h l</code> with <code>h</code> a variable. Nothing reduces. You have to <i>make</i> it a constructor: <code>cases hl : h l with | none =&gt; … | some v =&gt; …</code>.",
        "In each branch the saved equation <code>hl</code> is exactly the hypothesis <code>union_of_none</code> / <code>union_of_some</code> wants. In the <code>none</code> branch you are left with <code>Heap.empty l = none</code>, which <i>is</i> <code>rfl</code>."
      ],
      "hint": "Left: <code>funext l; rfl</code>. Right: <code>funext l</code> then <code>cases hl : h l</code> and rewrite with <code>union_of_none</code> / <code>union_of_some</code>.",
      "sol": "theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by\n  funext l; rfl\n\ntheorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by\n  funext l\n  cases hl : h l with\n  | none   => rw [union_of_none Heap.empty hl]; rfl\n  | some v => rw [union_of_some Heap.empty hl]",
      "expl": "This asymmetry is a small lesson about definitional unfolding: a definition by pattern matching computes only when the scrutinee is a constructor. <code>Heap.empty l</code> reduces to <code>none</code> immediately; <code>h l</code> does not reduce at all until you case on it.",
      "walk": [
        {
          "tac": "funext l",
          "h": "First theorem. Reduces the equality of two heaps to their equality at an arbitrary location <code>l</code>. This is function extensionality, which in Lean is a theorem about <code>Eq</code>, not a definitional fact — hence a tactic rather than nothing."
        },
        {
          "tac": "rfl",
          "h": "Both sides are now definitionally the same term. Lean unfolds <code>Heap.union</code>, beta-reduces, unfolds <code>Heap.empty</code> to see the scrutinee is <code>none</code>, takes the second branch of the <code>match</code>, and arrives at <code>h l</code> on both sides. All of that is silent."
        },
        {
          "tac": "funext l",
          "h": "Second theorem, same opening move, completely different sequel."
        },
        {
          "tac": "cases hl : h l with",
          "h": "The scrutinee this time is <code>h l</code>, which is stuck. <code>cases</code> splits on the two constructors of <code>Option</code>, and the <code>hl :</code> prefix saves the defining equation in each branch. Without that prefix you would get the case split and lose the ability to rewrite — which is why the plain <code>cases h l</code> is almost never what you want here."
        },
        {
          "tac": "| none   => rw [union_of_none Heap.empty hl]",
          "h": "In this branch <code>hl : h l = none</code>. Rewriting turns the left-hand side <code>Heap.union h Heap.empty l</code> into <code>Heap.empty l</code>. Note that <code>cases</code> has already replaced <code>h l</code> by <code>none</code> on the right-hand side of the goal."
        },
        {
          "tac": "; rfl",
          "h": "Leaving <code>Heap.empty l = none</code>, which is true by unfolding. Two different uses of <code>rfl</code> in one exercise, both discharging a goal that no rewriting could reach."
        },
        {
          "tac": "| some v => rw [union_of_some Heap.empty hl]",
          "h": "Here <code>hl : h l = some v</code>, and one rewrite makes both sides <code>some v</code>. <code>rw</code> closes goals of the form <code>a = a</code> automatically, so no explicit <code>rfl</code> is needed — that is why this branch is one tactic and the other is two."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "Why one is rfl and the other is not",
          "start": "h : Heap\n⊢ Heap.empty.union h = h",
          "steps": [
            {
              "tac": "funext l",
              "state": "h : Heap\nl : Loc\n⊢ Heap.empty.union h l = h l",
              "h": "The left law. <code>rfl</code> closes this: the scrutinee <code>Heap.empty l</code> unfolds to a constructor and the match computes."
            },
            {
              "tac": "(second theorem) funext l",
              "state": "h : Heap\nl : Loc\n⊢ h.union Heap.empty l = h l",
              "h": "The right law, at the same point. It looks like the mirror image, and it is not: here the scrutinee is <code>h l</code>."
            },
            {
              "tac": "cases hl : h l with | none =>",
              "state": "case none\nh : Heap\nl : Loc\nhl : h l = none\n⊢ h.union Heap.empty l = none",
              "h": "<code>cases</code> replaced <code>h l</code> by <code>none</code> in the goal and saved <code>hl</code> for the left-hand side, which <code>cases</code> could not touch because <code>h l</code> is buried inside <code>Heap.union</code>."
            },
            {
              "tac": "rw [union_of_none Heap.empty hl]",
              "state": "case none\nh : Heap\nl : Loc\nhl : h l = none\n⊢ Heap.empty l = none",
              "h": "Closed by <code>rfl</code>."
            },
            {
              "tac": "(the some branch)",
              "state": "case some\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\n⊢ h.union Heap.empty l = some v",
              "h": "And <code>rw [union_of_some Heap.empty hl]</code> makes both sides <code>some v</code>, closing it."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "The tempting one-liner",
            "kind": "bad",
            "h": "It fails, and the error message is precise about why. This is not a defect of <code>rfl</code>; it is a fact about what <code>match</code> can compute.",
            "src": "example (h : Heap) : Heap.union h Heap.empty = h := by\n  funext l\n  rfl",
            "tag": "sketch"
          },
          "right": {
            "t": "What Lean says",
            "h": "The left-hand side is stuck on an application of a variable. No amount of unfolding will turn <code>h l</code> into a constructor, so the case split is unavoidable.",
            "src": "error: Tactic `rfl` failed: The left-hand side\n  h.union Heap.empty l\nis not definitionally equal to the right-hand side\n  h l\n\nh : Heap\nl : Loc\n⊢ h.union Heap.empty l = h l",
            "tag": "sketch"
          }
        },
        {
          "t": "detail",
          "title": "The left law does not need <code>funext</code> either",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Push the point one step further. The <code>funext l</code> in <code>union_empty_left</code> is doing no work at all — the equation between the two <i>heaps</i>, not merely between their values at a location, is already definitional:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem union_empty_left_rfl (h : Heap) : Heap.union Heap.empty h = h := rfl"
            },
            {
              "t": "p",
              "h": "Trace it: <code>Heap.union Heap.empty h</code> unfolds to <code>fun l =&gt; match Heap.empty l with | some v =&gt; some v | none =&gt; h l</code>; under the binder, <code>Heap.empty l</code> reduces to <code>none</code>, the match takes its second branch, and what is left is <code>fun l =&gt; h l</code>. That is not <i>syntactically</i> <code>h</code>, but Lean 4 has <b>eta for functions</b> as a definitional rule, so <code>fun l =&gt; h l</code> and <code>h</code> are the same term to the kernel. The corpus proof writes <code>funext l; rfl</code> anyway, so that the two unit laws line up on the page. Nothing forces it."
            },
            {
              "t": "p",
              "h": "This is not a curiosity. It is why the orientation slip in <code>splits_empty_left</code> (see the pitfall on that exercise) goes undetected: <code>Heap.union Heap.empty h = h</code> and <code>h = Heap.union Heap.empty h</code> are both definitionally <code>h = h</code>, so Lean accepts either proof for either goal. The right-handed version has no such escape hatch."
            }
          ]
        }
      ],
      "pitfall": "Reaching for <code>simp [Heap.union]</code> when <code>rfl</code> fails. It does not help. On the un-<code>funext</code>ed goal it reports <code>simp made no progress</code>; after <code>funext l</code> it unfolds the definition and hands back <code>⊢ (match h l with | some v =&gt; some v | none =&gt; Heap.empty l) = h l</code> — the <code>match</code> now written out in the goal, and no closer to reducing, because the scrutinee is still the opaque <code>h l</code>. The fix is always the same: case on the scrutinee first, with the <code>hl :</code> prefix so you keep the equation.",
      "variants": "Had <code>union</code> been defined by matching on its <i>second</i> argument, the two proofs would swap: the right unit law would be <code>rfl</code> and the left one would need the case split. Nothing mathematical changes; the asymmetry is entirely an artefact of which argument the definition inspects. Worth internalising, because the same asymmetry reappears in <code>union_assoc</code>, where the <code>h₁ l = some v</code> branch is one line and the <code>none</code> branch needs a nested split."
    },
    {
      "t": "ex",
      "id": "m2-5",
      "name": "union_assoc",
      "hard": false,
      "why": "<b>No disjointness hypothesis.</b> Left-biased union is associative on the nose, because “first defined value wins” is an associative rule. Worth pausing on: this is the reason the associativity of <code>∗</code> in M4 is only about bookkeeping, not about heaps.",
      "goal": "theorem union_assoc (h₁ h₂ h₃ : Heap) :\n    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃)",
      "hints": [
        "Think of the value at a fixed location as “the first of <code>h₁ l</code>, <code>h₂ l</code>, <code>h₃ l</code> that is <code>some</code>”. There are three regimes: <code>h₁</code> defined; <code>h₁</code> undefined and <code>h₂</code> defined; both undefined. Your proof will have exactly three leaves.",
        "<code>funext l</code>, then <code>cases hl : h₁ l</code>. The <code>some</code> regime is the easy one: both sides are <code>some v</code> after two rewrites, one of which is <code>union_of_some h₃ (union_of_some h₂ hl)</code> — a lemma applied to a lemma.",
        "In the <code>none</code> regime, the right-hand side collapses immediately to <code>Heap.union h₂ h₃ l</code>. Now case on <code>h₂ l</code>.",
        "The obstacle in both inner branches is the same: to rewrite the <i>outer</i> union on the left you need a fact about <code>Heap.union h₁ h₂ l</code>, and you only have facts about <code>h₁ l</code> and <code>h₂ l</code>. Manufacture it — <code>union_eq_none.mpr ⟨hl, hl2⟩</code> in the <code>none/none</code> leaf, and an explicit <code>have hu</code> in the <code>none/some</code> leaf."
      ],
      "hint": "<code>funext l</code>, case on <code>h₁ l</code>, and inside the <code>none</code> branch case on <code>h₂ l</code>. Three leaves.",
      "sol": "theorem union_assoc (h₁ h₂ h₃ : Heap) :\n    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by\n  funext l\n  cases hl : h₁ l with\n  | none =>\n      rw [union_of_none (Heap.union h₂ h₃) hl]\n      cases hl2 : h₂ l with\n      | none =>\n          rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]\n      | some v =>\n          have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2\n          rw [union_of_some h₃ hu, union_of_some h₃ hl2]\n  | some v =>\n      rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]",
      "expl": "Think of it as: “take the first of <code>h₁ l</code>, <code>h₂ l</code>, <code>h₃ l</code> that is <code>some</code>.” Both bracketings compute that. The Lean proof just walks the three cases and rewrites with the lookup lemmas. Note <code>union_eq_none.mpr ⟨hl, hl2⟩</code> in the middle branch: to rewrite the outer union you first have to know the inner one is <code>none</code>, which is exactly what <code>union_eq_none</code> gives you.",
      "walk": [
        {
          "tac": "funext l",
          "h": "Two heaps are equal iff they agree everywhere. Fix a location."
        },
        {
          "tac": "cases hl : h₁ l with",
          "h": "The outermost question: is the leftmost heap defined here? The saved equation <code>hl</code> is what every rewrite below consumes."
        },
        {
          "tac": "| none =>",
          "h": "First regime. <code>h₁</code> contributes nothing at <code>l</code>."
        },
        {
          "tac": "rw [union_of_none (Heap.union h₂ h₃) hl]",
          "h": "Rewrites the <i>right-hand side</i> of the goal: <code>Heap.union h₁ (Heap.union h₂ h₃) l</code> becomes <code>Heap.union h₂ h₃ l</code>. The explicit argument is the whole heap <code>Heap.union h₂ h₃</code>, because that is what plays the role of <code>h₂</code> in the lemma. Getting this argument wrong is the single most common failure in this proof."
        },
        {
          "tac": "cases hl2 : h₂ l with",
          "h": "Second question, asked only inside the first <code>none</code> branch: is the middle heap defined here?"
        },
        {
          "tac": "| none =>",
          "h": "Both <code>h₁</code> and <code>h₂</code> are undefined at <code>l</code>; the answer must be <code>h₃ l</code> on both sides."
        },
        {
          "tac": "rw [union_of_none h₃ (union_eq_none.mpr ⟨hl, hl2⟩), union_of_none h₃ hl2]",
          "h": "Two rewrites. The first attacks the left-hand side <code>Heap.union (Heap.union h₁ h₂) h₃ l</code>, and to do so it needs <code>Heap.union h₁ h₂ l = none</code> — supplied by <code>union_eq_none.mpr</code> applied to the pair of facts you have. The second turns the right-hand side <code>Heap.union h₂ h₃ l</code> into <code>h₃ l</code>. Both sides are now <code>h₃ l</code> and <code>rw</code> closes the goal."
        },
        {
          "tac": "| some v =>",
          "h": "<code>h₁</code> undefined, <code>h₂</code> defined. The answer is <code>some v</code> on both sides."
        },
        {
          "tac": "have hu : Heap.union h₁ h₂ l = some v := by rw [union_of_none h₂ hl]; exact hl2",
          "h": "A named intermediate fact, because <code>union_eq_none</code> only covers the <code>none</code> case and there is no <code>union_eq_some</code> lemma. Its own proof is two steps: rewrite <code>Heap.union h₁ h₂ l</code> to <code>h₂ l</code> using <code>hl</code>, then that is <code>hl2</code>."
        },
        {
          "tac": "rw [union_of_some h₃ hu, union_of_some h₃ hl2]",
          "h": "Left-hand side to <code>some v</code> using <code>hu</code>; right-hand side to <code>some v</code> using <code>hl2</code>. Done."
        },
        {
          "tac": "| some v =>",
          "h": "Third regime, back at the outer split: <code>h₁</code> is defined at <code>l</code>, so nothing else is ever consulted."
        },
        {
          "tac": "rw [union_of_some h₃ (union_of_some h₂ hl), union_of_some (Heap.union h₂ h₃) hl]",
          "h": "Note the nesting in the first argument: <code>union_of_some h₂ hl : Heap.union h₁ h₂ l = some v</code> is itself fed to <code>union_of_some h₃</code> to get a fact about the doubly-nested union. The second rewrite handles the right-hand side, where <code>h₁</code> is the outer left argument and the partner heap is <code>Heap.union h₂ h₃</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "union_assoc — the three leaves",
          "start": "h₁ h₂ h₃ : Heap\n⊢ (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃)",
          "steps": [
            {
              "tac": "funext l",
              "state": "h₁ h₂ h₃ : Heap\nl : Loc\n⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l",
              "h": "Pointwise. Note the printer’s bracketing: <code>(h₁.union h₂).union h₃</code> on the left, <code>h₁.union (h₂.union h₃)</code> on the right."
            },
            {
              "tac": "cases hl : h₁ l with | none =>",
              "state": "case none\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l",
              "h": "The goal is unchanged — <code>h₁ l</code> does not occur in it syntactically, it is buried inside the unions — but <code>hl</code> is now available."
            },
            {
              "tac": "rw [union_of_none (Heap.union h₂ h₃) hl]",
              "state": "case none\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l",
              "h": "Only the right-hand side moved. The left-hand side still has <code>h₁</code> buried two levels down, which is why it needs its own manufactured fact."
            },
            {
              "tac": "cases hl2 : h₂ l with | none =>",
              "state": "case none.none\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\nhl2 : h₂ l = none\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l",
              "h": "First leaf. The case name <code>none.none</code> records both decisions. Now <code>union_eq_none.mpr ⟨hl, hl2⟩</code> is exactly the fact <code>Heap.union h₁ h₂ l = none</code> that the left-hand side is waiting for."
            },
            {
              "tac": "| some v =>",
              "state": "case none.some\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\nv : Val\nhl2 : h₂ l = some v\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l",
              "h": "Second leaf. Same shape, but now the answer is <code>some v</code> rather than <code>h₃ l</code>."
            },
            {
              "tac": "have hu : Heap.union h₁ h₂ l = some v := …",
              "state": "case none.some\nh₁ h₂ h₃ : Heap\nl : Loc\nhl : h₁ l = none\nv : Val\nhl2 : h₂ l = some v\nhu : h₁.union h₂ l = some v\n⊢ (h₁.union h₂).union h₃ l = h₂.union h₃ l",
              "h": "<code>hu</code> is the missing rewrite rule for the left-hand side. Compare the previous leaf, where <code>union_eq_none.mpr</code> played the same role inline."
            },
            {
              "tac": "(the outer some branch)",
              "state": "case some\nh₁ h₂ h₃ : Heap\nl : Loc\nv : Val\nhl : h₁ l = some v\n⊢ (h₁.union h₂).union h₃ l = h₁.union (h₂.union h₃) l",
              "h": "Third leaf, and the shortest: one <code>rw</code> with two lemma applications turns both sides into <code>some v</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The mathematics underneath",
          "items": [
            {
              "k": "Both bracketings compute the same selector",
              "h": "At a fixed <code>l</code>, <code>(h₁ ∪ h₂) ∪ h₃</code> asks: is <code>h₁ ∪ h₂</code> defined? which asks: is <code>h₁</code> defined, else is <code>h₂</code>? And <code>h₁ ∪ (h₂ ∪ h₃)</code> asks: is <code>h₁</code> defined, else is <code>h₂ ∪ h₃</code>? Both are the function “first <code>some</code> in the list <code>[h₁ l, h₂ l, h₃ l]</code>”, and that function does not care how the list was bracketed."
            },
            {
              "k": "Which is why no hypothesis is needed",
              "h": "Associativity of “first defined wins” is unconditional. Overlap changes <i>which</i> value is selected, but it changes it the same way on both sides. Disjointness is needed only when you want to claim the bias is <i>invisible</i>, which is commutativity, not associativity."
            },
            {
              "k": "And why M4 is cheap",
              "h": "M4’s <code>star_assoc_left</code> has to re-bracket a splitting of a heap and produce new disjointness proofs. Its heap-equation obligation is this lemma, applied once, with no side conditions to discharge — the whole of it is <code>rw [hu₁, union_assoc]</code>. All the remaining work there is <code>disjoint_union_left</code> and <code>disjoint_union_right</code>."
            }
          ]
        }
      ],
      "pitfall": "Passing the wrong explicit heap to <code>union_of_none</code> / <code>union_of_some</code>. In the outer <code>none</code> branch the natural reflex is <code>rw [union_of_none h₃ hl]</code>, but <code>union_of_none h₃ hl</code> has type <code>Heap.union h₁ h₃ l = h₃ l</code> — a statement about a union that does not occur in the goal, so <code>rw</code> reports that it failed to find the pattern. Ask yourself, every time: <i>which</i> union am I rewriting, and what are its two arguments? On the left they are <code>Heap.union h₁ h₂</code> and <code>h₃</code>; on the right they are <code>h₁</code> and <code>Heap.union h₂ h₃</code>.",
      "variants": "There is no hypothesis to drop, which is itself the content. The comparison worth making is with a genuinely partial union — one that is undefined whenever the domains overlap. That operation is associative only in the guarded sense “whenever both sides are defined, they are equal”, and every use of associativity then carries a definedness obligation. Our total, biased version satisfies the unguarded equation, which is strictly stronger, and it is exactly that strength that makes <code>union_assoc</code> usable as a plain rewrite rule anywhere, with no context."
    },
    {
      "t": "ex",
      "id": "m2-6",
      "name": "union_comm",
      "hard": false,
      "why": "Commutativity is where disjointness is <i>needed</i> — and where the “partial” in partial commutative monoid earns its keep. Without <code>hd</code> the statement is false as soon as the heaps overlap.",
      "goal": "theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :\n    Heap.union h₁ h₂ = Heap.union h₂ h₁",
      "hints": [
        "<code>funext l</code>, and then use the hypothesis <i>at that location</i>. <code>hd l</code> is a disjunction; <code>rcases hd l with h | h</code> gives you the two cases.",
        "In each case one of the two heaps is known to be <code>none</code> at <code>l</code>, so <code>union_of_none</code> collapses one side of the equation. The other side is still a union whose first argument is opaque — so it still needs a case split.",
        "Watch the shape of the goal after the first rewrite. If you rewrote the left-hand side, the remaining union sits on the <i>right</i> of the equals sign, and your subsequent rewrites have to be aimed there.",
        "The fiddly leaf is <code>none</code>/<code>none</code>: both sides really are <code>none</code>, but Lean sees <code>none = h₁ l</code>. Two rewrites chained in one <code>rw</code>, the second being the hypothesis <code>h</code> itself, finish it."
      ],
      "hint": "<code>funext l</code>, then <code>rcases hd l</code>. In each branch one side is known to be <code>none</code>, so <code>union_of_none</code> collapses it; then case on the other heap.",
      "sol": "theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) :\n    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by\n  funext l\n  rcases hd l with h | h\n  · rw [union_of_none h₂ h]\n    cases hl : h₂ l with\n    | none   => rw [union_of_none h₁ hl, h]\n    | some v => rw [union_of_some h₁ hl]\n  · rw [union_of_none h₁ h]\n    cases hl : h₁ l with\n    | none   => rw [union_of_none h₂ hl]; exact h\n    | some v => rw [union_of_some h₂ hl]",
      "expl": "At each location, disjointness says at least one of the two heaps is undefined there. If <code>h₁ l = none</code>, then <code>union h₁ h₂ l = h₂ l</code>, and <code>union h₂ h₁ l</code> is <code>h₂ l</code> if that is <code>some</code>, or <code>h₁ l = none = h₂ l</code> if it is not. The proof is that sentence, mechanised."
      ,
      "walk": [
        {
          "tac": "funext l",
          "h": "Pointwise, as always."
        },
        {
          "tac": "rcases hd l with h | h",
          "h": "This is the only place the hypothesis is used, and it is used at a single location. Two goals, <code>inl</code> and <code>inr</code>. In the first, <code>h : h₁ l = none</code>; in the second, <code>h : h₂ l = none</code>. Reusing the name is deliberate: the two branches then read almost identically, with <code>h₁</code> and <code>h₂</code> swapped."
        },
        {
          "tac": "· rw [union_of_none h₂ h]",
          "h": "<code>h₁ l = none</code>, so the left-hand side <code>Heap.union h₁ h₂ l</code> becomes <code>h₂ l</code>. The goal is now <code>h₂ l = Heap.union h₂ h₁ l</code> — the unknown is on the right."
        },
        {
          "tac": "cases hl : h₂ l with",
          "h": "The remaining union has <code>h₂</code> as its first argument, so that is the scrutinee to split on."
        },
        {
          "tac": "| none   => rw [union_of_none h₁ hl, h]",
          "h": "Both heaps are undefined at <code>l</code>. <code>cases</code> has already turned the left-hand side into <code>none</code>; the first rewrite turns the right-hand side into <code>h₁ l</code>, leaving <code>none = h₁ l</code>; the second rewrite uses <code>h : h₁ l = none</code> to make it <code>none = none</code>, which <code>rw</code> closes."
        },
        {
          "tac": "| some v => rw [union_of_some h₁ hl]",
          "h": "<code>h₂</code> is defined at <code>l</code>. One rewrite makes the right-hand side <code>some v</code>, matching the left."
        },
        {
          "tac": "· rw [union_of_none h₁ h]",
          "h": "Second branch: now <code>h : h₂ l = none</code>, and it is the <i>right-hand</i> side <code>Heap.union h₂ h₁ l</code> that collapses, to <code>h₁ l</code>. The goal is <code>Heap.union h₁ h₂ l = h₁ l</code> — the unknown has moved to the left."
        },
        {
          "tac": "cases hl : h₁ l with",
          "h": "Split on the first argument of the surviving union, which is now <code>h₁</code>."
        },
        {
          "tac": "| none   => rw [union_of_none h₂ hl]; exact h",
          "h": "Left-hand side becomes <code>h₂ l</code>, and the goal is <code>h₂ l = none</code>, which is <code>h</code>. Note that this branch ends with <code>exact</code>, not with <code>rw</code> closing it — the mirror-image branch above ended with a second rewrite instead. The asymmetry is only in which side of the equation the leftover sits on."
        },
        {
          "tac": "| some v => rw [union_of_some h₂ hl]",
          "h": "And the last leaf: <code>h₁</code> defined, so the left-hand side is <code>some v</code>, matching the right."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "union_comm — four leaves, two of them nearly identical",
          "start": "h₁ h₂ : Heap\nhd : h₁.disjoint h₂\n⊢ h₁.union h₂ = h₂.union h₁",
          "steps": [
            {
              "tac": "funext l",
              "state": "h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\n⊢ h₁.union h₂ l = h₂.union h₁ l",
              "h": "Note that <code>hd</code> is still folded. It will be unfolded implicitly when we apply it to <code>l</code>."
            },
            {
              "tac": "rcases hd l with h | h",
              "state": "case inl\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\n⊢ h₁.union h₂ l = h₂.union h₁ l",
              "h": "The first branch. <code>hd</code> stays in context — you may use it again at another location if you need to, though here you never do."
            },
            {
              "tac": "rw [union_of_none h₂ h]",
              "state": "case inl\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\n⊢ h₂ l = h₂.union h₁ l",
              "h": "The left-hand side has collapsed. Everything remaining is about the right."
            },
            {
              "tac": "cases hl : h₂ l with | none =>",
              "state": "case inl.none\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\nhl : h₂ l = none\n⊢ none = h₂.union h₁ l",
              "h": "<code>cases</code> rewrote the exposed <code>h₂ l</code> on the left to <code>none</code>, but could not touch the copy buried inside the union on the right."
            },
            {
              "tac": "rw [union_of_none h₁ hl]",
              "state": "case inl.none\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\nhl : h₂ l = none\n⊢ none = h₁ l",
              "h": "Now the second element of the <code>rw</code> list, <code>h</code>, rewrites <code>h₁ l</code> to <code>none</code> and the goal closes."
            },
            {
              "tac": "(the inl.some leaf)",
              "state": "case inl.some\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₁ l = none\nv : Val\nhl : h₂ l = some v\n⊢ some v = h₂.union h₁ l",
              "h": "One rewrite with <code>union_of_some h₁ hl</code> and it is done."
            },
            {
              "tac": "(the second rcases branch)",
              "state": "case inr\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\n⊢ h₁.union h₂ l = h₂.union h₁ l",
              "h": "Same goal, different hypothesis. This is where reusing the name <code>h</code> pays: the branch below is the previous one with the roles exchanged."
            },
            {
              "tac": "rw [union_of_none h₁ h]",
              "state": "case inr\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\n⊢ h₁.union h₂ l = h₁ l",
              "h": "This time the <i>right</i>-hand side collapsed. The residual work is on the left, which is why this branch ends with <code>exact h</code> rather than a rewrite."
            },
            {
              "tac": "cases hl : h₁ l with | none => rw [union_of_none h₂ hl]",
              "state": "case inr.none\nh₁ h₂ : Heap\nhd : h₁.disjoint h₂\nl : Loc\nh : h₂ l = none\nhl : h₁ l = none\n⊢ h₂ l = none",
              "h": "Which is exactly <code>h</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "code",
          "tag": "illustration",
          "cap": "Two overlapping singletons. Drop <code>hd</code> and this is the counterexample.",
          "src": "example :\n    Heap.union (Heap.singleton 0 1) (Heap.singleton 0 2)\n      ≠ Heap.union (Heap.singleton 0 2) (Heap.singleton 0 1) := by\n  intro heq\n  have h0 : Heap.union (Heap.singleton 0 1) (Heap.singleton 0 2) 0\n          = Heap.union (Heap.singleton 0 2) (Heap.singleton 0 1) 0 := by rw [heq]\n  rw [union_of_some _ (singleton_same 0 1), union_of_some _ (singleton_same 0 2)] at h0\n  exact absurd h0 (by simp)"
        }
      ],
      "pitfall": "Copy-pasting the first <code>rcases</code> branch into the second. They look symmetric and they are not: in the first branch the rewrite lands on the left-hand side of the goal, in the second it lands on the right. Consequently the <code>none</code> leaf finishes with <code>rw [union_of_none h₁ hl, h]</code> in one branch and with <code>rw [union_of_none h₂ hl]; exact h</code> in the other. If you paste, <code>rw</code> will complain that it cannot find the pattern, and the message will look mysterious because the goal <i>reads</i> the same as the one you succeeded on. Read the pattern it printed rather than the goal: <code>union_of_none h₂ h</code> with <code>h : h₂ l = none</code> is a fact about <code>h₂.union h₂</code>, and a doubled heap name in an error message means you fed the lemma the wrong disjunct.",
      "variants": "Drop <code>hd</code> and the theorem is false — the <code>illustration</code> above is the witness. Take <code>h₁ = 0 ↦ 1</code> and <code>h₂ = 0 ↦ 2</code>: the left-biased union gives <code>some 1</code> one way round and <code>some 2</code> the other. Note how little overlap is needed: one location, and the two heaps need not even be singletons. This is the precise sense in which the monoid is <i>partial</i> — the operation is defined everywhere, but the commutative law is only claimed on the compatible pairs, and <code>Heap.disjoint</code> is the name of that compatibility relation."
    },
    {
      "t": "ex",
      "id": "m2-7",
      "name": "disjoint_union_left / right",
      "hard": false,
      "why": "These two are the workhorses of the entire course. Every time you re-bracket a separating conjunction you will be re-deriving disjointness proofs, and it will always be one of these.",
      "goal": "theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃\n\ntheorem disjoint_union_right {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃",
      "hints": [
        "<code>constructor</code> on the <code>↔</code>. In the forward direction the goal is a conjunction of two <code>∀</code>s, so you need to build a pair whose components are functions of a location.",
        "<code>refine ⟨fun l =&gt; ?_, fun l =&gt; ?_⟩</code> does that in one move: it commits to the pair and to the two lambdas, and leaves you two pointwise goals named <code>refine_1</code> and <code>refine_2</code>. Each of them has its own <code>l</code>.",
        "Both goals begin the same way: <code>rcases hd l with h | h</code>. In the <code>inr</code> case <code>h : h₃ l = none</code> already proves the right disjunct. In the <code>inl</code> case <code>h : Heap.union h₁ h₂ l = none</code> — and <code>union_eq_none.mp h</code> turns that into a pair, of which you want <code>.1</code> in the first goal and <code>.2</code> in the second.",
        "For the backward direction, <code>intro ⟨ha, hb⟩ l</code> destructures the conjunction and introduces the location in one tactic. Then case on <code>ha l</code>, and inside its <code>none</code> case on <code>hb l</code>, rebuilding with <code>union_eq_none.mpr</code>.",
        "Do not prove <code>disjoint_union_right</code> from scratch. It is the left version conjugated by <code>disjoint_symm</code>: symmetrise the input, apply the left lemma, symmetrise both outputs."
      ],
      "hint": "Prove the left one from <code>union_eq_none</code>; then get the right one for free by conjugating with <code>disjoint_symm</code>.",
      "sol": "theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint (Heap.union h₁ h₂) h₃ ↔ Heap.disjoint h₁ h₃ ∧ Heap.disjoint h₂ h₃ := by\n  constructor\n  · intro hd\n    refine ⟨fun l => ?_, fun l => ?_⟩\n    · rcases hd l with h | h\n      · exact Or.inl (union_eq_none.mp h).1\n      · exact Or.inr h\n    · rcases hd l with h | h\n      · exact Or.inl (union_eq_none.mp h).2\n      · exact Or.inr h\n  · intro ⟨ha, hb⟩ l\n    rcases ha l with h | h\n    · rcases hb l with h' | h'\n      · exact Or.inl (union_eq_none.mpr ⟨h, h'⟩)\n      · exact Or.inr h'\n    · exact Or.inr h\n\ntheorem disjoint_union_right {h₁ h₂ h₃ : Heap} :\n    Heap.disjoint h₁ (Heap.union h₂ h₃) ↔ Heap.disjoint h₁ h₂ ∧ Heap.disjoint h₁ h₃ := by\n  constructor\n  · intro hd\n    have h' := disjoint_union_left.mp (disjoint_symm hd)\n    exact ⟨disjoint_symm h'.1, disjoint_symm h'.2⟩\n  · intro ⟨ha, hb⟩\n    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)",
      "expl": "The <code>right</code> version is not proved from scratch: it is <code>left</code> sandwiched between two applications of <code>disjoint_symm</code>. Getting into the habit of deriving rather than reproving is what keeps a development of this kind from tripling in size.",
      "walk": [
        {
          "tac": "constructor",
          "h": "Splits the <code>↔</code> into <code>mp</code> and <code>mpr</code>."
        },
        {
          "tac": "· intro hd",
          "h": "Forward direction. <code>hd : Heap.disjoint (Heap.union h₁ h₂) h₃</code> — one disjointness fact to be split into two."
        },
        {
          "tac": "refine ⟨fun l => ?_, fun l => ?_⟩",
          "h": "The goal is <code>A ∧ B</code> where each conjunct is a <code>∀ l, …</code>. This one tactic supplies the pair <i>and</i> both lambdas, leaving two goals with <code>l</code> already introduced. Doing it as <code>constructor</code> then <code>intro l</code> twice works too, and takes three tactics instead of one."
        },
        {
          "tac": "· rcases hd l with h | h",
          "h": "First goal: <code>h₁ l = none ∨ h₃ l = none</code>. Instantiate the hypothesis at the same location and split its disjunction."
        },
        {
          "tac": "· exact Or.inl (union_eq_none.mp h).1",
          "h": "<code>h : Heap.union h₁ h₂ l = none</code>. <code>union_eq_none.mp h</code> has type <code>h₁ l = none ∧ h₂ l = none</code>; <code>.1</code> selects the half about <code>h₁</code>; <code>Or.inl</code> injects it as the left disjunct of the goal. Three operations, one line, no tactic state in between."
        },
        {
          "tac": "· exact Or.inr h",
          "h": "<code>h : h₃ l = none</code> is already the right disjunct. Nothing about the union is needed here at all."
        },
        {
          "tac": "· rcases hd l with h | h",
          "h": "Second goal: <code>h₂ l = none ∨ h₃ l = none</code>. Same opening."
        },
        {
          "tac": "· exact Or.inl (union_eq_none.mp h).2",
          "h": "Identical to before except for <code>.2</code>. This is the only difference between the two goals, and getting it wrong is the classic error here."
        },
        {
          "tac": "· exact Or.inr h",
          "h": "And the same right-disjunct case."
        },
        {
          "tac": "· intro ⟨ha, hb⟩ l",
          "h": "Backward direction. The pattern <code>⟨ha, hb⟩</code> takes the conjunction apart as it is introduced, and the trailing <code>l</code> then introduces the location of the goal <code>Heap.disjoint (Heap.union h₁ h₂) h₃</code> — three introductions in one tactic, two of which are invisible in the statement."
        },
        {
          "tac": "rcases ha l with h | h",
          "h": "Now <i>we</i> must decide which disjunct to prove, and that depends on the data. Start with what <code>h₁</code> does at <code>l</code>."
        },
        {
          "tac": "· rcases hb l with h' | h'",
          "h": "If <code>h₁ l = none</code>, whether the union is <code>none</code> still depends on <code>h₂</code>, so ask <code>hb</code> too. Note the primed name — <code>h</code> is taken."
        },
        {
          "tac": "· exact Or.inl (union_eq_none.mpr ⟨h, h'⟩)",
          "h": "Both halves undefined: rebuild the fact about the union with the <i>backward</i> direction of the same iff, feeding it the pair."
        },
        {
          "tac": "· exact Or.inr h'",
          "h": "<code>h₁ l = none</code> but <code>h₂ l</code> unknown; luckily <code>h' : h₃ l = none</code>, which settles it without touching the union."
        },
        {
          "tac": "· exact Or.inr h",
          "h": "And if <code>ha</code> already gave <code>h₃ l = none</code>, we are done immediately. Note the proof never needs to know anything about <code>h₂</code> in this branch."
        },
        {
          "tac": "constructor",
          "h": "Second theorem. Same skeleton, but nothing below is a fresh argument."
        },
        {
          "tac": "· intro hd",
          "h": "<code>hd : Heap.disjoint h₁ (Heap.union h₂ h₃)</code> — the union is on the <i>wrong side</i> for the lemma we have."
        },
        {
          "tac": "have h' := disjoint_union_left.mp (disjoint_symm hd)",
          "h": "So flip it. <code>disjoint_symm hd : Heap.disjoint (Heap.union h₂ h₃) h₁</code>, which is exactly the left-hand side of <code>disjoint_union_left</code> with <code>(h₂, h₃, h₁)</code> for <code>(h₁, h₂, h₃)</code>. The implicit arguments are found by unification; you never write them. <code>h' : Heap.disjoint h₂ h₁ ∧ Heap.disjoint h₃ h₁</code>."
        },
        {
          "tac": "exact ⟨disjoint_symm h'.1, disjoint_symm h'.2⟩",
          "h": "Flip both components back. Conjugation by an involution: <code>symm</code> in, lemma, <code>symm</code> out."
        },
        {
          "tac": "· intro ⟨ha, hb⟩",
          "h": "Backward direction. No <code>l</code> this time — the whole thing is done at the level of disjointness facts."
        },
        {
          "tac": "exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm ha, disjoint_symm hb⟩)",
          "h": "The same conjugation read right to left: symmetrise both inputs, apply the left lemma backwards, symmetrise the output. Four uses of one lemma and zero new reasoning."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "disjoint_union_left, forwards",
          "steps": [
            {
              "tac": "constructor · intro hd",
              "state": "case mp\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\n⊢ h₁.disjoint h₃ ∧ h₂.disjoint h₃",
              "h": "One fact in, two facts out. Nothing has been unfolded yet."
            },
            {
              "tac": "refine ⟨fun l => ?_, fun l => ?_⟩",
              "state": "case mp.refine_1\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₁ l = none ∨ h₃ l = none",
              "h": "The first of the two holes. Notice the goal is already unfolded and already has its <code>l</code>: <code>refine</code> did the pairing, the two lambdas, and the definitional unfolding all at once. The naming <code>refine_1</code> / <code>refine_2</code> comes from the two <code>?_</code>s in the order written."
            },
            {
              "tac": "rcases hd l with h | h",
              "state": "case mp.refine_1.inl\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\nh : h₁.union h₂ l = none\n⊢ h₁ l = none ∨ h₃ l = none",
              "h": "The interesting case: the union is undefined at <code>l</code>, and we must extract the fact about <code>h₁</code>. That extraction is <code>union_eq_none.mp</code>."
            },
            {
              "tac": "(the other disjunct)",
              "state": "case mp.refine_1.inr\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\nh : h₃ l = none\n⊢ h₁ l = none ∨ h₃ l = none",
              "h": "The dull case: <code>h</code> <i>is</i> the right disjunct."
            },
            {
              "tac": "(the second hole)",
              "state": "case mp.refine_2\nh₁ h₂ h₃ : Heap\nhd : (h₁.union h₂).disjoint h₃\nl : Loc\n⊢ h₂ l = none ∨ h₃ l = none",
              "h": "Identical in shape to <code>refine_1</code> with <code>h₂</code> for <code>h₁</code>, and handled identically except that you take <code>.2</code> of the pair instead of <code>.1</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "disjoint_union_left, backwards",
          "steps": [
            {
              "tac": "· intro ⟨ha, hb⟩ l",
              "state": "case mpr\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\n⊢ h₁.union h₂ l = none ∨ h₃ l = none",
              "h": "Three introductions from one tactic: the conjunction (destructured into <code>ha</code> and <code>hb</code>) and the location."
            },
            {
              "tac": "rcases ha l with h | h",
              "state": "case mpr.inl\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\nh : h₁ l = none\n⊢ h₁.union h₂ l = none ∨ h₃ l = none",
              "h": "Knowing <code>h₁ l = none</code> is not yet enough to say the union is <code>none</code> — the union also consults <code>h₂</code>."
            },
            {
              "tac": "rcases hb l with h' | h'",
              "state": "case mpr.inl.inl\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\nh : h₁ l = none\nh' : h₂ l = none\n⊢ h₁.union h₂ l = none ∨ h₃ l = none",
              "h": "Now it is. <code>union_eq_none.mpr ⟨h, h'⟩</code> assembles the left disjunct."
            },
            {
              "tac": "(the h' : h₃ l = none case)",
              "state": "case mpr.inl.inr\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\nh : h₁ l = none\nh' : h₃ l = none\n⊢ h₁.union h₂ l = none ∨ h₃ l = none",
              "h": "Shortcut: <code>h'</code> settles the right disjunct and the union is irrelevant."
            },
            {
              "tac": "(the outer inr case)",
              "state": "case mpr.inr\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₃\nhb : h₂.disjoint h₃\nl : Loc\nh : h₃ l = none\n⊢ h₁.union h₂ l = none ∨ h₃ l = none",
              "h": "Same shortcut, one level up. Three of the four leaves are one-liners; only <code>mpr.inl.inl</code> does any work."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "disjoint_union_right — derived, not reproved",
          "steps": [
            {
              "tac": "constructor · intro hd",
              "state": "case mp\nh₁ h₂ h₃ : Heap\nhd : h₁.disjoint (h₂.union h₃)\n⊢ h₁.disjoint h₂ ∧ h₁.disjoint h₃",
              "h": "The union is on the right; <code>disjoint_union_left</code> wants it on the left."
            },
            {
              "tac": "have h' := disjoint_union_left.mp (disjoint_symm hd)",
              "state": "case mp\nh₁ h₂ h₃ : Heap\nhd : h₁.disjoint (h₂.union h₃)\nh' : h₂.disjoint h₁ ∧ h₃.disjoint h₁\n⊢ h₁.disjoint h₂ ∧ h₁.disjoint h₃",
              "h": "Compare <code>h'</code> with the goal: they are the same pair with both components reversed. Two applications of <code>disjoint_symm</code> finish it. This one line is the entire proof of a theorem that would otherwise be a copy of the fifteen lines above."
            },
            {
              "tac": "(the mpr direction)",
              "state": "case mpr\nh₁ h₂ h₃ : Heap\nha : h₁.disjoint h₂\nhb : h₁.disjoint h₃\n⊢ h₁.disjoint (h₂.union h₃)",
              "h": "Same conjugation, run the other way: flip <code>ha</code> and <code>hb</code>, apply <code>disjoint_union_left.mpr</code>, flip the result."
            }
          ],
          "done": "No goals."
        }
      ],
      "pitfall": "Taking <code>.1</code> where you need <code>.2</code>. The two <code>refine</code> holes differ in exactly one character, and if you use <code>.1</code> in the second, Lean reports a mismatch between <code>h₁ l = none</code> and <code>h₂ l = none</code> buried inside an <code>Or.inl</code> — a message that points at the injection rather than the projection. When a proof is this compressed, read the goal first and the error second. A second trap: <code>union_eq_none</code> has all three of its arguments implicit, so <code>union_eq_none.mp h</code> silently unifies against whatever <code>h</code> is; if <code>h</code> is the wrong hypothesis you get a unification failure about heaps you did not mention.",
      "variants": "Both statements are genuine iffs, and both directions get used — often in the same proof. <code>splits_assoc</code> below uses <code>disjoint_union_left.mp</code> to take a coarse disjointness fact apart and <code>disjoint_union_right.mpr</code> to build a new one; M4’s <code>star_assoc_left</code> does the same two things, and <code>star_assoc_right</code> uses the mirror pair, <code>disjoint_union_right.mp</code> and <code>disjoint_union_left.mpr</code>. Between the four of them every direction of both iffs is load-bearing, so neither can be weakened to an implication.<br><br>Note also what is absent: no hypothesis relating <code>h₁</code> and <code>h₂</code> appears anywhere. The lemma is true of the total left-biased union with no compatibility assumption at all, which is what makes it safe to use as a rewriting <code>↔</code> in any context."
    },

    {
      "t": "sec",
      "s": "Exercises · splitting"
    },
    {
      "t": "p",
      "h": "<code>Heap.splits</code> packages a disjointness fact and a heap equation into one proposition. Everything in this section is therefore a matter of pairing and unpairing, plus one of the union laws you have already proved. Nothing new happens mathematically. What is worth the two exercises is that these two proofs are, line for line, the proofs you will write in M4: <code>star_comm</code> is <code>splits_comm</code> with two heaps and two assertion facts added to the tuple, and <code>star_assoc_left</code> is <code>splits_assoc</code> with the same addition. Getting the shape into your fingers here is the point."
    },
    {
      "t": "ex",
      "id": "m2-8",
      "name": "splits_empty_left / splits_comm",
      "hard": false,
      "why": "These are M4’s <code>star_emp_left_intro</code> (<code>P ⊢ emp ∗ P</code>) and <code>star_comm</code> (<code>P ∗ Q ⊢ Q ∗ P</code>) with all the assertion machinery deleted. The resemblance is not an analogy: <code>star_comm</code>’s proof is <code>exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩</code>, which is the tuple below with two heaps and two assertion facts inserted. They also drill the one thing that trips people up about <code>splits</code>: the direction of its equation.",
      "goal": "theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h\ntheorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁",
      "hints": [
        "<code>Heap.splits whole left right</code> is a conjunction, so a proof is a pair <code>⟨_, _⟩</code> and using one means taking a pair apart. Neither theorem needs a case analysis on anything.",
        "For <code>splits_empty_left</code> the two components are <code>disjoint_empty_left h</code> and a proof of <code>h = Heap.union Heap.empty h</code>. You have <code>union_empty_left h</code>, whose equation points the other way. <code>Eq.symm</code>, written <code>.symm</code>, fixes it.",
        "For <code>splits_comm</code>, <code>intro ⟨hd, he⟩</code> introduces the hypothesis already destructured: <code>hd</code> the disjointness, <code>he : h = Heap.union h₁ h₂</code>.",
        "The second component of the answer is <code>h = Heap.union h₂ h₁</code>. Rewrite with <code>he</code> to make the goal <code>Heap.union h₁ h₂ = Heap.union h₂ h₁</code>, which is <code>union_comm hd</code> — and note that <code>hd</code>, not <code>disjoint_symm hd</code>, is the right argument there."
      ],
      "hint": "Both are direct consequences of the lemmas you already have.",
      "sol": "theorem splits_empty_left (h : Heap) : Heap.splits h Heap.empty h :=\n  ⟨disjoint_empty_left h, (union_empty_left h).symm⟩\n\ntheorem splits_comm {h h₁ h₂ : Heap} : Heap.splits h h₁ h₂ → Heap.splits h h₂ h₁ := by\n  intro ⟨hd, he⟩\n  exact ⟨disjoint_symm hd, by rw [he, union_comm hd]⟩",
      "expl": "Both proofs are pairing. <code>splits_empty_left</code> is a term: the empty heap is disjoint from everything, and it is a left unit — with the equation turned round, because <code>splits</code> states it as <i>whole = union of parts</i>. <code>splits_comm</code> takes the pair apart and rebuilds it with <code>disjoint_symm</code> on the first component and <code>union_comm</code> on the second.",
      "walk": [
        {
          "tac": "⟨disjoint_empty_left h, …⟩",
          "h": "First theorem, given as a term. The anonymous constructor builds the conjunction; the first component is exactly the lemma from exercise 2."
        },
        {
          "tac": "(union_empty_left h).symm",
          "h": "<code>union_empty_left h : Heap.union Heap.empty h = h</code>, but <code>splits</code> asks for <code>h = Heap.union Heap.empty h</code>. <code>.symm</code> is <code>Eq.symm</code> found by dot notation on the head constant <code>Eq</code>. Forgetting it is the most common failure in this exercise."
        },
        {
          "tac": "intro ⟨hd, he⟩",
          "h": "Second theorem. The hypothesis <code>Heap.splits h h₁ h₂</code> is introduced and destructured in the same breath, giving <code>hd : Heap.disjoint h₁ h₂</code> and <code>he : h = Heap.union h₁ h₂</code>. Writing <code>intro hs</code> then <code>obtain ⟨hd, he⟩ := hs</code> is the same thing in two steps."
        },
        {
          "tac": "exact ⟨disjoint_symm hd, …⟩",
          "h": "Build the answer pair. The first component is symmetry of disjointness — exercise 1, cashed in."
        },
        {
          "tac": "by rw [he, union_comm hd]",
          "h": "A nested tactic block inside a term. The goal there is <code>h = Heap.union h₂ h₁</code>; <code>rw [he]</code> replaces <code>h</code> by <code>Heap.union h₁ h₂</code>, and <code>rw [union_comm hd]</code> rewrites that to <code>Heap.union h₂ h₁</code>, leaving <code>a = a</code>, which <code>rw</code> closes. Note that <code>union_comm hd</code> is used left-to-right, so <code>hd</code> is the disjointness of the <i>original</i> pair, not the flipped one."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "splits_comm, with the nested `by` spelled out as tactics",
          "start": "h h₁ h₂ : Heap\n⊢ h.splits h₁ h₂ → h.splits h₂ h₁",
          "steps": [
            {
              "tac": "intro ⟨hd, he⟩",
              "state": "h h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhe : h = h₁.union h₂\n⊢ h.splits h₂ h₁",
              "h": "The conjunction never appears as such: <code>intro</code> with a pattern splits it on arrival. Two hypotheses, and the goal is still folded."
            },
            {
              "tac": "refine ⟨disjoint_symm hd, ?_⟩",
              "state": "h h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhe : h = h₁.union h₂\n⊢ h = h₂.union h₁",
              "h": "Supplying the first component unfolds <code>splits</code> and leaves the heap equation. This is what the <code>by</code> block in the real proof is proving."
            },
            {
              "tac": "rw [he]",
              "state": "h h₁ h₂ : Heap\nhd : h₁.disjoint h₂\nhe : h = h₁.union h₂\n⊢ h₁.union h₂ = h₂.union h₁",
              "h": "And this is literally the statement of <code>union_comm hd</code>. The rest is one rewrite."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why <code>splits</code> states the equation as <code>whole = union left right</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Because that is the direction you consume it in. In M4 you will hold a heap <code>h</code> and a proof that it splits, and you will want to <i>replace</i> <code>h</code> by the union — that is <code>rw [he]</code>, left to right. Had the equation been written the other way you would spend the whole course typing <code>rw [← he]</code>."
            },
            {
              "t": "p",
              "h": "The cost is that the unit laws come out of M2 pointing the wrong way. You pay it every time you build a splitting one of whose halves is empty — <code>(union_empty_left _).symm</code> and <code>(union_empty_right _).symm</code> occur nine times between here and M10, in <code>splits_empty_left</code>, in M4’s <code>star_emp_left_intro</code> and <code>star_pure_right</code>, in M7’s <code>hoare_load</code>, and in M10’s concrete list. Nine appended <code>.symm</code>s against a course-long supply of <code>rw [← he]</code>: the trade is worth it."
            }
          ]
        }
      ],
      "pitfall": "Forgetting the <code>.symm</code> — and getting away with it, which is worse. <code>⟨disjoint_empty_left h, union_empty_left h⟩</code> is accepted, even though <code>union_empty_left h : Heap.union Heap.empty h = h</code> and the goal wants the equation the other way round. It is accepted because <code>Heap.union Heap.empty h</code> is <i>definitionally</i> <code>h</code> (see the aside under <code>union_empty_left</code>), so the two propositions are the same proposition up to unfolding. The habit that builds is wrong. Try the same omission on the mirror-image statement and Lean is unforgiving:<br><br><code>example (h : Heap) : Heap.splits h h Heap.empty := ⟨disjoint_empty_right h, union_empty_right h⟩</code><br><br><code>error: Application type mismatch: The argument union_empty_right h has type h.union Heap.empty = h but is expected to have type h = h.union Heap.empty</code><br><br>Whenever a component of a <code>splits</code> pair is rejected for no visible reason, check the orientation of the equation before anything else.",
      "variants": "The right-handed unit law, <code>Heap.splits h h Heap.empty</code>, is proved the same way from <code>disjoint_empty_right</code> and <code>(union_empty_right h).symm</code> — but recall that <code>union_empty_right</code> was the one that needed a case split, so the “symmetric” statement is genuinely more expensive to establish.<br><br>As for <code>splits_comm</code>: its content is exactly <code>union_comm</code>, so it inherits that lemma’s dependence on disjointness. There is no version of <code>splits_comm</code> without <code>hd</code>, because <code>hd</code> is part of what <code>splits</code> asserts — the relation was designed so that the hypothesis is always in your hand when you need it. That is the payoff for bundling."
    },
    {
      "t": "ex",
      "id": "m2-9",
      "name": "splits_assoc",
      "hard": true,
      "why": "This is the associativity of <code>∗</code>, stripped of all assertion machinery. Prove it once here and M4’s <code>star_assoc</code> becomes bookkeeping.",
      "goal": "theorem splits_assoc {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR",
      "hints": [
        "Both hypotheses are conjunctions. <code>obtain ⟨hd₁, he₁⟩ := h1</code> and the same for <code>h2</code> put four facts in your context: two disjointness proofs and two heap equations.",
        "<code>he₂ : hPQ = Heap.union hP hQ</code> has a local variable on the left, so <code>subst he₂</code> eliminates <code>hPQ</code> entirely. Afterwards <code>hd₁</code> and <code>he₁</code> talk about <code>Heap.union hP hQ</code> directly, which is what the union lemmas can see.",
        "Now <code>hd₁ : Heap.disjoint (Heap.union hP hQ) hR</code> is precisely the left-hand side of <code>disjoint_union_left</code>. <code>obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁</code> gives you <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code> separately.",
        "The witness for the existential is <code>Heap.union hQ hR</code>. To show <code>hP</code> is disjoint from it you need <code>disjoint_union_right.mpr</code> applied to the pair <code>⟨hd₂, hPR⟩</code>. The second <code>splits</code> is <code>⟨hQR', rfl⟩</code> — <code>rfl</code>, because you chose the witness to be syntactically that union.",
        "Assemble it all with one <code>refine</code>, leaving <code>?_</code> for the single genuine heap equation, and finish with <code>rw [he₁, union_assoc]</code>."
      ],
      "hint": "Substitute <code>hPQ = hP ∪ hQ</code>, then use <code>disjoint_union_left</code> to split <code>hd₁</code> into <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code>. The witness is <code>hQ ∪ hR</code>, and its disjointness from <code>hP</code> comes from <code>disjoint_union_right</code>.",
      "sol": "theorem splits_assoc {h hPQ hP hQ hR : Heap}\n    (h1 : Heap.splits h hPQ hR) (h2 : Heap.splits hPQ hP hQ) :\n    ∃ hQR, Heap.splits h hP hQR ∧ Heap.splits hQR hQ hR := by\n  obtain ⟨hd₁, he₁⟩ := h1\n  obtain ⟨hd₂, he₂⟩ := h2\n  subst he₂\n  obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁\n  refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩\n  rw [he₁, union_assoc]",
      "expl": "Read the two <code>disjoint_union_*</code> uses as the real content. From <code>(hP ∪ hQ) ⊥ hR</code> you extract both <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code>; combined with the given <code>hP ⊥ hQ</code> you can assemble <code>hP ⊥ (hQ ∪ hR)</code>. The heap equation itself is one <code>union_assoc</code>. Everything hard about associativity of <code>∗</code> is in these three lines.",
      "walk": [
        {
          "tac": "obtain ⟨hd₁, he₁⟩ := h1",
          "h": "Unpack the outer splitting: <code>hd₁ : Heap.disjoint hPQ hR</code> and <code>he₁ : h = Heap.union hPQ hR</code>. <code>obtain</code> is <code>rcases</code> with a single pattern; it consumes <code>h1</code> and replaces it by its two components."
        },
        {
          "tac": "obtain ⟨hd₂, he₂⟩ := h2",
          "h": "And the inner one: <code>hd₂ : Heap.disjoint hP hQ</code>, <code>he₂ : hPQ = Heap.union hP hQ</code>."
        },
        {
          "tac": "subst he₂",
          "h": "The pivotal step. <code>hPQ</code> is a variable, so it can be eliminated: every occurrence, in <code>hd₁</code> and in <code>he₁</code>, becomes <code>Heap.union hP hQ</code>. Watch <code>hPQ</code> vanish from the context in the trace. <code>rw [he₂] at hd₁ he₁</code> would rewrite the same two hypotheses and the proof would still go through — but <code>hPQ</code> and <code>he₂</code> would both survive in the context, referring to nothing you can still use. <code>subst</code> is the version that leaves no residue."
        },
        {
          "tac": "obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁",
          "h": "The first of the two real steps. <code>hd₁</code> now has exactly the shape <code>disjoint_union_left</code> expects, and its forward direction hands you <code>hPR : Heap.disjoint hP hR</code> and <code>hQR' : Heap.disjoint hQ hR</code>. This is the moment the given bracketing is dismantled."
        },
        {
          "tac": "refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩",
          "h": "One tactic doing four things. The witness <code>Heap.union hQ hR</code>; then the first <code>splits</code>, whose disjointness component is the second real step — <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩ : Heap.disjoint hP (Heap.union hQ hR)</code>, built from the inner disjointness you were given and the one you just extracted; then <code>?_</code> for its heap equation; then the second <code>splits</code>, which is <code>⟨hQR', rfl⟩</code> outright."
        },
        {
          "tac": "rw [he₁, union_assoc]",
          "h": "The only goal left is <code>h = Heap.union hP (Heap.union hQ hR)</code>. <code>rw [he₁]</code> replaces <code>h</code> by <code>Heap.union (Heap.union hP hQ) hR</code>, and then <code>union_assoc</code> rewrites left-to-right into the right-bracketed form, leaving <code>a = a</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "splits_assoc, tactic by tactic",
          "start": "h hPQ hP hQ hR : Heap\nh1 : h.splits hPQ hR\nh2 : hPQ.splits hP hQ\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR",
          "steps": [
            {
              "tac": "obtain ⟨hd₁, he₁⟩ := h1  /  obtain ⟨hd₂, he₂⟩ := h2",
              "state": "h hPQ hP hQ hR : Heap\nhd₁ : hPQ.disjoint hR\nhe₁ : h = hPQ.union hR\nhd₂ : hP.disjoint hQ\nhe₂ : hPQ = hP.union hQ\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR",
              "h": "Four facts, one goal. Everything from here on is combinatorics on these four."
            },
            {
              "tac": "subst he₂",
              "state": "h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR",
              "h": "<code>hPQ</code> is gone from the variable list, and <code>hd₁</code> and <code>he₁</code> now speak in terms of <code>hP</code> and <code>hQ</code>. Compare with the previous state: this is the whole reason to prefer <code>subst</code> over <code>rw … at</code>."
            },
            {
              "tac": "obtain ⟨hPR, hQR'⟩ := disjoint_union_left.mp hd₁",
              "state": "h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR' : hQ.disjoint hR\n⊢ ∃ hQR, h.splits hP hQR ∧ hQR.splits hQ hR",
              "h": "Three pairwise disjointness facts are now available: <code>hP ⊥ hQ</code>, <code>hP ⊥ hR</code>, <code>hQ ⊥ hR</code>. That is exactly the information content of a three-way splitting, and it is bracketing-independent — which is why re-bracketing is possible at all."
            },
            {
              "tac": "refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩",
              "state": "h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR' : hQ.disjoint hR\n⊢ h = hP.union (hQ.union hR)",
              "h": "One goal survives: the heap equation. Every disjointness obligation was discharged inline."
            },
            {
              "tac": "rw [he₁]",
              "state": "h hP hQ hR : Heap\nhd₂ : hP.disjoint hQ\nhd₁ : (hP.union hQ).disjoint hR\nhe₁ : h = (hP.union hQ).union hR\nhPR : hP.disjoint hR\nhQR' : hQ.disjoint hR\n⊢ (hP.union hQ).union hR = hP.union (hQ.union hR)",
              "h": "Which is <code>union_assoc hP hQ hR</code>, verbatim. The final rewrite closes it."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why that <code>⟨…⟩</code> has three components and not two",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The goal is <code>∃ hQR, A ∧ B</code>. <code>Exists.intro</code> takes two arguments — a witness and a proof — so you would expect <code>⟨witness, proof⟩</code>. The <code>refine</code> supplies three things. This is the anonymous constructor’s one piece of magic: <b>surplus components are re-nested into the last field</b>. <code>⟨a, b, c⟩</code> elaborates as <code>⟨a, ⟨b, c⟩⟩</code>, <code>⟨a, b, c, d⟩</code> as <code>⟨a, ⟨b, ⟨c, d⟩⟩⟩</code>, and so on. Both of these are accepted here:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "refine ⟨Heap.union hQ hR, ⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩\n\nrefine ⟨Heap.union hQ hR, ⟨⟨disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_⟩, ⟨hQR', rfl⟩⟩⟩"
            },
            {
              "t": "p",
              "h": "The second is what the first means. Note that the re-nesting is only ever to the <i>right</i>, so it flattens a right-leaning chain and nothing else. The inner <code>⟨…, ?_⟩</code> and <code>⟨hQR', rfl⟩</code> keep their brackets because the tree there is <code>(A₁ ∧ A₂) ∧ (B₁ ∧ B₂)</code> — left-leaning at the top. Flatten those too and it breaks:"
            },
            {
              "t": "cmp",
              "left": {
                "t": "Flattening one level too far",
                "kind": "bad",
                "h": "Five components for <code>∃ hQR, (A₁ ∧ A₂) ∧ (B₁ ∧ B₂)</code>.",
                "src": "refine ⟨Heap.union hQ hR, disjoint_union_right.mpr ⟨hd₂, hPR⟩, ?_, hQR', rfl⟩",
                "tag": "sketch"
              },
              "right": {
                "t": "What Lean says",
                "h": "The right-nesting put the disjointness proof where a whole <code>Heap.splits</code> was expected.",
                "src": "error: Application type mismatch: The argument\n  disjoint_union_right.mpr ⟨hd₂, hPR⟩\nhas type\n  hP.disjoint (hQ.union hR)\nbut is expected to have type\n  h.splits hP (hQ.union hR)\nin the application\n  And.intro (disjoint_union_right.mpr ⟨hd₂, hPR⟩)",
                "tag": "sketch"
              }
            },
            {
              "t": "p",
              "h": "One more thing is happening silently. <code>Heap.splits h hP hQR</code> is a <code>def</code>, not a structure — <code>⟨_, _⟩</code> works on it only because the elaborator reduces the expected type to weak head normal form first, finds <code>And</code>, and uses <code>And.intro</code>. Same mechanism as <code>intro l</code> seeing the <code>∀</code> inside <code>Heap.disjoint</code>. In M4 the definition of <code>∗</code> is one long right-leaning chain <code>∃ h₁ h₂, _ ∧ _ ∧ _ ∧ _</code>, so there the flattening does apply all the way down and you write six components in a row."
            }
          ]
        },
        {
          "t": "steps",
          "title": "The argument, without Lean",
          "items": [
            {
              "k": "Given",
              "h": "<code>h = (hP ∪ hQ) ∪ hR</code>, with <code>hP ⊥ hQ</code> and <code>(hP ∪ hQ) ⊥ hR</code>."
            },
            {
              "k": "Decompose the coarse disjointness",
              "h": "<code>(hP ∪ hQ) ⊥ hR</code> gives <code>hP ⊥ hR</code> and <code>hQ ⊥ hR</code>. This is <code>disjoint_union_left</code>, forwards. You now have all three pairwise facts."
            },
            {
              "k": "Recompose it the other way",
              "h": "<code>hP ⊥ hQ</code> and <code>hP ⊥ hR</code> give <code>hP ⊥ (hQ ∪ hR)</code>. This is <code>disjoint_union_right</code>, backwards. The two lemmas are used in opposite directions, which is why both had to be iffs."
            },
            {
              "k": "Move the brackets",
              "h": "<code>(hP ∪ hQ) ∪ hR = hP ∪ (hQ ∪ hR)</code>, unconditionally. This is where <code>union_assoc</code>’s lack of hypotheses pays off: no extra disjointness obligation appears at the very step that changes the shape."
            },
            {
              "k": "What M4 adds",
              "h": "Two more binders (<code>σ</code> and <code>h</code>) and three assertion facts to carry. Nothing else: <code>star_assoc_left</code>’s proof is <code>subst</code>, <code>obtain ⟨hPR, hQR⟩ := disjoint_union_left.mp hd₁</code>, a <code>refine</code> with <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code> in it, and <code>rw [hu₁, union_assoc]</code> — the five lines below, with <code>hp</code>, <code>hq</code>, <code>hr</code> threaded through. That is the sense in which it is bookkeeping."
            }
          ]
        }
      ],
      "pitfall": "Expecting <code>rfl</code> to work for the second <code>splits</code> if you pick a different witness. <code>⟨hQR', rfl⟩</code> proves <code>Heap.splits (Heap.union hQ hR) hQ hR</code> only because the witness you supplied is <i>syntactically</i> <code>Heap.union hQ hR</code>; a propositionally equal but differently written witness (say, obtained by rewriting first) leaves <code>rfl</code> failing with two sides that print identically after unfolding. Choose the witness to make the equation reflexive and put all the real work in the <code>?_</code>.<br><br>The other trap is the order of the pair fed to <code>disjoint_union_right.mpr</code>. It wants <code>⟨hP ⊥ hQ, hP ⊥ hR⟩</code> — the two halves in the order they appear in <code>Heap.union hQ hR</code> — and you have two disjointness facts about <code>hP</code> lying around, so <code>⟨hPR, hd₂⟩</code> is an easy slip. Lean catches it, but the message names the <i>first</i> component:<br><br><code>error: Application type mismatch: The argument hPR has type hP.disjoint hR but is expected to have type hP.disjoint hQ</code><br><br>which reads as if <code>hPR</code> were wrong rather than merely in the wrong seat.",
      "variants": "Drop <code>hd₂</code> — that is, keep <code>hPQ = hP ∪ hQ</code> but not <code>hP ⊥ hQ</code> — and the theorem is false. Take <code>hP = 0 ↦ 1</code>, <code>hQ = 0 ↦ 2</code>, <code>hR = Heap.empty</code>. Then <code>hPQ = hP ∪ hQ = 0 ↦ 1</code> by left bias, <code>h = hPQ ∪ hR = 0 ↦ 1</code>, and <code>Heap.splits h hPQ hR</code> holds outright. But the conclusion fails: the second component forces <code>hQR = hQ ∪ hR = 0 ↦ 2</code>, and then <code>Heap.splits h hP hQR</code> demands <code>hP ⊥ hQR</code>, i.e. that <code>0 ↦ 1</code> and <code>0 ↦ 2</code> be disjoint. They are not. So <code>hd₂</code> is load-bearing, and it enters through exactly one place: the <code>disjoint_union_right.mpr ⟨hd₂, hPR⟩</code> in the <code>refine</code>.<br><br>Reversing the statement — going from <code>splits h hP hQR</code> and <code>splits hQR hQ hR</code> to a left-bracketed splitting — is the mirror image: swap the roles of <code>disjoint_union_left</code> and <code>disjoint_union_right</code> and use <code>union_assoc</code> right-to-left with <code>rw [← union_assoc]</code>."
    },

    {
      "t": "h4",
      "s": "What you can now forget"
    },
    {
      "t": "p",
      "h": "From here on, <code>Heap.union</code> is used only through the lemmas in the table, and <code>match</code> should not appear in any proof you write again. If you find yourself unfolding <code>Heap.union</code> after this chapter, the missing lemma is almost always <code>union_of_none</code>, <code>union_of_some</code>, or <code>union_eq_none</code>."
    },
    {
      "t": "tbl",
      "head": ["When you need to…", "Reach for"],
      "rows": [
        ["evaluate a union where the left heap is undefined", "<code>union_of_none h₂ hl</code>"],
        ["evaluate a union where the left heap is defined", "<code>union_of_some h₂ hl</code>"],
        ["know that a union is undefined at a point", "<code>union_eq_none</code> (both directions)"],
        ["re-bracket", "<code>union_assoc</code> — no side condition"],
        ["swap two disjoint heaps", "<code>union_comm hd</code>"],
        ["split a disjointness fact", "<code>disjoint_union_left.mp</code> / <code>disjoint_union_right.mp</code>"],
        ["build a disjointness fact", "<code>disjoint_union_left.mpr</code> / <code>disjoint_union_right.mpr</code>"],
        ["flip a splitting", "<code>splits_comm</code>"],
        ["re-associate a splitting", "<code>splits_assoc</code>"]
      ]
    },
    {
      "t": "p",
      "h": "Next, M3 leaves heaps alone for a chapter and builds the assertion language on top of them: <code>Assertion := Store → Heap → Prop</code>, entailment, and the two heap-aware assertions <code>emp</code> and <code>l ↦ v</code>. Then M4 defines <code>∗</code> by quantifying over <code>Heap.splits</code>, at which point every theorem in this chapter reappears wearing two extra binders."
    },
    {
      "t": "dod",
      "h": "You have proved that <code>(Heap, union, empty, disjoint)</code> is a partial commutative monoid — and you can now forget the definitions and work with the laws."
    }
  ]
});
