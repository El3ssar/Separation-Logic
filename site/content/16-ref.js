/* § — Reference, discipline, and what to retain
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  id: "ref",
  num: "§",
  phase: "Reference",
  title: "Reference, discipline, and what to retain",
  blurb: "The notation table, the five rules of proof hygiene, and the ideas that outlive this particular development.",

  orient: {
    youWill: [
      "unfold any symbol in this workbook — <code>↦</code>, <code>∗</code>, <code>-∗</code>, <code>⊢</code>, <code>pure</code>, <code>Hoare</code>, <code>wp</code> — back to the raw <code>Store → Heap → Prop</code> it abbreviates, without looking it up;",
      "read a Lean goal state that the pretty-printer has folded into dot notation, and say what the source you wrote actually looks like;",
      "recognise which of <b>three</b> proof shapes a new goal belongs to, and know the first two tactics before you have thought about the mathematics;",
      "decode the four error messages that account for most of the time lost in this development, from the message alone;",
      "find the lemma you need by the <i>shape</i> of your goal rather than by remembering its name;",
      "state what the whole of Phase 1 actually assumed about heaps — a partial commutative monoid, nothing more — and therefore say which other models the same logic serves unchanged."
    ],
    needs: [
      "Nothing new. This chapter defines no Lean and asks for no exercises.",
      "It is written to be useful after M4 and indispensable after M9. If you have only read as far as M2, the notation table and the first proof shape are already worth having open in a second tab.",
      "The Lean snippets here are all fresh — written for this chapter and compiled against the M12 prelude — except where a block is quoted verbatim from the corpus and labelled <b>verified</b>."
    ],
    payoff: "Everything in Phase 1 used exactly one algebraic structure. Once you can name it, you can see which parts of this development were about heaps and which parts were about separation — and only the second kind transfers to concurrency, ghost state, and permissions."
  },

  blocks: [

    {
      t: "p",
      h: "This is not a summary to read once. It is the page to keep open in a second tab while you work: what each symbol unfolds to, what Lean is telling you when it prints something you did not write, which of three shapes your goal has, and which lemma to reach for. The last two sections are the part worth remembering a year from now."
    },

    /* ================= Notation ================= */

    {
      t: "h3",
      s: "Notation"
    },
    {
      t: "txt",
      src: "  h l = some v      location l is allocated in h and holds v\n  h l = none        location l is not in h\n\n  emp               I own nothing\n  l ↦ v             I own exactly the cell l, holding v\n  P ∗ Q             the heap splits into disjoint parts satisfying P and Q\n  P -∗ Q            give me a disjoint P-heap and the union satisfies Q\n  P ⊢ Q             every state satisfying P satisfies Q\n  P ⊣⊢ Q            P ⊢ Q and Q ⊢ P\n  fact φ            φ holds; says nothing about the heap        (pairs with ∧)\n  pure φ            φ holds and I own nothing                   (pairs with ∗)\n  ⌜φ⌝               common textbook notation for pure φ"
    },
    {
      t: "p",
      h: "That is the paper reading. Underneath, every one of those symbols is a plain Lean <code>def</code> producing a <code>Store → Heap → Prop</code>, and every proof you have written went through the right-hand column, not the left. When a goal stops making sense, the fix is almost always to unfold one row of this table by hand:"
    },
    {
      t: "tbl",
      head: ["Written", "Lean name", "What it literally is", "From"],
      rows: [
        ["<code>emp</code>", "<code>emp</code>", "<code>fun _ h =&gt; h = Heap.empty</code>", "M3"],
        ["<code>l ↦ v</code>", "<code>pointsTo l v</code>", "<code>fun _ h =&gt; h = Heap.singleton l v</code>", "M3"],
        ["<code>fact φ</code>", "<code>fact φ</code>", "<code>fun σ _ =&gt; φ σ</code>", "M3"],
        ["<code>pure φ</code>", "<code>pure φ</code>", "<code>aAnd (fact φ) emp</code>", "M3"],
        ["<code>P ⊢ Q</code>", "<code>Entails P Q</code>", "<code>∀ σ h, P σ h → Q σ h</code>", "M3"],
        ["<code>P ⊣⊢ Q</code>", "<code>AssertionEquiv P Q</code>", "<code>Entails P Q ∧ Entails Q P</code>", "M3"],
        ["<code>P ∗ Q</code>", "<code>star P Q</code>", "<code>fun σ h =&gt; ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>", "M4"],
        ["<code>P -∗ Q</code>", "<code>wand P Q</code>", "<code>fun σ h =&gt; ∀ h', Heap.disjoint h h' → P σ h' → Q σ (Heap.union h h')</code>", "M11"],
        ["<code>Hoare P c Q</code>", "<code>Hoare</code>", "<code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>", "M6"],
        ["<code>wp c Q</code>", "<code>wp</code>", "<code>fun σ h =&gt; ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>", "M12"]
      ],
      cap: "Read the last two rows together. <code>Hoare P c Q</code> is <code>∀ σ h, P σ h → (wp c Q) σ h</code>, and <code>P ⊢ wp c Q</code> is the same string of symbols. That is why <code>hoare_iff_entails_wp</code> is proved by <code>Iff.rfl</code> and not by an argument."
    },
    {
      t: "note",
      kind: "tip",
      title: "Precedences, so you can drop brackets safely",
      h: "<code>↦</code> binds tightest at 60, then <code>∗</code> at 55, then <code>-∗</code> at 54, then <code>⊢</code> at 40. Both <code>∗</code> and <code>-∗</code> are <b>right</b>-associative, as is <code>;;</code> at 60. So <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂ -∗ R</code> needs no brackets at all, and <code>P ∗ Q ∗ R</code> always means <code>P ∗ (Q ∗ R)</code> — which is why the assortment of re-bracketing lemmas in M4 exists at all."
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- ↦ binds tightest (60), then ∗ (55), then -∗ (54), then ⊢ (40).
example (l₁ l₂ : Loc) (v₁ v₂ : Val) (R : Assertion) :
    (l₁ ↦ v₁ ∗ l₂ ↦ v₂ -∗ R) = (((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) -∗ R) := rfl

-- ∗ and -∗ are right-associative, so no brackets means right-nested.
example (P Q R : Assertion) : (P ∗ Q ∗ R) = (P ∗ (Q ∗ R)) := rfl

-- ;; is right-associative too.
example (c₁ c₂ c₃ : Cmd) : (c₁ ;; c₂ ;; c₃) = (c₁ ;; (c₂ ;; c₃)) := rfl`,
      cap: "Each of these is closed by <code>rfl</code>: the two sides are not merely equivalent, they are the <i>same term</i> after parsing. If you are ever unsure how an expression brackets, this is a two-line way to ask Lean instead of guessing."
    },

    /* ================= Anatomy of star ================= */

    {
      t: "h3",
      s: "The one definition to keep in your head"
    },
    {
      t: "p",
      h: "If you memorise nothing else, memorise the shape of <code>star</code>. Almost every anonymous constructor you write from M4 onwards — every <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code>, every <code>obtain</code> pattern, every mysterious arity error — is this definition being taken apart or put back together."
    },
    {
      t: "anat",
      tag: "verified",
      src: `def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star`,
      parts: [
        { m: "∃ h₁ h₂", h: "Two witnesses. When you destructure a <code>∗</code> these are the first two names in the pattern, and when you build one they are the first two things you must supply. This is the point at which the split from paper — “the heap divides” — becomes something you have to <i>exhibit</i>." },
        { m: "Heap.disjoint h₁ h₂", h: "Component three. On paper this is a side condition written under the line, or not written at all. In Lean it is a conjunct of the proposition, so it is carried by the same proof term as everything else and you must produce it on the way in and consume it on the way out." },
        { m: "h = Heap.union h₁ h₂", h: "Component four, and the one that traps people. <code>Heap.union</code> is a <b>total</b> function — it is left-biased and defined for every pair, disjoint or not. Disjointness is a separate conjunct precisely so that <code>union</code> never has to take a proof as an argument. If it did, every rewrite in M2 would carry a disjointness proof around and <code>rw</code> would stop working." },
        { m: "P σ h₁", h: "Component five: the left assertion, applied to the <i>left half only</i>. Note <code>σ</code> is the same on both sides. The heap splits; the store does not." },
        { m: "Q σ h₂", h: "Component six. Two witnesses plus four conjuncts, and Lean's anonymous constructor flattens right-nested <code>∃</code> and <code>∧</code>, so the pattern for a <code>∗</code> has exactly <b>six</b> slots. Write five and you will get the arity error below." },
        { m: "infixr:55", h: "The notation, declared separately from the definition. <code>infixr</code> makes it right-associative; <code>55</code> is the precedence. Because notation is a separate declaration, <code>star P Q</code> and <code>P ∗ Q</code> are interchangeable everywhere, and Lean will sometimes print one where you wrote the other." }
      ]
    },
    {
      t: "detail",
      title: "Why fact and pure are two different things",
      tag: "aside",
      open: false,
      blocks: [
        { t: "p", h: "They look like duplicates and they are not. <code>fact φ</code> constrains the store and says <i>nothing</i> about the heap; <code>pure φ</code> constrains the store <i>and</i> demands that you own nothing. The difference is exactly which connective they compose with." },
        { t: "code", tag: "verified", src: `def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ

def pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp` },
        { t: "p", h: "<code>fact</code> pairs with <code>∧</code>: <code>aAnd (fact φ) P</code> says “<code>φ</code> holds and this heap satisfies <code>P</code>” — one heap, two claims about it. <code>pure</code> pairs with <code>∗</code>: <code>pure φ ∗ P</code> says the heap splits into an empty part carrying <code>φ</code> and a <code>P</code> part. Those are equivalent, and the two directions are <code>star_pure_left</code> and <code>star_pure_right</code> in M4." },
        { t: "p", h: "If you had only <code>fact</code> and wrote <code>fact φ ∗ P</code>, you would be asserting that some <i>arbitrary</i> sub-heap satisfies <code>fact φ</code> — which it does, vacuously, for any split — and the assertion would have lost all control over where the heap divides. That is why the postconditions in M7 say <code>pure (fun σ =&gt; σ x = v) ∗ (l ↦ v)</code> and not <code>fact … ∗ …</code>." }
      ]
    },

    /* ================= Reading what Lean prints ================= */

    {
      t: "h3",
      s: "Reading what Lean prints"
    },
    {
      t: "p",
      h: "The single most disorienting thing about this development is that Lean rarely prints back what you typed. The pretty-printer folds function application into dot notation, inserts case labels you did not write, shows you <code>¬x = l</code> where you were expecting <code>x ≠ l</code>, and renders anonymous structures with named-field braces. Nothing has gone wrong when this happens. Here is the translation."
    },
    {
      t: "cmp",
      left: {
        t: "What you write in the source",
        h: "<p>The long form, because it is what the definitions are called and what you can search for.</p>",
        tag: "sketch",
        src: `Heap.write (Heap.write h l v₁) l v₂
Heap.disjoint h₁ h₂
Heap.union h₁ h₂
Atom.eval σ e
State.mk σ h`
      },
      right: {
        t: "What Lean prints back",
        kind: "good",
        h: "<p>The folded form. Lean prints <code>Foo.bar</code> in dot notation exactly when the <b>first explicit argument</b> has type <code>Foo</code>: that argument becomes the receiver and the others trail behind it. Every heap operation is declared <code>Heap.write (h : Heap) …</code>, <code>Heap.union (h₁ h₂ : Heap)</code>, so this fires constantly. The fourth row is the exception, and it is here on purpose.</p>",
        tag: "sketch",
        src: `(h.write l v₁).write l v₂
h₁.disjoint h₂
h₁.union h₂
Atom.eval σ e
{ store := σ, heap := h }`
      }
    },
    {
      t: "p",
      h: "The fourth row is the one that teaches the rule, because it is the row where nothing happens. <code>Atom.eval</code> is declared <code>def Atom.eval (σ : Store) : Atom → Val</code>, so its first explicit argument is a <code>Store</code>, not an <code>Atom</code>. In the source you may still write <code>e.eval σ</code> — Lean's field notation searches for the first explicit argument whose type is <code>Atom</code> and finds the second one — but the printer does not run that search backwards, so it gives up and prints <code>Atom.eval σ e</code>. That is why the corpus says <code>e.eval σ</code> and the goal in the shape-C trace below says <code>Atom.eval σ e</code>: same term, and the direction of the fold is decided by argument order, not by which form you typed."
    },
    {
      t: "p",
      h: "Here is a real goal, taken mid-proof from <code>star_comm</code>. Every fold in the list above is visible in it at once, and this is the state you will be staring at most often between M4 and M11:"
    },
    {
      t: "state",
      src: `P Q : Assertion
σ : Store
h h₁ h₂ : Heap
hd : h₁.disjoint h₂
hu : h = h₁.union h₂
hp : P σ h₁
hq : Q σ h₂
⊢ (Q ∗ P) σ h`,
      cap: "After <code>intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩</code>. The six names in the pattern are exactly the six components of <code>star</code> anatomised above, in order."
    },
    {
      t: "dl",
      items: [
        { k: "<code>h₁.disjoint h₂</code>", h: "Means <code>Heap.disjoint h₁ h₂</code>. You may type either. Searching the corpus for <code>disjoint</code> finds the lemma; searching for <code>.disjoint</code> mostly finds goal states quoted in this workbook." },
        { k: "<code>case pos</code> / <code>case neg</code>", h: "The two goals <code>by_cases hx : x = l</code> produced, labelled by Lean, not by you. <code>pos</code> is the branch where the proposition holds, <code>neg</code> the branch where it does not. They are labels only — <code>·</code> focuses the first remaining goal regardless of its name, and <code>&lt;;&gt;</code> ignores names entirely. You can also write <code>case pos =&gt; …</code> if you want to be explicit about which branch you are in." },
        { k: "<code>hx : ¬x = l</code>", h: "The same proposition as <code>x ≠ l</code>, printed differently — and the difference is not the pretty-printer being inconsistent. <code>≠</code> is notation for <code>Ne</code>; <code>Ne a b</code> is a <code>def</code> that unfolds to <code>¬(a = b)</code>, which unfolds to <code>a = b → False</code>. Lean prints <code>Ne x l</code> as <code>x ≠ l</code> and prints <code>Not (x = l)</code> as <code>¬x = l</code>, and it does <i>not</i> unfold one into the other. So which form you see tells you how the hypothesis was built, not what it says: <code>by_cases hx : x = l</code> constructs <code>Not (x = l)</code>, so the negative branch shows <code>¬x = l</code>, whereas <code>write_other</code>, whose binder is written <code>(hne : x ≠ l)</code>, keeps its <code>≠</code> all the way into the goal display. They are definitionally equal, interchangeable, and <code>simp [Heap.write, hx]</code> uses either one the same way." },
        { k: "<code>{ store := σ, heap := h }</code>", h: "The <code>State</code> structure, printed with named fields. In source you almost always write <code>⟨σ, h⟩</code>, and Lean accepts it: the anonymous constructor <code>⟨…⟩</code> works for <i>any</i> single-constructor inductive type. That is one notation doing three jobs in this development — it builds a <code>State</code>, it builds an <code>∃</code>, and it builds an <code>∧</code> — and because it also flattens right-nested ones, the same brackets that hold two things here hold the six components of <code>star</code> elsewhere." },
        { k: "<code>s'.store</code> and <code>s'.heap</code>", h: "Projections out of an existentially quantified <code>State</code>. Every Hoare-triple goal ends in <code>Q s'.store s'.heap</code> because the postcondition has to be applied to the <i>final</i> state, which you have not chosen yet." },
        { k: "<code>Cmd.write l e</code>", h: "What <code>.write l e</code> elaborates to. Lean calls the leading dot <i>dotted identifier notation</i>, and it is a different device from <code>⟨…⟩</code>: Lean looks at the expected type of the position, sees <code>Cmd</code>, and resolves <code>.write</code> in the <code>Cmd</code> namespace. It works only where the expected type is already known — <code>#check .write</code> on its own fails with “the expected type of <code>.write</code> could not be determined”, and offers you <code>Cmd.write</code>, <code>Exec.write</code> and <code>Heap.write</code> to choose from. Once elaboration has resolved it the name is fixed, so goals print <code>Cmd.write l e</code>." },
        { k: "<code>?m.3</code>", h: "A metavariable — a hole Lean has not yet filled. Seeing one in an error message means unification failed <i>before</i> it could determine what you meant. It is not a mistake in your term so much as a signal that Lean gave up earlier than you expected." }
      ]
    },
    {
      t: "note",
      kind: "key",
      title: "Everything here is a def over functions, and that is load-bearing",
      h: "<code>Assertion</code>, <code>Entails</code>, <code>Hoare</code>, <code>wp</code>, <code>emp</code>, <code>pointsTo</code>, <code>star</code>, <code>wand</code> are all ordinary definitions whose bodies are <code>fun … =&gt; …</code>. Consequently <code>intro</code> walks straight through them without any <code>unfold</code>, <code>exact ⟨…⟩</code> builds through them, and <code>subst</code> fires on a hypothesis whose type merely <i>unfolds to</i> an equation. That is why you have written almost no <code>unfold</code> in this entire course."
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- \`⊢\` is a def, so \`intro\` walks straight through it: no \`unfold\` anywhere.
example (P : Assertion) : P ⊢ P := by
  intro σ h hp
  exact hp

-- \`Hoare\` is a def too. Same story, one binder deeper.
example (P : Assertion) : Hoare P .skip P := by
  intro σ h hp
  exact ⟨⟨σ, h⟩, Exec.skip, hp⟩

-- \`show\` retypes the goal to anything definitionally equal to it.
example (l : Loc) (v : Val) : (l ↦ v) (fun _ => 0) (Heap.singleton l v) := by
  show Heap.singleton l v = Heap.singleton l v
  rfl

-- Hoare and wp are not merely equivalent: they are the same proposition.
example (P Q : Assertion) (c : Cmd) : Hoare P c Q ↔ P ⊢ wp c Q := Iff.rfl`,
      cap: "All four compile against the M12 prelude. The third is the pattern behind every <code>show</code> in the corpus: when a goal is unreadable because it is stated through three definitions, <code>show</code> replaces it with any definitionally equal phrasing you prefer."
    },

    /* ================= Three proof shapes ================= */

    {
      t: "h3",
      s: "Three proof shapes"
    },
    {
      t: "p",
      h: "Essentially every proof in this workbook is one of three shapes. Recognising which one you are in tells you the first two tactics before you have thought about the mathematics at all, and it is the fastest single thing you can learn from the whole development."
    },
    {
      t: "steps",
      title: "Which shape am I in?",
      items: [
        {
          k: "Shape A · two heaps are equal",
          h: "<p>The goal is <code>h₁ = h₂</code> where both sides are <code>Heap</code>. Open with <code>funext x</code>, then <code>by_cases</code> on whichever location comparison the definitions branch on, then <code>simp</code> with the definitions and the case hypothesis. M0 and M1 are made of almost nothing else, and every heap <i>equation</i> in M2 — <code>union_empty_left</code>, <code>union_assoc</code>, <code>union_comm</code> — goes the same way. The rest of M2 does not, and the reason is worth noticing: <code>Heap.disjoint h₁ h₂</code> is defined as <code>∀ l, h₁ l = none ∨ h₂ l = none</code>, so it is already quantified over locations. Those proofs open with <code>intro l</code>; there is no function equality to break and no <code>funext</code> in sight.</p>"
        },
        {
          k: "Shape B · an entailment",
          h: "<p>The goal is <code>P ⊢ Q</code>. Open with <code>intro σ h</code> followed by a destructuring pattern for <code>P</code>, then close with <code>exact ⟨…⟩</code> rebuilding <code>Q</code>. No <code>funext</code> should appear: if you find yourself doing pointwise heap reasoning here, you are missing a lemma from M1–M2. M3, M4, M10 and M11 are this shape.</p>"
        },
        {
          k: "Shape C · a triple",
          h: "<p>The goal is <code>Hoare P c Q</code>. Open with <code>intro σ h hp</code>, use <code>subst</code> or <code>obtain</code> to pin down the initial heap from <code>hp</code>, then <code>exact ⟨finalState, Exec.someConstructor …, proofOfQ⟩</code>. The middle component is the only place the operational semantics appears. M6–M9 and M12–M13 are this shape.</p>"
        },
        {
          k: "And when none of them fits",
          h: "<p>You are almost certainly trying to do two shapes at once. The commonest instance: a triple whose proof drifts into a <code>funext</code>. Stop, extract the heap fact as a standalone lemma in the M1 style, and the triple goes back to shape C. That is discipline rule 3 below, and this is what it feels like from the inside.</p>"
        }
      ]
    },
    {
      t: "p",
      h: "Shape A, with the real goal states. <code>write_shadow</code> is the canonical instance: two writes to the same location, the first one invisible. Here is the whole proof, and then the same proof with the goal put back in."
    },
    {
      t: "code",
      tag: "verified",
      src: `theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, hx]`
    },
    {
      t: "trace",
      title: "Shape A — write_shadow, tactic by tactic",
      start: `h : Heap
l : Loc
v₁ v₂ : Val
⊢ (h.write l v₁).write l v₂ = h.write l v₂`,
      steps: [
        {
          tac: "funext x",
          state: `h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x`,
          h: "Both sides are functions <code>Loc → Option Val</code>, and Lean's equality on functions is not pointwise by definition. It is worth being exact about what <code>funext</code> is, because it is easy to assume the wrong thing: in Lean 4 extensionality is <b>not</b> an axiom you postulate — <code>funext</code> is a theorem, derived from quotient soundness. You can ask. <code>#print axioms funext</code> answers <code>'funext' depends on axioms: [Quot.sound]</code>, and <code>#print axioms write_shadow</code> answers <code>[propext, Quot.sound]</code>. What matters tactically is only that you cannot cross from <code>∀ x, f x = g x</code> to <code>f = g</code> by <code>rfl</code> or by <code>simp</code>; you have to apply that theorem, and <code>funext x</code> is how. The goal gains a fresh <code>x : Loc</code> and both sides become applications. Everything after this line is about one location."
        },
        {
          tac: "by_cases hx : x = l",
          state: `case pos
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : x = l
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x

case neg
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : ¬x = l
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x`,
          h: "Two goals, identical except for <code>hx</code>. This is the move that makes the proof work: <code>Heap.write h l v</code> is <code>fun x =&gt; if x = l then some v else h x</code>, so nothing simplifies until Lean knows which branch it is in. One thing here is easy to half-learn and worth getting right: <code>by_cases</code> does <b>not</b> require the proposition to be decidable. In Lean 4 core it opens <code>Classical</code>, and <code>by_cases hp : P</code> splits on an opaque <code>P : Prop</code> quite happily, giving <code>hp : P</code> and <code>hp : ¬P</code>. What genuinely needs decidability is the <code>if</code> inside <code>Heap.write</code> — that is why the model fixes <code>Loc := Nat</code> rather than leaving locations abstract. The two facts hold together here, which is why they get conflated."
        },
        {
          tac: "<;> simp [Heap.write, hx]",
          state: "No goals.",
          h: "<code>&lt;;&gt;</code> runs the tactic on <b>every</b> goal the previous tactic produced, so one line discharges both branches. <code>simp [Heap.write]</code> unfolds the definition, exposing the <code>if</code>; <code>simp [… , hx]</code> then uses <code>hx</code> to decide it — in <code>pos</code> it rewrites <code>x</code> to <code>l</code> and both sides become <code>some v₂</code>; in <code>neg</code> it turns the condition into <code>False</code> and both sides become <code>h x</code>. Replace <code>simp</code> by <code>simp?</code> and Lean reports the same minimal set for both branches: <code>simp only [Heap.write, hx, ↓reduceIte]</code>. The third name is not one of yours — <code>↓reduceIte</code> is the built-in simproc that collapses <code>if c then a else b</code> once <code>c</code> has been settled, and it is what actually closes the goal. Your two names only put it in a position to fire."
        }
      ],
      done: "No goals."
    },
    {
      t: "p",
      h: "Shape B, with the real goal states. <code>star_comm</code> is the smallest honest instance: take a split apart, put it back the other way round."
    },
    {
      t: "code",
      tag: "verified",
      src: `theorem star_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by
  intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩
  exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩`
    },
    {
      t: "trace",
      title: "Shape B — star_comm, tactic by tactic",
      start: `P Q : Assertion
⊢ P ∗ Q ⊢ Q ∗ P`,
      steps: [
        {
          tac: "intro σ h ⟨h₁, h₂, hd, hu, hp, hq⟩",
          state: `P Q : Assertion
σ : Store
h h₁ h₂ : Heap
hd : h₁.disjoint h₂
hu : h = h₁.union h₂
hp : P σ h₁
hq : Q σ h₂
⊢ (Q ∗ P) σ h`,
          h: "One tactic doing two jobs. <code>intro σ h</code> unfolds <code>Entails</code> — it is a <code>def</code>, so <code>intro</code> sees the <code>∀</code> underneath without help. The <code>⟨…⟩</code> pattern then introduces the hypothesis <i>and</i> immediately destructures it into the six components of <code>star</code>. Writing <code>intro σ h hstar</code> followed by <code>obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hstar</code> gives exactly this state."
        },
        {
          tac: "exact ⟨h₂, h₁, disjoint_symm hd, by rw [hu, union_comm hd], hq, hp⟩",
          state: "No goals.",
          h: "<p>The same six slots, filled in swapped order. Slots one and two are the witnesses <code>h₂, h₁</code>. Slot three needs <code>Heap.disjoint h₂ h₁</code>, which is <code>disjoint_symm hd</code>. Slots five and six are <code>hq, hp</code>.</p><p>Slot four is the one with work in it, and it is filled by <code>by rw [hu, union_comm hd]</code> — a tactic block sitting inside a term. That is legal anywhere a term is expected, and it is what saves you from breaking a one-line <code>exact</code> into a <code>refine</code> with a <code>?_</code> hole. The obligation there is <code>h = h₂.union h₁</code>. <code>rw [hu]</code> replaces <code>h</code> by <code>h₁.union h₂</code>, leaving <code>h₁.union h₂ = h₂.union h₁</code>; <code>rw [union_comm hd]</code> rewrites the left side into the right and the goal closes. There is no third tactic because <code>rw</code> attempts <code>rfl</code> after every rewrite — which is why so many <code>rw</code> chains in the corpus stop without an explicit closer, and why removing the last rewrite from one of them produces a confusing “unsolved goals” rather than a visible difference. Note also that <code>union_comm</code> <b>requires</b> <code>hd</code>: union is left-biased and commutes only on disjoint pairs.</p>"
        }
      ],
      done: "No goals."
    },
    {
      t: "p",
      h: "Shape C, with the real goal states. <code>hoare_write</code> is the smallest instance that shows all three moves: unfold the triple, pin the initial heap, exhibit the final state. The closing term is three lines, so it is worth having the source in front of you before the trace."
    },
    {
      t: "code",
      tag: "verified",
      src: `theorem hoare_write (l : Loc) (e : Atom) (old : Val) :
    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by
  intro σ h hp
  subst hp
  exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,
         Exec.write (singleton_same l old),
         write_singleton l old (e.eval σ)⟩`
    },
    {
      t: "trace",
      title: "Shape C — hoare_write, tactic by tactic",
      start: `l : Loc
e : Atom
old : Val
⊢ Hoare (l ↦ old) (Cmd.write l e) fun σ h => (l ↦ Atom.eval σ e) σ h`,
      steps: [
        {
          tac: "intro σ h hp",
          state: `l : Loc
e : Atom
old : Val
σ : Store
h : Heap
hp : (l ↦ old) σ h
⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap`,
          h: "The triple has vanished and its definition is on the screen: an existential over the final state, an <code>Exec</code> derivation, and the postcondition applied to that state's two projections. This is what every shape-C goal looks like after one tactic, and it tells you the closing term has three components."
        },
        {
          tac: "subst hp",
          state: `l : Loc
e : Atom
old : Val
σ : Store
⊢ ∃ s',
    Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old } s' ∧
      (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap`,
          h: "The interesting line. <code>hp : (l ↦ old) σ h</code> does not <i>look</i> like an equation, but <code>pointsTo</code> is <code>fun _ h =&gt; h = Heap.singleton l v</code>, so it is one. <code>subst</code> unfolds far enough to see that, eliminates the variable <code>h</code> entirely, and replaces it everywhere by <code>Heap.singleton l old</code>. Exact ownership is what makes this legal: the precondition does not say the heap <i>contains</i> the cell, it says the heap <b>is</b> the cell."
        },
        {
          tac: "exact ⟨⟨σ, …⟩, Exec.write …, write_singleton …⟩",
          state: "No goals.",
          h: "<p>Three components matching the three parts of the goal; the source block above has them written out. <b>Slot one</b> is the final state, <code>⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩</code> — anonymous-constructor notation for <code>State</code>, which is why it prints back as <code>{ store := σ, heap := … }</code>. The store is untouched: a write moves no variables.</p><p><b>Slot two</b> is an <code>Exec</code> derivation landing in that state. The constructor is <code>| write {s l e old} (hl : s.heap l = some old)</code>, and its conclusion is <code>Exec (.write l e) s ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩</code>. So slot one is not a free choice at all — it is forced, letter for letter, by what slot two concludes. If you cannot guess the final state, read the constructor and copy it. Its one explicit argument is the proof that the cell was already allocated, and here that is <code>singleton_same l old : Heap.singleton l old l = some old</code>. This is where exact ownership pays: the precondition did not merely say the cell exists somewhere in <code>h</code>, it said <code>h</code> <i>is</i> that cell, so the witness is a one-line M1 lemma rather than a case analysis.</p><p><b>Slot three</b> is the postcondition at that state. Unfolding <code>↦</code>, that obligation is <code>Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l (e.eval σ)</code> — which is <code>write_singleton l old (e.eval σ)</code> on the nose. The only heap-level fact in the whole proof arrives by name, from M1. That is discipline rule 3 in action.</p>"
        }
      ],
      done: "No goals."
    },

    /* ================= Errors ================= */

    {
      t: "h3",
      s: "Four errors, and what they actually mean"
    },
    {
      t: "p",
      h: "These four account for most of the time lost in this development. Every message below is real: each is what Lean 4.32.2 printed for the snippet shown, run against the chapter prelude. Two presentational liberties, so that nothing surprises you at your own terminal. Lean prefixes each diagnostic with a <code>file:line:column:</code> locator — those are stripped here, and a blank line stands between one diagnostic and the next in their place. Error 2 is abridged a little further, in the way its caption records. Learning to read these from the message alone is worth more than learning another tactic."
    },
    {
      t: "detail",
      title: "1 · “Type mismatch: rfl has type ?m.3 = ?m.3”",
      tag: "error",
      open: false,
      blocks: [
        { t: "code", tag: "sketch", src: `example (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := rfl`, cap: "Meant to fail. This is the proof you try first, and it is the right instinct with the wrong tool." },
        { t: "state", src: `error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  (h.write l v₁).write l v₂ = h.write l v₂` },
        { t: "p", h: "The two functions agree at every argument, but they are not the <i>same term</i>, and <code>rfl</code> only closes goals whose sides are definitionally equal. Lean does unfold both sides — you can check this by replacing the proof with a <code>show</code>, which Lean accepts: the goal is <code>(fun x =&gt; if x = l then some v₂ else h.write l v₁ x) = fun x =&gt; if x = l then some v₂ else h x</code>. Then it stops. The two <code>else</code> branches are <code>h.write l v₁ x</code> and <code>h x</code>; those are equal at every <code>x</code>, but they are not <i>convertible</i>, because reducing the first would require deciding <code>x = l</code> and <code>x</code> is a bound variable with nothing known about it. Pointwise equality that needs a case split is exactly what definitional equality cannot see." },
        { t: "p", h: "The fix is <code>funext x</code> — shape A. The metavariables <code>?m.3</code> in the message are the ordinary way Lean reports “I tried to unify your term's type with the goal and failed”; they are not a symptom of anything you did." }
      ]
    },
    {
      t: "detail",
      title: "2 · “unsolved goals … ⊢ x = l → some v = h x”, and an unused simp argument",
      tag: "error",
      open: false,
      blocks: [
        { t: "code", tag: "sketch", src: `theorem write_other' (h : Heap) (l x : Loc) (v : Val) (hne : l ≠ x) :
    Heap.write h l v x = h x := by
  simp [Heap.write, hne]`, cap: "Meant to fail. Compare with <code>write_other</code> in M1, whose hypothesis is <code>hne : x ≠ l</code>." },
        { t: "state", src: `error: unsolved goals
h : Heap
l x : Loc
v : Val
hne : l ≠ x
⊢ x = l → some v = h x

warning: This simp argument is unused:
  hne

Hint: Omit it from the simp argument list.
  simp [Heap.write, hne]`, cap: "Lean's real output, abridged in exactly two ways. A terminal draws the unused argument <i>struck through</i> in that last line — Lean emits combining strikethrough characters over <code>, hne</code>, and they render unpredictably in a browser, so they are dropped here. And one closing line is omitted: Lean adds a note saying the linter can be turned off with <code>set_option linter.unusedSimpArgs false</code>. Do not turn it off; that warning is the most useful thing on the screen. Notice too that <code>hne : l ≠ x</code> keeps its <code>≠</code> here, where <code>by_cases</code> gave you <code>¬x = l</code> — the same phenomenon as in the table above, and equally harmless." },
        { t: "p", h: "First, where that leftover goal comes from, because it looks nothing like what you wrote. Unfolding <code>Heap.write</code> turns the goal into <code>(if x = l then some v else h x) = h x</code>. <code>simp</code> then splits an equation whose left side is an <code>if</code> into the two implications <code>x = l → some v = h x</code> and <code>¬x = l → h x = h x</code>, discharges the second by <code>rfl</code>, and hands you the first. So the residue is the <i>positive</i> branch: “if <code>x</code> really were <code>l</code>, you would still have to prove this”. Which you cannot, and should not have to." },
        { t: "p", h: "The disequality is the wrong way round. To kill that branch <code>simp</code> must rewrite <code>x = l</code> to <code>False</code>, and for that it needs a hypothesis of shape <code>x ≠ l</code>. It has <code>l ≠ x</code>, which becomes the rewrite rule <code>(l = x) = False</code> and so fires only on <code>l = x</code> — a pattern that does not occur. <code>simp</code> does not try <code>Ne.symm</code> on your behalf, and there is no <code>eq_comm</code> normalisation running to bring the two into line." },
        { t: "p", h: "The warning is the tell: Lean says outright that <code>hne</code> was unused, and in a terminal it strikes the argument through in the suggested replacement. Whenever a <code>simp</code> fails and the linter reports the hypothesis you were counting on as unused, suspect an orientation problem before anything else. The fix is <code>simp [Heap.write, hne.symm]</code>, or better, state the hypothesis as <code>x ≠ l</code> in the first place — which is exactly why every M1 lemma is phrased with the bound variable on the left." }
      ]
    },
    {
      t: "detail",
      title: "3 · “Application type mismatch … has type P σ h₁ ∧ Q σ h₂ but is expected to have type Q σ h₂”",
      tag: "error",
      open: false,
      blocks: [
        { t: "code", tag: "sketch", src: `example (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by
  intro σ h ⟨h₁, h₂, hd, hp, hq⟩
  exact ⟨h₂, h₁, disjoint_symm hd, by rw [union_comm hd], hq, hp⟩`, cap: "Meant to fail. Five names in the destructuring pattern where <code>star</code> has six components." },
        { t: "state", src: `error: Application type mismatch: The argument
  hq
has type
  P σ h₁ ∧ Q σ h₂
but is expected to have type
  Q σ h₂
in the application
  And.intro hq

error: Tactic \`rewrite\` failed: Did not find an occurrence of the pattern
  h₁.union h₂
in the target expression
  h = h₂.union h₁

P Q : Assertion
σ : Store
h h₁ h₂ : Heap
hd : h₁.disjoint h₂
hp : h = h₁.union h₂
hq : P σ h₁ ∧ Q σ h₂
⊢ h = h₂.union h₁` },
        { t: "p", h: "There is no “wrong number of arguments” error, and that is what makes this one expensive. A short anonymous-constructor pattern does not fail — it stops splitting early and binds the remaining <i>nest</i> to the last name. Look at the hypotheses in the second message: <code>hp</code> got the union equation instead of <code>P σ h₁</code>, and <code>hq</code> got the whole conjunction <code>P σ h₁ ∧ Q σ h₂</code>. Every name after the mistake is shifted by one." },
        { t: "p", h: "So the error surfaces far from its cause, usually as a type mismatch in the closing <code>exact</code>. Diagnose it by reading the <i>hypothesis list</i>, not the message: if a name has a type you did not expect, count the components of the definition you destructured. For <code>star</code> the answer is always six." }
      ]
    },
    {
      t: "detail",
      title: "4 · “simp made no progress”",
      tag: "error",
      open: false,
      blocks: [
        { t: "code", tag: "sketch", src: `example (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by
  simp [Heap.write]`, cap: "Meant to fail. Same theorem as error 1, attacked with a bigger hammer." },
        { t: "state", src: "error: `simp` made no progress" },
        { t: "p", h: "<code>simp</code> unfolded nothing at all — that is what “no progress” means, and the reason is worth knowing exactly, because it is not the reason most people guess. When Lean compiles <code>def Heap.write (h : Heap) (l : Loc) (v : Val) : Heap := fun x =&gt; if x = l then some v else h x</code>, it generates the equation lemma in <b>applied</b> form, with the lambda's binder pulled out as a fourth argument. Ask it: <code>#check @Heap.write.eq_1</code> prints <code>∀ (h : Heap) (l : Loc) (v : Val) (x : Loc), h.write l v x = if x = l then some v else h x</code>." },
        { t: "p", h: "Writing <code>Heap.write</code> in the simp set installs that as a left-to-right rewrite rule, and its left-hand side has <i>four</i> arguments. The goal applies <code>Heap.write</code> to three. So the rule does not match anywhere, nothing is rewritten, and <code>simp</code> reports the goal came back unchanged. It is a stuck-ness message, not a failure of the simp set — and adding more lemmas cannot help, because the rule you already supplied cannot fire." },
        { t: "p", h: "<code>funext x</code> is precisely what supplies the missing fourth argument, after which <code>simp [Heap.write, hx]</code> closes both branches in one line. The lesson generalises to every definition here whose body is a <code>fun</code>: to rewrite with it you must first put the goal in a form where it is applied. Shape A always starts with <code>funext</code>. If you are ever tempted to add more lemmas to the <code>simp</code> list here, add <code>funext x</code> above it instead." }
      ]
    },

    /* ================= Finding the lemma ================= */

    {
      t: "h3",
      s: "Where to look when you are stuck"
    },
    {
      t: "p",
      h: "By M9 there are about a hundred and forty names in scope, and remembering them is not the skill. Indexing them by the <i>shape of the goal</i> is. This is the table to scan first."
    },
    {
      t: "tbl",
      head: ["Your goal looks like", "Reach for", "From"],
      rows: [
        ["two heaps are equal", "<code>funext</code>, then <code>by_cases</code> on the location, then <code>simp</code> with the definitions", "M0, M1"],
        ["<code>Heap.union h₁ h₂ l = …</code> at one location", "<code>union_of_none</code>, <code>union_of_some</code>, <code>union_eq_none</code>", "M2"],
        ["<code>Heap.disjoint</code> of a union", "<code>disjoint_union_left</code>, <code>disjoint_union_right</code> — both are <code>↔</code>, so usable in either direction", "M2"],
        ["disjointness of two singletons", "<code>singleton_disjoint</code>, <code>singleton_disjoint_iff</code>", "M2"],
        ["re-bracketing a chain of <code>∗</code>", "<code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>star_rotate_left</code>, <code>star_rotate_right</code>, <code>star_swap_middle</code>", "M4"],
        ["an <code>emp</code> to add or remove", "<code>star_emp_left</code>, <code>star_emp_right</code>, and the two <code>_intro</code> converses", "M4"],
        ["improving one side of a <code>∗</code>", "<code>star_mono</code>, <code>star_mono_left</code>, <code>star_mono_right</code>", "M4"],
        ["a <code>pure</code> stuck inside a <code>∗</code>", "<code>star_pure_left</code>, <code>star_pure_right</code>, <code>pure_star_regroup</code>", "M4, M9"],
        ["you need <code>l₁ ≠ l₂</code> and have no hypothesis", "<code>two_cells_distinct</code> — separation <i>proves</i> non-aliasing", "M4"],
        ["chaining entailments", "<code>entails_refl</code>, <code>entails_trans</code>", "M3"],
        ["a precondition too strong or a postcondition too weak", "<code>hoare_consequence</code>", "M6"],
        ["a <code>;;</code> to split", "<code>hoare_seq</code>", "M6"],
        ["one cell of many, and a rule that mentions one", "<code>hoare_frame</code>, plus a <code>heapLocal_*</code> and a <code>Preserves</code> proof", "M8"],
        ["a <code>Preserves</code> obligation", "<code>preserves_of_heapOnly</code> for heap-only frames, <code>preserves_of_storeStable</code> for commands that never touch the store", "M8, M9"],
        ["a linked list to unfold or refold", "<code>listRep_cons_unfold</code>, <code>listRep_cons_fold</code>", "M10"],
        ["two list segments to join", "<code>lseg_append</code>, <code>lseg_listRep</code>", "M10"],
        ["moving an assumption across a <code>∗</code>", "<code>wand_intro</code>, <code>wand_elim</code>, <code>star_wand_adjunction</code>", "M11"],
        ["working backwards from a postcondition", "<code>hoare_iff_entails_wp</code>, then <code>wp_seq</code>, <code>wp_mono</code>, <code>wp_skip</code>, <code>wp_assign</code>", "M12"],
        ["a loop", "<code>partialHoare_while</code> for partial correctness, <code>hoare_while_variant</code> for total", "M13"]
      ],
      cap: "Two habits make this table redundant faster than memorisation does: the names are systematic (<code>star_</code>, <code>hoare_</code>, <code>heapLocal_</code>, <code>wp_</code>, <code>union_</code>, <code>disjoint_</code>), and <code>exact?</code> in the editor will search for you once you can state the goal precisely."
    },

    /* ================= Discipline ================= */

    {
      t: "h3",
      s: "Proof discipline"
    },
    {
      t: "p",
      h: "Five rules. They are not style preferences: each one is a specific failure this development would have suffered, and each was earned somewhere you can point at."
    },
    {
      t: "ol",
      items: [
        "<b>Prove semantic lemmas before you introduce notation.</b> Notation hides definitions, which is useful only once you no longer need to see them.",
        "<b>Keep primitive specifications small.</b> A write rule mentions one cell. If your rule mentions two, you have baked a frame into it and it will not compose.",
        "<b>Separate heap algebra from program semantics.</b> <code>star_assoc</code> must not mention commands; <code>hoare_write</code> must not do a <code>funext</code>. When you catch yourself doing pointwise heap reasoning inside a Hoare proof, stop and extract a lemma.",
        "<b>Avoid automation early.</b> <code>simp</code> closing a goal about disjoint union teaches you nothing about disjoint union. Build tactics after the manual proofs, not instead of them.",
        "<b>Draw the heap decomposition before writing Lean.</b> Almost every hard proof in this course is bookkeeping about <code>h = (h₁ ∪ h₂) ∪ h₃</code>. Two minutes with a pen saves twenty in the editor."
      ]
    },
    {
      t: "steps",
      title: "Where each rule was earned",
      items: [
        { k: "1 · Semantics before notation", h: "<p>M1 and M2 prove <code>write_shadow</code>, <code>union_assoc</code>, <code>disjoint_union_left</code> before <code>↦</code> or <code>∗</code> exist. That ordering is why M4 is so short. <code>star_comm</code> and <code>star_mono</code> are two tactics each; <code>star_assoc_left</code>, the longest thing in the chapter, is six, and all it does is apply <code>disjoint_union_left.mp</code>, <code>disjoint_union_right.mpr</code> and <code>union_assoc</code> and put the six slots back in a different order. Every one of those three already existed. Had <code>∗</code> come first, each M4 proof would have had to unfold to a heap argument, and you would have proved <code>union_assoc</code> four times inline with slightly different phrasing each time.</p>" },
        { k: "2 · Small primitives", h: "<p><code>hoare_write</code> mentions exactly one cell. <code>write_with_frame</code> — the two-cell version — is not a primitive; it is a four-line derivation. It names <code>hoare_write l (.const new) old</code> as <code>base</code> and hands it to <code>hoare_frame</code> along with two side conditions: <code>heapLocal_write</code>, saying the command is local, and <code>preserves_of_heapOnly _ (heapOnly_pointsTo other w)</code>, saying the frame is a heap-only assertion and therefore cannot be disturbed by anything the command does to the store. Had the two-cell rule been the primitive, you would need a three-cell version, and a version for the case where the second cell is a list, and so on forever. The frame rule exists so that the list is one item long.</p>" },
        { k: "3 · Algebra apart from semantics", h: "<p>Check the M7 proofs: not one contains a <code>funext</code>. Every heap-level fact they need — <code>singleton_same</code>, <code>write_singleton</code>, <code>erase_singleton</code> — arrives as a named lemma from M1. This is what makes the address-expression refactor set out at the end of M13 tractable: the semantics changes in one place and the heap algebra is untouched, because they were never entangled.</p>" },
        { k: "4 · Automation last", h: "<p>The corpus uses <code>simp</code> sixty-four times, and where those uses sit is the whole argument. Thirty-five are in M5, grinding the fuel-indexed <code>run</code> against <code>Exec</code> — bookkeeping with no separation-logic content. Seventeen more are in M0–M2, and five of those are the shape-A pattern to the letter: <code>funext x</code>, then <code>by_cases</code>, then <code>simp</code> as the last line with nothing after it. M4, M10, M11 and M12 — the algebra of <code>∗</code>, the list predicates, the wand, and <code>wp</code> — contain not one <code>simp</code> between them. It is a finisher, not an opener. A <code>simp</code>-only proof of <code>union_assoc</code> would be shorter and would leave you unable to state <i>why</i> union is associative — which is the fact you need when you switch to finite heaps in M14 and have to prove it again by a different argument.</p>" },
        { k: "5 · Draw it first", h: "<p><code>splits_assoc</code>, <code>star_assoc_left</code>, <code>lseg_append</code>, <code>hoare_frame</code>: four of the hardest proofs here, and all four are the same picture — a heap in three pieces, re-bracketed. Once the picture is on paper, the Lean is a transcription; without it, you are doing the re-bracketing and the tactic search simultaneously, and the tactic search is what will fail.</p>" }
      ]
    },
    {
      t: "note",
      kind: "warn",
      title: "The rule that is hardest to keep",
      h: "Rule 4. Once a <code>simp</code> call closes a goal you will not go back and find out why it closed. The moment that costs you is error 2 above: <code>simp [Heap.write, hne]</code> fails, and if you never learned that <code>simp</code> is orienting <code>hne</code> as a left-to-right rewrite rule, the message is opaque and the fix — <code>hne.symm</code> — is invisible. Automation you do not understand is not leverage; it is a proof you cannot repair."
    },

    /* ================= Ideas ================= */

    {
      t: "h3",
      s: "The ideas worth keeping"
    },
    {
      t: "ul",
      items: [
        "<b>Ownership is exact.</b> <code>l ↦ v</code> owns one cell. Everything else follows from taking that literally.",
        "<b>Separation implies non-aliasing.</b> <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂</code> <i>proves</i> <code>l₁ ≠ l₂</code>. Side conditions became theorems.",
        "<b>Small specifications scale.</b> A one-cell write rule is reusable in a heap of a million cells, unchanged, via one structural rule.",
        "<b>The frame rule is a theorem about the semantics.</b> It holds because commands are local. Break locality — with fixed-address allocation, with a “heap size” primitive — and it fails.",
        "<b>Recursive predicates fuse shape and ownership.</b> One assertion says both “these pointers form a list” and “I own every cell in it”.",
        "<b>∗ and -∗ are an adjoint pair.</b> Not two connectives, one adjunction.",
        "<b>The logic is algebraic, and heaps are only one model.</b> Everything in Phase 1 used exactly: a partial commutative monoid. Replace heaps with permissions, tokens, ghost state, protocol states, or fractional ownership, and the same laws hold. That is why one framework can serve concurrency, refinement, and program logic at once — and it is the single most useful thing to carry out of this course."
      ]
    },
    {
      t: "p",
      h: "The second item is worth seeing once as Lean rather than as a slogan, because it is what the whole apparatus buys. Exactness plus separation makes an aliased assertion not merely unproved but <i>unsatisfiable</i> — which is exactly the counterexample that kills fixed-address allocation in M14:"
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- The postcondition of the framed \`alloc-at\` triple, made concrete.
-- \`∗\` forces the two cells apart, so asking for \`l\` twice is asking for
-- a heap that does not exist.
example (l : Loc) : ((l ↦ 0) ∗ (l ↦ 7)) ⊢ aFalse := by
  intro σ h hstar
  exact two_cells_distinct l l 0 7 σ h hstar rfl`,
      cap: "The last line is eight arguments long and every one of them is forced, so it is worth counting them once. <code>two_cells_distinct</code> takes four explicit arguments — <code>l₁ l₂ v₁ v₂</code> — giving <code>(l ↦ 0) ∗ (l ↦ 7) ⊢ fact (fun _ =&gt; l ≠ l)</code>. That <code>⊢</code> is <code>Entails</code>, which is a <code>def</code> for <code>∀ σ h, P σ h → Q σ h</code>, so three more arguments <code>σ h hstar</code> apply it and land on <code>fact (fun _ =&gt; l ≠ l) σ h</code>. <code>fact φ</code> is <code>fun σ _ =&gt; φ σ</code>, so that <i>is</i> <code>l ≠ l</code>, which is <code>l = l → False</code> — hence the eighth argument, <code>rfl</code>, and the result is <code>False</code>. The goal is <code>aFalse σ h</code>, and <code>aFalse</code> is <code>fun _ _ =&gt; False</code>. Nothing is coerced anywhere; the term type-checks because every one of those definitions unfolds without being asked. In classical Hoare logic <code>[l] = 0 ∧ [l] = 7</code> is also unsatisfiable, but you have to notice; here the contradiction is delivered by the definition of <code>∗</code>."
    },
    {
      t: "p",
      h: "The last item deserves its own screen, because it is the one that survives this particular Lean file. Go back through Phase 1 and ask what any of it assumed about heaps. The answer is: <b>nothing except six laws</b>. Write the interface down and every field of it is a lemma you already proved."
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- The whole of Phase 1 used exactly this much structure.
structure PCM where
  Carrier   : Type
  compat    : Carrier → Carrier → Prop      -- "these two can be combined"
  op        : Carrier → Carrier → Carrier   -- total; meaningful when compat
  unit      : Carrier
  compat_symm    : ∀ a b, compat a b → compat b a
  compat_unit    : ∀ a, compat unit a
  op_unit_left   : ∀ a, op unit a = a
  op_comm        : ∀ a b, compat a b → op a b = op b a
  op_assoc       : ∀ a b c, op (op a b) c = op a (op b c)
  compat_op_left : ∀ a b c, compat (op a b) c ↔ compat a c ∧ compat b c

-- Heaps are one model. Every field is a lemma you already proved in M2.
def HeapPCM : PCM where
  Carrier        := Heap
  compat         := Heap.disjoint
  op             := Heap.union
  unit           := Heap.empty
  compat_symm    := fun _ _ => disjoint_symm
  compat_unit    := disjoint_empty_left
  op_unit_left   := union_empty_left
  op_comm        := fun _ _ => union_comm
  op_assoc       := union_assoc
  compat_op_left := fun _ _ _ => disjoint_union_left`,
      cap: "Compiled against the M12 prelude. Note that no field takes a proof of compatibility as an <i>argument</i> to <code>op</code>: the operation is total and compatibility is a separate predicate, which is the same design decision as left-biased <code>Heap.union</code>, for the same reason."
    },
    {
      t: "p",
      h: "The <code>fun _ _ =&gt;</code> wrappers in <code>HeapPCM</code> are not noise, and if you have wondered why some Lean lemmas need arguments you never seem to supply, this is the answer in miniature. A <code>structure</code> field is stated with <b>explicit</b> binders — <code>op_comm : ∀ a b, compat a b → op a b = op b a</code> — but <code>union_comm</code> was proved as <code>theorem union_comm {h₁ h₂ : Heap} (hd : Heap.disjoint h₁ h₂) : …</code>, with its two heaps <b>implicit</b>. So <code>union_comm</code> alone does not have the field's type: it is missing two visible arguments. <code>fun _ _ =&gt; union_comm</code> introduces them, discards them, and lets unification recover them from <code>hd</code>. The same wrapper appears on <code>compat_symm</code> and <code>compat_op_left</code> for exactly this reason, and is absent from <code>op_assoc</code>, <code>op_unit_left</code> and <code>compat_unit</code> — because <code>union_assoc</code>, <code>union_empty_left</code> and <code>disjoint_empty_left</code> were all stated with explicit heap arguments. Look back at the M2 signatures and the pattern of wrappers reads off exactly."
    },
    {
      t: "tbl",
      head: ["PCM law", "Proved for heaps as", "What it powers"],
      rows: [
        ["<code>compat</code> is symmetric", "<code>disjoint_symm</code>", "<code>star_comm</code>, <code>splits_comm</code>"],
        ["the unit is compatible with everything", "<code>disjoint_empty_left</code>, <code>disjoint_empty_right</code>", "<code>star_emp_left_intro</code>, <code>star_emp_right_intro</code>"],
        ["the unit is a unit", "<code>union_empty_left</code>, <code>union_empty_right</code>", "<code>star_emp_left</code>, <code>star_emp_right</code>"],
        ["<code>op</code> commutes on compatible pairs", "<code>union_comm</code>", "<code>star_comm</code>"],
        ["<code>op</code> is associative", "<code>union_assoc</code>", "<code>star_assoc_left</code>, <code>star_assoc_right</code>"],
        ["compatibility distributes over <code>op</code>", "<code>disjoint_union_left</code>, <code>disjoint_union_right</code>", "<code>splits_assoc</code>, both associativity laws for <code>∗</code>"]
      ],
      cap: "Six laws. Every structural law of <code>∗</code> and <code>-∗</code> follows from them plus the definitions: <code>star_comm</code>, both associativity laws, the four <code>emp</code> laws, <code>star_mono</code> and its two one-sided forms, and the whole of M11. Not one of those proofs ever looks at what a heap <i>is</i>. Exactly three theorems do look, and they are worth knowing by name because they mark the boundary — <code>pointsTo_value_unique</code> and <code>pointsTo_not_emp</code> in M3, and <code>two_cells_distinct</code> in M4. All three are statements about <code>↦</code>, and all three need a fact about <code>Heap.singleton</code> that no monoid supplies. That is the same boundary the aside below draws around exactness."
    },
    {
      t: "p",
      h: "So the transfer is mechanical. Take any other partial commutative monoid — fractional permissions, where <code>compat</code> is “the shares sum to at most one”; token multisets, where <code>compat</code> is always true and <code>op</code> is multiset union; ghost state in a state-transition system, where <code>compat</code> is “these two ghost fragments are consistent” — instantiate <code>PCM</code>, and every law of <code>∗</code>, <code>emp</code> and <code>-∗</code> comes back unchanged, with the same proofs. Nothing in M4 or M11 would have to be reopened, because nothing in them ever asked. What you would have to redo is the short list in the caption above — the three theorems about <code>↦</code> — plus every locality proof in M8, since those are about commands and not about the monoid at all."
    },
    {
      t: "detail",
      title: "What the PCM does not give you",
      tag: "aside",
      open: false,
      blocks: [
        { t: "p", h: "Being precise about the boundary is what makes the claim useful rather than a slogan. Three things in this development are <b>not</b> consequences of the monoid structure." },
        { t: "p", h: "<b>The store.</b> <code>Store</code> is total and never splits, which is why <code>star</code> passes the same <code>σ</code> to both sides and why the frame rule needs the extra hypothesis <code>Preserves c R</code>. A frame can be destroyed by an assignment to a program variable without a single heap cell changing. Swapping the heap model out does not touch that; a framework that also splits the store is doing something the PCM does not describe." },
        { t: "p", h: "<b>Locality.</b> <code>HeapLocal</code> is a property of <code>Exec</code>, not of heaps. The PCM tells you what <code>∗</code> means; it says nothing about whether your commands respect it. M8 proves locality one constructor at a time, and M14 exhibits a command for which it is false." },
        { t: "p", h: "<b>Exactness.</b> That <code>l ↦ v</code> means <code>h = Heap.singleton l v</code> and not <code>h l = some v</code> is a choice about the assertion language, not about the algebra. The monoid is the same either way; the logic is not. Exactness is what makes <code>two_cells_distinct</code> provable, and “at least this” would make it false." }
      ]
    },

    /* ================= Inventory ================= */

    {
      t: "h3",
      s: "What you have built"
    },
    {
      t: "p",
      h: "A complete separation logic, from the empty file: a heap PCM; assertions and entailment; <code>∗</code>, <code>emp</code>, and the BI laws; a toy imperative language with relational and executable semantics proved equivalent; safe Hoare triples; small-footprint load / write / free rules; a semantic frame theorem; verified copy and move programs; recursive list and list-segment predicates with the append theorem; the magic wand and its adjunction; weakest preconditions; and the loop rules for partial and total correctness."
    },
    {
      t: "p",
      h: "In names, so you can find any of it. Everything below is in <code>lean/corpus.lean</code>, which compiles as one file under Lean 4.32.2 with no imports and no <code>sorry</code>."
    },
    {
      t: "dl",
      items: [
        { k: "Model", h: "<code>Loc</code>, <code>Val</code>, <code>Heap</code>, <code>Var</code>, <code>Store</code>, <code>Assertion</code>, <code>State</code>" },
        { k: "M1 · cells", h: "<code>Heap.empty</code>, <code>Heap.singleton</code>, <code>Heap.write</code>, <code>Heap.erase</code>; <code>singleton_same</code>, <code>singleton_other</code>, <code>write_same</code>, <code>write_other</code>, <code>erase_same</code>, <code>erase_other</code>, <code>write_shadow</code>, <code>erase_write_same</code>, <code>write_comm</code>, <code>write_singleton</code>, <code>erase_singleton</code>" },
        { k: "M2 · the monoid", h: "<code>Heap.disjoint</code>, <code>Heap.union</code>, <code>Heap.splits</code>; <code>disjoint_symm</code>, <code>disjoint_empty_left</code>, <code>disjoint_empty_right</code>, <code>singleton_disjoint</code>, <code>singleton_disjoint_iff</code>, <code>union_of_none</code>, <code>union_of_some</code>, <code>union_eq_none</code>, <code>union_empty_left</code>, <code>union_empty_right</code>, <code>union_assoc</code>, <code>union_comm</code>, <code>disjoint_union_left</code>, <code>disjoint_union_right</code>, <code>splits_empty_left</code>, <code>splits_comm</code>, <code>splits_assoc</code>" },
        { k: "M3 · assertions", h: "<code>Entails</code>, <code>AssertionEquiv</code>, <code>aTrue</code>, <code>aFalse</code>, <code>aAnd</code>, <code>aOr</code>, <code>aExists</code>, <code>emp</code>, <code>pointsTo</code>, <code>fact</code>, <code>pure</code>; <code>pointsTo_value_unique</code>, <code>pointsTo_not_emp</code>, <code>entails_refl</code>, <code>entails_trans</code>, <code>and_left</code>, <code>and_right</code>, <code>and_intro</code>" },
        { k: "M4 · separating conjunction", h: "<code>star</code>; <code>star_emp_left</code>, <code>star_emp_right</code>, <code>star_emp_left_intro</code>, <code>star_emp_right_intro</code>, <code>star_comm</code>, <code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>star_mono</code>, <code>star_mono_left</code>, <code>star_mono_right</code>, <code>star_or_left</code>, <code>star_exists_left</code>, <code>two_cells_distinct</code>, <code>star_swap_middle</code>, <code>star_rotate_left</code>, <code>star_rotate_right</code>, <code>star_pure_left</code>, <code>star_pure_right</code>" },
        { k: "M5 · the language", h: "<code>Atom</code>, <code>Atom.eval</code>, <code>Store.set</code>, <code>BExpr</code>, <code>BExpr.eval</code>, <code>Cmd</code>, <code>Exec</code>, <code>run</code>; <code>exec_skip_inv</code>, <code>exec_deterministic</code>, <code>run_sound</code>, <code>run_mono</code>, <code>run_le</code>, <code>run_complete</code>" },
        { k: "M6 · triples", h: "<code>Hoare</code>, <code>PartialHoare</code>, <code>subst</code>; <code>hoare_consequence</code>, <code>hoare_skip</code>, <code>hoare_seq</code>, <code>hoare_assign</code>, <code>assign_constant</code>, <code>assign_twice</code>" },
        { k: "M7 · small footprints", h: "<code>hoare_load</code>, <code>hoare_write</code>, <code>hoare_free</code>, <code>clearCell</code>, <code>clearCell_spec</code>, <code>readAndFree</code>, <code>readAndFree_spec</code>" },
        { k: "M8 · locality and framing", h: "<code>HeapLocal</code>, <code>Preserves</code>, <code>HeapOnly</code>; <code>preserves_of_heapOnly</code>, <code>heapOnly_pointsTo</code>, <code>heapOnly_emp</code>, <code>heapOnly_star</code>, <code>heapLocal_skip</code>, <code>heapLocal_assign</code>, <code>heapLocal_load</code>, <code>heapLocal_write</code>, <code>heapLocal_free</code>, <code>heapLocal_seq</code>, <code>hoare_frame</code>, <code>write_with_frame</code>" },
        { k: "M9 · verified programs", h: "<code>StoreStable</code>, <code>storeStable_write</code>, <code>storeStable_free</code>, <code>preserves_of_storeStable</code>, <code>hoare_write_val</code>, <code>pure_star_regroup</code>, <code>copyCell</code>, <code>copyCell_spec</code>, <code>moveCell</code>, <code>exec_seq_assoc</code>, <code>moveCell_spec</code>, <code>preserves_load_fact</code>" },
        { k: "M10 · linked structures", h: "<code>node</code>, <code>listRep</code>, <code>lseg</code>; <code>listRep_nil</code>, <code>listRep_cons_unfold</code>, <code>listRep_cons_fold</code>, <code>node_cells_distinct</code>, <code>concrete_list</code>, <code>aExists_mono</code>, <code>lseg_append</code>, <code>lseg_listRep</code>" },
        { k: "M11 · the wand", h: "<code>wand</code>; <code>wand_intro</code>, <code>wand_elim</code>, <code>star_wand_adjunction</code>, <code>wand_mono</code>" },
        { k: "M12 · weakest preconditions", h: "<code>wp</code>; <code>hoare_iff_entails_wp</code>, <code>wp_skip</code>, <code>wp_assign</code>, <code>wp_seq</code>, <code>wp_mono</code>, <code>heap_eq_singleton</code>, <code>wp_free_emp</code>, <code>wp_write</code>" },
        { k: "M13 · loops", h: "<code>partial_of_total</code>, <code>bTrue</code>, <code>bFalse</code>, <code>partialHoare_skip</code>, <code>partialHoare_seq</code>, <code>partialHoare_consequence</code>, <code>partialHoare_ite</code>, <code>loop_invariant</code>, <code>partialHoare_while</code>, <code>hoare_while_variant</code>, <code>counterGuard</code>, <code>countdown</code>, <code>countdown_spec</code>" }
      ]
    },
    {
      t: "quote",
      h: "That is a small but genuine separation-logic implementation, rather than a collection of Hoare-logic examples."
    },
    {
      t: "note",
      kind: "info",
      title: "Next",
      h: "Two things are deliberately left undone, and both are good next sessions: the address-expression refactor with the two linked-list capstones (M13), and allocation (M14)."
    },
    {
      t: "p",
      h: "The module numbers in brackets say where each is <i>described</i>, not which chapter does the work. M13 closes by setting out the address-expression refactor and the two linked-list capstones; M14 sets out allocation, complete with the <code>alloc</code> constructor, the counterexample against fixed addresses, and four exercise statements with no proofs behind them. Neither is in <code>corpus.lean</code>, and that is the point of the brackets."
    },
    {
      t: "p",
      h: "Each tests a different rule from the list above. The refactor tests rule 3. Our <code>Cmd</code> has <code>load : Var → Loc → Cmd</code>, <code>write : Loc → Atom → Cmd</code>, <code>free : Loc → Cmd</code> — literal addresses, which is why you cannot dereference a pointer held in a variable and why the list capstones are not expressible. The fix replaces each <code>Loc</code> by an <code>Atom</code> and threads <code>a.eval s.store</code> through the semantics. If heap algebra really is separate from program semantics, that should cost you the primitive rules and nothing else: locality, the frame rule and the <code>wp</code> equations should go through with the same proofs, because not one of them ever asks how an address was obtained. Allocation tests the frame rule itself: it is the standard place where locality is lost, and repairing it teaches you what locality was actually demanding all along."
    },
    {
      t: "dod",
      h: "You can take any symbol in this workbook and unfold it, from memory, to the <code>Store → Heap → Prop</code> underneath. Given an unfamiliar goal, you can say within a few seconds whether it is a heap equality, an entailment or a triple, and name the first two tactics. You can read a Lean error message and locate the mistake it is reporting rather than the line it points at. And you can state, in one sentence, what this logic assumed about memory — a partial commutative monoid — and therefore say what else the same proofs would serve."
    }
  ]
});
