/* M3 — Assertions, entailment, and exact ownership
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m3 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm3',
  num: 'M3',
  phase: 'Phase 1 · Semantic foundations',
  title: 'Assertions, entailment, and exact ownership',
  blurb: 'The non-separating part of the logic — and the subtle distinction between “true” and “true and I own nothing”.',

  orient: {
    youWill: [
      'Say what relation stands in for equality between assertions, and why the one-directional one is primitive even though <code>propext</code> makes the two-sided one a genuine equation.',
      'Prove an entailment by writing a function of three arguments, and <b>refute</b> one by instantiating it at a single chosen state.',
      'Define exactness in Lean, and prove that <code>emp</code> and <code>l ↦ v</code> have it while <code>aTrue</code> does not.',
      'Tell <code>fact φ</code> from <code>pure φ</code>, and say which side of a turnstile each one belongs on.',
      'Read a goal Lean prints as <code>fact (fun x =&gt; v₁ = v₂) σ h</code> and recognise that it <i>is</i> the goal <code>v₁ = v₂</code>.'
    ],
    needs: [
      'M1’s lookup equations <code>singleton_same</code> and <code>singleton_other</code>, and <code>Heap.empty</code>.',
      'The refutation shape for heaps: apply both sides at the location where they disagree, and land on two different <code>Option</code> constructors.',
      'No proof below uses anything from M2 — but the argument M2 could only give in English is what this chapter is aimed at.'
    ],
    payoff: 'Every triple in the rest of the course has an assertion on each side. Read those assertions as ownership rather than description and the frame rule stops being a surprise; read them the other way and none of Phase 2 makes sense.'
  },

  blocks: [

    /* ================================================================
       1 — the relation
       ================================================================ */

    { t: 'h3', s: 'What stands in for equality' },

    { t: 'p', h: '<code>=</code> is not false. Mutually entailing assertions genuinely are equal — <code>funext</code> twice, then <code>propext</code> pointwise, four lines, and the proof is in the aside below. <code>=</code> is merely useless. It is symmetric, and almost nothing the logic says about a pair of assertions is: a precondition gets strengthened, a postcondition weakened, a list predicate unfolded one step in the direction that throws information away. Take the one-directional relation as the primitive and the symmetric one comes back as its conjunction with itself.' },

    { t: 'code', src: `abbrev Assertion := Store → Heap → Prop` },

    { t: 'p', h: '<code>Prop</code>, not <code>Bool</code>: an assertion quantifies over heaps and over locations, so there is no hope of deciding one and no reason to want to. Both arguments are always present even when an assertion ignores one — <code>emp</code> and <code>l ↦ v</code> below never read the store, <code>fact φ</code> never reads the heap — because one uniform type is what lets <code>aAnd</code>, <code>Entails</code> and eventually <code>∗</code> be written once instead of in variants. And because <code>Assertion</code> is an <code>abbrev</code>, the application <code>P σ h</code> elaborates even though <code>P</code>’s type is not syntactically an arrow.' },

    { t: 'code', src: `def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h
infix:40 " ⊢ " => Entails

def AssertionEquiv (P Q : Assertion) : Prop := Entails P Q ∧ Entails Q P
infix:40 " ⊣⊢ " => AssertionEquiv` },

    { t: 'anat',
      src: `def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h`,
      parts: [
        { m: 'Entails', h: 'A plain <code>def</code>. So a goal displayed as <code>P ⊢ Q</code> yields to <code>intro σ h hp</code> with nothing in front of it, and you will never write <code>unfold Entails</code> in this course.' },
        { m: '∀ σ h', h: 'Quantified over <i>both</i> components of the state. An entailment is a statement about every state at once, which is why proving one begins by fixing an arbitrary one and refuting one ends by choosing a particular one.' },
        { m: 'P σ h → Q σ h', h: 'Ordinary implication. No resource accounting whatsoever: <code>⊢</code> is inclusion of sets of states. Every substructural thing this logic does lives in the <i>connectives</i>, and none of it lives here. Hold onto that, because when <code>l ↦ v ⊢ emp</code> turns out to be false the reason will have nothing to do with implication — it will be that the two sides describe different heaps.' }
      ] },

    { t: 'detail', title: 'Mutual entailment is equality, and the course still does not use it', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: '<code>AssertionEquiv P Q</code> is <code>P ⊢ Q ∧ Q ⊢ P</code>, and once <code>⊢</code> is known to be a preorder that makes <code>⊣⊢</code> an equivalence relation. It is also, in Lean, indistinguishable from equality:' },
        { t: 'code', tag: 'illustration',
          src: `theorem equiv_eq (P Q : Assertion) (h : P ⊣⊢ Q) : P = Q := by
  funext σ hh
  exact propext ⟨h.1 σ hh, h.2 σ hh⟩`,
          cap: 'Compiles against the M3 prelude. Two <code>funext</code>s in one tactic, one per argument, then propositional extensionality at the point.' },
        { t: 'p', h: 'So you could in principle <code>rw</code> with an assertion equivalence anywhere. The workbook never does, for two reasons. <code>propext</code> is an axiom, and a proof that reaches for it in place of a one-line entailment has learned nothing. More practically, an equation between assertions can only be <i>used</i> by rewriting, whereas <code>h : P ⊢ Q</code> is a function you can apply to a state — which is how every lemma in Phase 1 gets consumed.' }
      ] },

    { t: 'note', kind: 'warn', title: 'You are about to see two turnstiles',
      h: 'Lean prints the goal separator as <code>⊢</code>, and <code>⊢</code> has just been declared as notation for <code>Entails</code>. Goals in this chapter contain the symbol twice, meaning different things. The <b>leftmost</b> one, at the start of the line, is Lean’s; every other one is <code>Entails</code>.' },

    { t: 'state',
      src: `l : Loc
v₁ v₂ : Val
⊢ aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact fun x => v₁ = v₂`,
      cap: 'The opening goal of exercise 1: prove that <code>aAnd (l ↦ v₁) (l ↦ v₂)</code> entails <code>fact (fun _ =&gt; v₁ = v₂)</code>. Note that the printer renamed the anonymous binder to <code>x</code> and dropped the parentheses the source had.' },

    { t: 'p', h: 'A proof of <code>P ⊢ Q</code> is therefore a function of three arguments: a store, a heap, and a proof of the premise. When the goal is a function type the shortest proof is a function, and reaching for <code>by</code> is a reflex worth suppressing.' },

    { t: 'ex',
      id: 'm3-2',
      name: 'entails_refl / entails_trans',
      hard: false,

      why: 'These two are the glue. The name <code>entails_trans</code> occurs fourteen times in the corpus and <code>entails_refl</code> eleven; M4’s <code>star_swap_middle</code> is three entailments chained by two nested <code>entails_trans</code> with no <code>intro</code>, no heap and no <code>by</code> anywhere in it. Proving them as terms now is what lets later chapters read as equational reasoning instead of state-by-state grinding. They also settle the question the chapter opened on: <code>⊢</code> is a preorder, so <code>⊣⊢</code> is an equivalence, and nothing further is needed.',
      setup: 'No tactics required, and none is an improvement. <code>P ⊢ Q</code> unfolds to <code>∀ σ h, P σ h → Q σ h</code> — a function type with three arguments.',
      goal: `theorem entails_refl (P : Assertion) : P ⊢ P
theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R`,

      hints: [
        'Unfold the notation in your head. <code>P ⊢ P</code> is <code>∀ σ h, P σ h → P σ h</code>. Which function has that type?',
        'Give the terms directly — identity and composition.',
        'Reflexivity: <code>fun _ _ hp =&gt; hp</code>. The two underscores are the store and the heap; nothing in the proof looks at them.',
        'Transitivity: you hold <code>h₁ : ∀ σ h, P σ h → Q σ h</code> and <code>h₂ : ∀ σ h, Q σ h → R σ h</code> and must produce <code>∀ σ h, P σ h → R σ h</code>. Feed <code>hp</code> to <code>h₁</code>, the result to <code>h₂</code>, at the <b>same</b> <code>σ</code> and <code>h</code> both times: <code>fun σ h hp =&gt; h₂ σ h (h₁ σ h hp)</code>.'
      ],

      sol: `theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp

theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun σ h hp => h₂ σ h (h₁ σ h hp)`,

      expl: 'Entailment is implication under two binders, so reflexivity is the identity function and transitivity is composition. Recognising that saves three <code>intro</code>s and, more importantly, makes the later chained proofs legible.',

      walk: [
        { tac: 'theorem entails_refl (P : Assertion) : P ⊢ P :=',
          h: '<code>:=</code> and not <code>:= by</code>. The type is a function type, so what follows is a function.' },
        { tac: 'fun _ _ hp => hp',
          h: 'Three binders for three arguments. The first two are the store and the heap, discarded because nothing depends on them; the third is the premise, returned unchanged. Lean accepts this against a goal displayed as <code>P ⊢ P</code> because <code>Entails</code> is an ordinary <code>def</code> and the elaborator sees the arrows underneath.' },
        { tac: 'theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=',
          h: 'The three assertions are implicit, so every call site is <code>entails_trans hA hB</code> with the assertions never mentioned. That is the whole reason M4’s chained proofs fit on one line.' },
        { tac: 'fun σ h hp => h₂ σ h (h₁ σ h hp)',
          h: 'Composition. <code>h₁ σ h hp : Q σ h</code> is exactly the third argument <code>h₂ σ h</code> wants, and the result is <code>R σ h</code>. Here the store and heap must be named, because they are passed on twice: the content of the proof is that the <i>same</i> state is threaded through both hypotheses.' }
      ],

      deep: [
        { t: 'p', h: 'The tactic version is longer and says nothing extra, but tracing it shows what the term is doing — and it is the first place in the course that needs <code>apply</code>.' },
        { t: 'code', tag: 'illustration',
          src: `theorem entails_trans_tac {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R := by
  intro σ h hp
  apply h₂
  exact h₁ σ h hp`,
          cap: 'Compiles against the M3 prelude.' },
        { t: 'trace', title: 'entails_trans in tactic mode',
          start: `P Q R : Assertion
h₁ : P ⊢ Q
h₂ : Q ⊢ R
⊢ P ⊢ R`,
          steps: [
            { tac: 'intro σ h hp',
              state: `P Q R : Assertion
h₁ : P ⊢ Q
h₂ : Q ⊢ R
σ : Store
h : Heap
hp : P σ h
⊢ R σ h`,
              h: 'Three introductions consume the three binders hidden inside <code>Entails</code>.' },
            { tac: 'apply h₂',
              state: `P Q R : Assertion
h₁ : P ⊢ Q
h₂ : Q ⊢ R
σ : Store
h : Heap
hp : P σ h
⊢ Q σ h`,
              h: '<b><code>apply</code></b>, first appearance. Where <code>exact e</code> demands that <code>e</code> already prove the goal, <code>apply e</code> unifies the <i>conclusion</i> of <code>e</code>’s type with the goal and leaves the arguments it could not determine as new goals. Here it matches <code>R ?σ ?h</code> against <code>R σ h</code>, which pins both, and the undetermined third argument becomes the goal <code>Q σ h</code>. This is the step the term writes as the outer application <code>h₂ σ h (…)</code>: <code>apply</code> is that application built backwards, from the result towards the arguments.' },
            { tac: 'exact h₁ σ h hp',
              state: 'No goals.',
              h: 'The inner application, written out. <code>apply h₁</code> would work here too and leave <code>P σ h</code>, closed by <code>exact hp</code> — three tactics where the term has one.' }
          ],
          done: 'No goals.' }
      ],

      pitfall: 'Composing in the wrong order. <code>fun σ h hp =&gt; h₁ σ h (h₂ σ h hp)</code> is what you write if you read the hypotheses left to right, and Lean rejects it: <i>Application type mismatch: The argument <code>hp</code> has type <code>P σ h</code> but is expected to have type <code>Q σ h</code> in the application <code>h₂ σ h hp</code></i>. The message names both the offending argument and the application it sits in, which is the habit to build — in proofs made of applications the error nearly always tells you which of two similar terms you swapped. The other slip is dropping the state arguments and writing <code>h₂ (h₁ hp)</code>; an entailment is a function of <b>three</b> arguments, not one.',
      variants: 'Both statements are unconditional, and that is the point of the exercise: entailment is the boring part, deliberately. Contrast M4, where <code>star_comm</code> needs <code>disjoint_symm</code> and <code>star_assoc_left</code> needs <code>union_assoc</code>.<br><br><b>Is <code>⊢</code> a partial order?</b> Not as stated — mutual entailment gives <code>P ⊣⊢ Q</code>, not <code>P = Q</code> — but <code>equiv_eq</code> upgrades it, so morally yes.<br><br><b>Could entailment be indexed by a state?</b> Nothing to write down: the quantifier is <i>inside</i> <code>Entails</code>, so a hypothesis <code>P ⊢ Q</code> already speaks about every state. A version that fixed one state would make <code>entails_trans</code> equally trivial and every later rule unusable, because the rule of consequence has to hold at the state the program reaches, which the rule does not know.'
    },

    /* ================================================================
       2 — the connectives that only carry the heap
       ================================================================ */

    { t: 'sec', s: 'The connectives that only carry the heap along' },

    { t: 'p', h: 'Five definitions, lifted pointwise from <code>Prop</code>. None of them is separation logic; they are what separation logic has to sit on top of.' },

    { t: 'code', src: `def aTrue  : Assertion := fun _ _ => True

def aFalse : Assertion := fun _ _ => False

def aAnd (P Q : Assertion) : Assertion := fun σ h => P σ h ∧ Q σ h

def aOr  (P Q : Assertion) : Assertion := fun σ h => P σ h ∨ Q σ h

def aExists {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h` },

    { t: 'dl', items: [
      { k: 'aTrue', h: 'Holds of every state; everything entails it, by <code>fun _ _ _ =&gt; trivial</code> (<code>trivial</code> being the proof of <code>True</code>). This is <b>not</b> <code>emp</code>: a heap with a million cells satisfies <code>aTrue</code>.' },
      { k: 'aFalse', h: 'Holds of no state and entails everything, by <code>fun _ _ hf =&gt; hf.elim</code>. What an unsatisfiable precondition collapses to — which is how a vacuous specification announces itself, and how the closing section will say “this assertion has no model”.' },
      { k: 'aAnd P Q', h: 'Both, <i>of the same heap</i>. Not the interesting connective, and the whole of M4 is the discovery of how uninteresting it is.' },
      { k: 'aOr P Q', h: 'Either, of the same heap. Case-split postconditions.' },
      { k: 'aExists P', h: '<code>P</code> is a <i>family</i> of assertions indexed by <code>α</code>. From M10 on you write <code>aExists (fun n =&gt; …)</code> constantly, because a linked-list predicate has to quantify over the tail pointer it does not know.' }
    ] },

    { t: 'detail', title: 'What <code>{α : Sort u}</code> is doing there', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: '<code>Sort u</code> rather than <code>Type</code>: <code>Sort 0</code> is <code>Prop</code> and <code>Sort (n+1)</code> is <code>Type n</code>, so quantifying over <code>Sort u</code> permits an existential over a <i>proof</i> as well as over data. Rarely wanted, free to allow.' },
        { t: 'p', h: 'The bare <code>u</code> is an <b>auto-bound universe variable</b>: Lean sees an undeclared identifier in universe position and quietly inserts <code>universe u</code>. If an error message ever mentions <code>u_1</code>, that is one of these, named by the elaborator rather than by you.' }
      ] },

    { t: 'ex',
      id: 'm3-3',
      name: 'and_left / and_right / and_intro',
      hard: false,

      why: 'This is the complete theory of <code>∧</code> here, and it exists so that the contrast in M4 has something to be a contrast with. <code>and_left</code> lets you <b>forget</b> a conjunct. The separating analogue <code>P ∗ Q ⊢ P</code> is not provable and must not be, because forgetting <code>Q</code> would mean silently leaking the memory <code>Q</code> owns. Prove these in one line each, and when the separating versions have to destructure a splitting of the heap on the way in you will know exactly which line was the substructural one.',
      setup: '<code>aAnd P Q</code> is <code>fun σ h =&gt; P σ h ∧ Q σ h</code>. Lean’s <code>And</code> is a one-constructor structure, so <code>h.1</code> and <code>h.2</code> are its fields (also <code>h.left</code>, <code>h.right</code>) and <code>⟨a, b⟩</code> builds one. All three proofs are terms.',
      goal: `theorem and_left  (P Q : Assertion) : aAnd P Q ⊢ P
theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q
theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R`,

      hints: [
        'Same shape as the previous exercise. Write <code>fun</code> and ask what type Lean wants back.',
        'Projections and pairing. One term each.',
        'For <code>and_left</code> the third argument has type <code>aAnd P Q σ h</code>, which <i>is</i> <code>P σ h ∧ Q σ h</code>; take its first component. For <code>and_intro</code> the return type is a conjunction, so the body is <code>⟨…, …⟩</code>, each component being one of the given entailments applied to <code>σ</code>, <code>h</code> and <code>hp</code>.'
      ],

      sol: `theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1

theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2

theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=
  fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩`,

      expl: '<code>aAnd</code> is <code>And</code> under two binders, so <code>.1</code>, <code>.2</code> and <code>⟨_,_⟩</code> do all the work. The corresponding facts for <code>∗</code> are not projections, and that difference is M4’s entire subject.',

      walk: [
        { tac: 'theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1',
          h: 'Watch the name: the third binder is called <code>h</code> and it is a <i>proof</i>, while everywhere else in this chapter <code>h</code> is a heap — the heap here is the second <code>_</code>. <code>h.1</code> resolves because Lean puts the type of <code>h</code> into weak head normal form, unfolds <code>aAnd</code>, beta-reduces, and finds the structure <code>And</code>.' },
        { tac: 'theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2',
          h: 'The mirror image. Swap <code>.1</code> and <code>.2</code> and the error names both types, so the pair is self-checking.' },
        { tac: 'theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=',
          h: 'The direction that <i>builds</i> a conjunction. Both hypotheses share the premise <code>P</code>, and that shared premise is what makes this the introduction rule for <code>∧</code> and not for <code>∗</code>, where the premise would have to be cut in two.' },
        { tac: 'fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩',
          h: '<code>hp</code> is used <b>twice</b>, at the same <code>σ</code> and the same <code>h</code>. One resource, handed to both conjuncts. That single duplication is the whole difference between <code>∧</code> and <code>∗</code>, and it is why the separating version of this rule has to take a splitting of the heap as extra input.' }
      ],

      deep: [
        { t: 'trace', title: 'and_intro in tactic mode, to watch the two obligations appear',
          start: `P Q R : Assertion
h₁ : P ⊢ Q
h₂ : P ⊢ R
⊢ P ⊢ aAnd Q R`,
          steps: [
            { tac: 'intro σ h hp',
              state: `P Q R : Assertion
h₁ : P ⊢ Q
h₂ : P ⊢ R
σ : Store
h : Heap
hp : P σ h
⊢ aAnd Q R σ h`,
              h: 'The goal is displayed folded. It is definitionally <code>Q σ h ∧ R σ h</code>, which is what the next tactic relies on.' },
            { tac: 'constructor',
              state: `case left
P Q R : Assertion
h₁ : P ⊢ Q
h₂ : P ⊢ R
σ : Store
h : Heap
hp : P σ h
⊢ Q σ h

case right
P Q R : Assertion
h₁ : P ⊢ Q
h₂ : P ⊢ R
σ : Store
h : Heap
hp : P σ h
⊢ R σ h`,
              h: 'One goal per field, labelled by the field names. Look at <code>hp</code>: present in <b>both</b> branches, undiminished. Lean’s context is not linear and neither is <code>∧</code> — which is exactly the property <code>∗</code> gives up.' },
            { tac: '· exact h₁ σ h hp',
              state: `case right
P Q R : Assertion
h₁ : P ⊢ Q
h₂ : P ⊢ R
σ : Store
h : Heap
hp : P σ h
⊢ R σ h`,
              h: 'The first goal closes and <code>case right</code> is what remains.' },
            { tac: '· exact h₂ σ h hp',
              state: 'No goals.',
              h: 'The term-mode proof <code>⟨h₁ σ h hp, h₂ σ h hp⟩</code> is these two lines with the bookkeeping deleted.' }
          ],
          done: 'No goals.' },
        { t: 'code', tag: 'illustration',
          src: `theorem and_intro_tac {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R := by
  intro σ h hp
  constructor
  · exact h₁ σ h hp
  · exact h₂ σ h hp`,
          cap: 'The traced proof in full. Compiles against the M3 prelude.' },
        { t: 'detail', title: 'Why <code>h.1</code> works on something whose type is <code>aAnd P Q σ h</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'A dot-projection is resolved from the head constant of the type. Here the head is <code>aAnd</code>, not a structure — so Lean unfolds it, beta-reduces the application to <code>σ</code> and <code>h</code>, arrives at <code>P σ h ∧ Q σ h</code>, and now the head is <code>And</code> and <code>.1</code> means <code>And.left</code>.' },
            { t: 'p', h: 'The same mechanism lets <code>intro</code> see through <code>Entails</code> and will let <code>exact</code> accept a proof of <code>v₁ = v₂</code> for a goal displayed as <code>fact …</code>. One rule to internalise: <b>elaboration unfolds definitions, <code>simp</code> does not.</b> A tactic that surprises you by succeeding is usually the first half; one that surprises you by failing is usually the second.' },
            { t: 'p', h: 'It is also why the error for <code>fun _ _ h =&gt; h.2</code> in <code>and_left</code> mentions daggered names:' },
            { t: 'state',
              src: `error: Type mismatch
  h.right
has type
  Q x✝¹ x✝
but is expected to have type
  P x✝¹ x✝`,
              cap: '<code>x✝¹</code> and <code>x✝</code> are the two <code>_</code> binders. Lean invents <b>inaccessible</b> names for them, which you cannot write — correctly, since you declined to name them.' }
          ] }
      ],

      pitfall: 'Beyond pasting <code>.1</code> where <code>.2</code> belongs, the instructive one is debugging with underscores in place. Because <code>_</code> creates inaccessible hypotheses, error messages refer to the store and heap as <code>x✝¹</code> and <code>x✝</code> and you cannot mention them in a fix. Name them while you debug — <code>fun σ h hpq =&gt; hpq.1</code> — and put the underscores back afterwards if you prefer them.',
      variants: '<b>Different premises:</b> <code>(h₁ : P ⊢ Q) (h₂ : P\' ⊢ R) : aAnd P P\' ⊢ aAnd Q R</code> is true as well, by <code>fun σ h hp =&gt; ⟨h₁ σ h hp.1, h₂ σ h hp.2⟩</code>. It is the <code>∧</code>-shadow of M4’s <code>star_mono</code> — and in the <code>∗</code> version you cannot write <code>hp.1</code> at all, because you must destructure a heap splitting first. That extra destructuring is precisely what <code>∗</code> costs.<br><br><b>Drop the shared premise:</b> there is no rule <code>P ⊢ Q → P\' ⊢ R → P ⊢ aAnd Q R</code>. You cannot conjure <code>R</code> out of a <code>P</code> you were never handed. <code>and_intro</code> may use <code>hp</code> twice only because <code>∧</code> is not resource-sensitive.<br><br><b>Reverse <code>and_left</code> into <code>P ⊢ aAnd P Q</code>:</b> false, since <code>Q</code> could be <code>aFalse</code>. One-directionality is what makes <code>and_left</code> a weakening rule.'
    },

    { t: 'p', h: 'Nothing so far has touched the heap: the parameter has been carried and never read. The two definitions that read it are also the reason <code>P ∗ Q ⊢ P</code> will fail.' },

    /* ================================================================
       3 — the two definitions that touch the heap
       ================================================================ */

    { t: 'sec', s: 'Two assertions that name their own heap' },

    { t: 'code', src: `def emp : Assertion := fun _ h => h = Heap.empty

def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v
infix:60 " ↦ " => pointsTo` },

    { t: 'quote', h: '<code>emp</code> means <i>I own nothing.</i><br><code>l ↦ v</code> means <i>I own exactly one cell, namely <code>l</code>, and it contains <code>v</code>.</i>' },

    { t: 'anat',
      src: `def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v
infix:60 " ↦ " => pointsTo`,
      parts: [
        { m: 'fun _ h =>', h: 'The store is ignored: <code>l</code> and <code>v</code> are already fixed by the time the assertion is applied. Every heap assertion in this course is store-independent; only <code>fact</code> and <code>pure</code> read the store.' },
        { m: 'h = Heap.singleton l v', h: 'An <b>equation between heaps</b>. Not <code>h l = some v</code>. This is the one design decision of the chapter and the reason the word is <i>exact</i>.' },
        { m: 'infix:60', h: 'Tighter than <code>∗</code> (<code>infixr:55</code> in M4) and much tighter than <code>⊢</code> (<code>infix:40</code>), so <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂ ⊢ P</code> parses as <code>((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) ⊢ P</code> with no parentheses. The tower 60 &gt; 55 &gt; 40 exists so that the notation reads the way it does on paper.' }
      ] },

    { t: 'note', kind: 'key', title: 'The one thing to remember',
      h: 'Read every assertion as a <b>claim of ownership</b>, in the first person. Not “the heap contains this”, but “this is what I have”. Once that reading is automatic the frame rule stops being surprising.' },

    { t: 'p', h: 'The phrase “pins its heap down” can now be retired in favour of a definition. For each store, at most one heap satisfies the assertion:' },

    { t: 'code', tag: 'illustration',
      src: `def Exact (P : Assertion) : Prop :=
  ∀ σ h₁ h₂, P σ h₁ → P σ h₂ → h₁ = h₂

theorem exact_emp : Exact emp := fun _ _ _ ha hb => by rw [ha, hb]

theorem exact_pointsTo (l : Loc) (v : Val) : Exact (l ↦ v) :=
  fun _ _ _ ha hb => by rw [ha, hb]

theorem not_exact_aTrue : ¬ Exact aTrue := by
  intro hex
  have heq := hex (fun _ => 0) Heap.empty (Heap.singleton 0 0) trivial trivial
  have h0 := congrFun heq 0
  rw [singleton_same] at h0
  exact absurd h0 (by simp [Heap.empty])`,
      cap: 'Compiles against the M3 prelude. <code>Exact</code> is not in the corpus — it is a word this chapter needs, not a definition later chapters use.' },

    { t: 'p', h: 'The two positive proofs are letter for letter the same, and that is the dividend from defining <code>emp</code> and <code>↦</code> as equations: two hypotheses of the form <code>h = …</code> rewrite into each other and nothing is left to do. The refutation instantiates <code>Exact</code> at one store and two heaps that both satisfy <code>aTrue</code>, and reads the resulting heap equation at location <code>0</code>.' },

    { t: 'detail', title: 'Why <code>simp [Heap.empty]</code> is allowed to appear', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'That bracket names a heap operation, which the M1 interface was supposed to have made unnecessary. The lemma it stands in for would be “<code>Heap.empty l = none</code>”, and it was never proved because there is nothing to prove: <code>Heap.empty l</code> reduces on its own. What the bracket buys is not a rewrite, it is permission — <code>simp</code> will not unfold a defined constant unless the constant is named. So <code>Heap.empty</code> is the one heap operation that stays legal inside a bracket, and only at the last step of a refutation, where the goal is <code>¬ (some v = Heap.empty l)</code> and <code>simp</code> has to see the <code>none</code>.' }
      ] },

    { t: 'defn', term: 'Exact ownership',
      h: 'Exactness is what makes a specification a <b>footprint</b>: the precondition of a command names the memory the command may touch, and no more. <code>emp</code> and <code>l ↦ v</code> are exact; <code>aTrue</code> and <code>fact φ</code> are not. The literature calls such assertions <i>precise</i>; this course says exact throughout.',
      cap: 'The property, and what it is for.' },

    { t: 'cmp',
      left: { t: 'The reading we chose (exact)', kind: 'good',
        h: 'The domain of <code>h</code> is <i>exactly</i> <code>{l}</code>. A specification written this way names its own footprint, so <code>{l ↦ v} free l {emp}</code> is true as stated, and larger heaps are recovered by one structural rule.',
        src: `def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v`,
        tag: 'verified' },
      right: { t: 'The reading you would write first (inexact)', kind: 'bad',
        h: '“<code>l</code> is in the domain, and who knows what else is.” Every triple then carries side conditions about the rest of the heap, and <code>{l ↦ v} free l {emp}</code> becomes <b>false</b> — freeing one cell of a big heap does not leave it empty. That is the trade: tiny exact specifications plus one structural rule, instead of large specifications with side conditions.',
        src: `def pointsTo_inexact (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v`,
        tag: 'illustration' } },

    { t: 'detail', title: 'Why <code>emp</code> is an equation and not <code>∀ l, h l = none</code>', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'The two are equivalent, and you might expect the pointwise one to be friendlier.' },
        { t: 'code', tag: 'illustration',
          src: `theorem emp_pointwise (σ : Store) (h : Heap) : emp σ h ↔ ∀ l, h l = none := by
  constructor
  · intro he l
    rw [he]
    rfl
  · intro hl
    funext l
    rw [hl]
    rfl`,
          cap: 'Compiles against the M3 prelude. The backward direction costs one extra tactic, the <code>funext</code> that turns a pointwise statement into an equation of heaps.' },
        { t: 'note', kind: 'warn', title: 'Why those trailing <code>rfl</code>s are not redundant',
          h: 'Elsewhere <code>rw</code> closes such a goal by itself. Here it does not: after <code>rw [he]</code> the goal is <code>Heap.empty l = none</code> and Lean reports <i>unsolved goals</i>. The <code>rfl</code> that <code>rw</code> attempts silently only unfolds <b>reducible</b> definitions, and <code>Heap.empty</code> is an ordinary <code>def</code>; the <code>rfl</code> <i>tactic</i> uses default transparency, unfolds it, and closes the goal. Whenever <code>rw</code> stops one step short of the obvious, this is why.' },
        { t: 'p', h: 'The equation wins because it is a <b>rewrite rule</b>. Given <code>he : emp σ h</code> you write <code>rw [he]</code> and the heap disappears from wherever it stood. With the pointwise version you would apply <code>funext</code> at every use site first. M4’s <code>star_emp_left</code> is, after the destructuring, the single line <code>rw [hu, he, union_empty_left]</code> followed by <code>exact hp</code>; that middle line exists only because <code>emp</code> is an equation. The same argument covers <code>pointsTo</code>, and it is what nearly every proof in M7 and M9 lives on.' }
      ] },

    /* ================================================================
       4 — fact and pure
       ================================================================ */

    { t: 'sec', s: 'Two kinds of “pure”' },

    { t: 'p', h: 'There are two reasonable ways to push an ordinary proposition about the store into an assertion, and the choice between them is the one place in this chapter where a plausible statement comes out false.' },

    { t: 'code', src: `def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ

def pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp` },

    { t: 'ul', items: [
      '<code>fact φ</code> — “<code>φ</code> holds”, saying <b>nothing</b> about the heap. Compatible with owning anything.',
      '<code>pure φ</code> — “<code>φ</code> holds <b>and I own nothing</b>”.'
    ] },

    { t: 'p', h: 'You need both, and which one you need is decided by the connective standing next to it.' },

    { t: 'txt', src: `  aAnd (fact φ) P   ≡   pure φ ∗ P

  fact  pairs with  ∧      (it does not consume heap, so ∧ is right)
  pure  pairs with  ∗      (∗ splits the heap, so the left piece must be empty)` },

    { t: 'p', h: 'The mechanism, since it explains the definition: to satisfy <code>pure φ ∗ P</code> you must cut the heap into two disjoint pieces, one for each side. The <code>emp</code> conjunct forces the left piece to be <code>Heap.empty</code>, so the right piece is the whole heap, and what you have is <code>φ</code> together with <code>P</code> on all of <code>h</code> — which is <code>aAnd (fact φ) P</code>. Delete the <code>emp</code> and the cut is unconstrained; the equivalence dies. M4 proves it both ways round as <code>star_pure_left</code> and <code>star_pure_right</code>.' },

    { t: 'cmp',
      left: { t: '<code>fact φ</code> — a side condition', kind: 'good',
        h: 'For <i>reading a fact off</i> the state without giving anything up. “These two locations are distinct”, “this index is in range”, “this value is nonzero” — all <code>fact</code>. M4’s <code>two_cells_distinct</code> concludes in <code>fact</code> precisely because deriving non-aliasing must not cost you the memory you derived it from.',
        src: `theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :
    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)`,
        tag: 'sketch' },
      right: { t: '<code>pure φ</code> — a resource-free assertion',
        h: 'For sitting next to a <code>∗</code>. <code>pure φ ∗ P</code> says “<code>φ</code>, and separately, <code>P</code>”, and because <code>pure φ</code> owns nothing that is the same as “<code>φ</code> and <code>P</code>”. Write <code>fact φ ∗ P</code> instead and you have something strictly weaker: the <code>fact</code> side is entitled to walk off with an arbitrary chunk of the heap.',
        src: `theorem star_pure_left (φ : Store → Prop) (P : Assertion) :
    pure φ ∗ P ⊢ aAnd (fact φ) P`,
        tag: 'sketch' } },

    { t: 'note', kind: 'tip', title: 'A rule of thumb that always works',
      h: 'Ask which side of the turnstile the proposition is on. In a <b>conclusion</b> you almost always want <code>fact</code>: you are extracting information and keeping the memory. In a <b>hypothesis about to be cut up by <code>∗</code></b> you want <code>pure</code>, so that the cut is forced to hand the whole heap to the other side.' },

    { t: 'p', h: 'Here is the whole vocabulary evaluated on two concrete heaps. The store is irrelevant to every row; take it to be <code>fun _ =&gt; 0</code>.' },

    { t: 'tbl',
      head: ['assertion', 'on <code>Heap.empty</code>', 'on <code>Heap.singleton 3 7</code>', 'reading'],
      rows: [
        ['<code>aTrue</code>', 'holds', 'holds', 'no claim at all'],
        ['<code>emp</code>', 'holds', '<b>fails</b>', 'I own nothing'],
        ['<code>3 ↦ 7</code>', '<b>fails</b>', 'holds', 'I own exactly cell 3, holding 7'],
        ['<code>3 ↦ 8</code>', '<b>fails</b>', '<b>fails</b>', 'I own exactly cell 3, holding 8'],
        ['<code>fact (fun _ =&gt; True)</code>', 'holds', 'holds', 'True is true; the heap is my business, not yours'],
        ['<code>pure (fun _ =&gt; True)</code>', 'holds', '<b>fails</b>', 'True is true <i>and</i> I own nothing']
      ],
      cap: 'The last two rows are the whole difference between <code>fact</code> and <code>pure</code>, and it shows up on one heap out of two.' },

    { t: 'detail', title: 'Four of those rows, checked', tag: 'aside', open: false,
      blocks: [
        { t: 'code', tag: 'illustration',
          src: `example : (3 ↦ 7) (fun _ => 0) (Heap.singleton 3 7) := rfl

example : pure (fun _ => True) (fun _ => 0) Heap.empty := ⟨trivial, rfl⟩

example : ¬ emp (fun _ => 0) (Heap.singleton 3 7) := by
  intro he
  have : Heap.singleton 3 7 3 = Heap.empty 3 := by rw [he]
  rw [singleton_same] at this
  exact absurd this (by simp [Heap.empty])

example : ¬ pure (fun _ => True) (fun _ => 0) (Heap.singleton 3 7) := by
  intro hp
  have : Heap.singleton 3 7 3 = Heap.empty 3 := by rw [hp.2]
  rw [singleton_same] at this
  exact absurd this (by simp [Heap.empty])`,
          cap: 'Compiles against the M3 prelude.' },
        { t: 'p', h: 'The positive rows need no tactics: <code>pointsTo</code> and <code>emp</code> unfold to equations that hold definitionally on literal heaps. The pair has two components because <code>pure φ</code> is <code>aAnd (fact φ) emp</code> — <code>trivial</code> for <code>True</code>, <code>rfl</code> for <code>Heap.empty = Heap.empty</code>. Both negative rows have the same four-line shape: assume it, evaluate the resulting heap equation at the interesting location, land on <code>some _ = none</code>. That shape is the second half of the next exercise.' }
      ] },

    { t: 'p', h: 'Confuse <code>fact</code> and <code>pure</code> and you get statements that look right and are false. The classic one is worth proving both halves of.' },

    { t: 'ex',
      id: 'm3-1',
      name: 'pointsTo_value_unique — and why the obvious statement is false',
      hard: false,

      why: 'If I own exactly cell <code>l</code> holding <code>v₁</code>, <i>and simultaneously</i> own exactly cell <code>l</code> holding <code>v₂</code>, the two descriptions are of one heap, so <code>v₁ = v₂</code>. The exercise delivers two things the rest of the chapter needs. <code>pointsTo_value_unique</code> shows that under <code>∧</code> aliasing is <b>forced</b>: two conjuncts describing one heap had better describe the same cell. And <code>pointsTo_not_emp</code> is the statement “<code>l ↦ v</code> owns something”, discharged once, which is the hypothesis the closing section cannot do without. On the way you learn to read a folded goal and to refute an entailment by producing a single state.',
      setup: 'In scope: everything above, plus <code>singleton_same</code> from M1. <code>Option.some.inj : some a = some b → a = b</code> and <code>absurd : a → ¬a → b</code> are Lean’s. Two theorems are wanted: the one that is true, and the refutation that explains why the tempting one is not it.',
      goal: `-- the version you will be tempted to write:
theorem bad :
    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ pure (fun _ => v₁ = v₂)

-- the version that is actually true:
theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :
    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂)`,

      hints: [
        '<code>P ⊢ Q</code> <i>is</i> <code>∀ σ h, P σ h → Q σ h</code>, so begin with <code>intro</code>. Three things arrive: a store, a heap, and the premise. The store is never looked at.',
        'The premise is an <code>aAnd</code>, so destructure it on arrival: <code>intro σ h ⟨h1, h2⟩</code> gives <code>h1 : h = Heap.singleton l v₁</code> and <code>h2 : h = Heap.singleton l v₂</code> — though Lean displays them folded, as <code>h1 : (l ↦ v₁) σ h</code>.',
        'You want the single equation <code>Heap.singleton l v₁ l = Heap.singleton l v₂ l</code>, since both sides are <code>h l</code>. Mind the direction: <code>rw [h1]</code> hunts for <code>h</code> in the goal, and there is none. Run the equations backwards.',
        'Finish with <code>rw [singleton_same, singleton_same] at this</code> to reach <code>this : some v₁ = some v₂</code>, then <code>exact Option.some.inj this</code>. For the refutation: <code>¬ X</code> is <code>X → False</code>, so <code>intro hcontra</code> hands you the entailment as a hypothesis — and it is a function, so apply it to any store, to <code>Heap.singleton l v</code>, and to <code>rfl</code>. Evaluating the resulting heap equation at <code>l</code> gives <code>some v = none</code>.'
      ],

      sol: `theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :
    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by
  intro σ h ⟨h1, h2⟩
  have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]
  rw [singleton_same, singleton_same] at this
  exact Option.some.inj this

theorem pointsTo_not_emp (l : Loc) (v : Val) :
    ¬ ((l ↦ v) ⊢ emp) := by
  intro hcontra
  have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl
  have : Heap.singleton l v l = Heap.empty l := by rw [h]
  rw [singleton_same] at this
  exact absurd this (by simp [Heap.empty])`,

      solNote: 'The second theorem targets <code>emp</code> rather than <code>pure</code> on purpose: it is the sharper fact. Since <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, anything entailing <code>pure φ</code> also entails <code>emp</code> — compose with <code>and_right (fact φ) emp</code> — so one refutation kills the whole family. Aiming it at <code>bad</code> itself needs one more link, <code>(l ↦ v) ⊢ aAnd (l ↦ v) (l ↦ v)</code>, which is <code>and_intro</code> applied to <code>entails_refl</code> twice; the <code>bad_is_false</code> snippet under “Why it works” skips the chain and refutes <code>bad</code> head-on instead.',
      expl: 'The first proof transports the two heap equations into one equation between singletons, evaluates it at <code>l</code>, and strips the <code>some</code>. The second is a refutation: <code>(l ↦ v) ⊢ emp</code> would give <code>Heap.singleton l v = Heap.empty</code>, and at <code>l</code> that is <code>some v = none</code>. Since <code>pure φ = aAnd (fact φ) emp</code>, the tempting statement implies exactly that, which is why the true conclusion uses <code>fact</code>.',

      walk: [
        { tac: 'intro σ h ⟨h1, h2⟩',
          h: 'Three introductions in one. <code>σ</code> and <code>h</code> come from the <code>∀ σ h</code> inside <code>Entails</code>; the third is the premise, a conjunction, split on arrival. The goal becomes <code>fact (fun x =&gt; v₁ = v₂) σ h</code>, which is definitionally <code>v₁ = v₂</code>.' },
        { tac: 'have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]',
          h: 'The mathematical content, in one line. Both hypotheses say the heap <i>is</i> a particular singleton, so the singletons are equal; evaluating at <code>l</code> is what turns that into something <code>singleton_same</code> can chew on. Anonymous <code>have</code>, so the result is <code>this</code>.' },
        { tac: 'rw [← h1, ← h2]',
          h: 'Inside the <code>have</code>. The arrow reverses each equation, so instead of replacing <code>h</code> by a singleton it replaces the singleton by <code>h</code>. After the first the goal is <code>h l = Heap.singleton l v₂ l</code>; after the second it is <code>h l = h l</code>, which <code>rw</code>’s trailing <code>rfl</code> closes.' },
        { tac: 'rw [singleton_same, singleton_same] at this',
          h: '<code>singleton_same</code> fires twice, once per side, turning <code>this</code> into <code>some v₁ = some v₂</code>. The two entries are not a typo: the first match fixes the lemma’s variables, and the two sides are different instances — <code>v₁</code> and <code>v₂</code> — so one pass leaves the other side untouched.' },
        { tac: 'exact Option.some.inj this',
          h: 'The result has type <code>v₁ = v₂</code>; the goal displays as <code>fact (fun x =&gt; v₁ = v₂) σ h</code>. <code>exact</code> checks up to definitional equality, unfolds <code>fact</code>, and accepts.' },
        { tac: 'theorem pointsTo_not_emp (l : Loc) (v : Val) : ¬ ((l ↦ v) ⊢ emp) := by',
          h: 'The parentheses around <code>(l ↦ v)</code> are unnecessary for parsing and necessary for reading. Lean prints this goal as <code>⊢ ¬l ↦ v ⊢ emp</code>, which is genuinely hard the first time.' },
        { tac: 'intro hcontra',
          h: '<code>¬ X</code> is <code>X → False</code>, so a negation goal is an implication goal. You now hold <code>hcontra : l ↦ v ⊢ emp</code> against the goal <code>False</code>.' },
        { tac: 'have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl',
          h: 'The refutation. <code>hcontra</code> is a function of three arguments, so apply it. The store is arbitrary; the heap is the witness, the one heap on which <code>l ↦ v</code> obviously holds; the premise <code>(l ↦ v) σ (Heap.singleton l v)</code> unfolds to <code>Heap.singleton l v = Heap.singleton l v</code>, hence <code>rfl</code>. Out comes <code>Heap.singleton l v = Heap.empty</code>.' },
        { tac: 'have : Heap.singleton l v l = Heap.empty l := by rw [h]',
          h: 'Evaluate the absurd heap equation at the one location where it is visibly wrong. <code>rw [h]</code> rewrites the left side into <code>Heap.empty</code> and the trailing <code>rfl</code> does the rest.' },
        { tac: 'rw [singleton_same] at this',
          h: 'Once only: the right-hand side is <code>Heap.empty l</code>, which no M1 lemma rewrites. <code>this</code> becomes <code>some v = Heap.empty l</code>, and the goal is still <code>False</code>.' },
        { tac: 'exact absurd this (by simp [Heap.empty])',
          h: 'The refutation argument is <code>by simp [Heap.empty]</code>: naming <code>Heap.empty</code> reduces the goal to <code>¬ (some v = none)</code>, which <code>simp</code> discharges because constructors are disjoint.' }
      ],

      deep: [
        { t: 'trace', title: 'pointsTo_value_unique, tactic by tactic',
          start: `l : Loc
v₁ v₂ : Val
⊢ aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact fun x => v₁ = v₂`,
          steps: [
            { tac: 'intro σ h ⟨h1, h2⟩',
              state: `l : Loc
v₁ v₂ : Val
σ : Store
h : Heap
h1 : (l ↦ v₁) σ h
h2 : (l ↦ v₂) σ h
⊢ fact (fun x => v₁ = v₂) σ h`,
              h: 'Two lessons in one display. <code>intro</code> unfolded <code>Entails</code> unasked. And <code>h1</code> is <i>shown</i> as <code>(l ↦ v₁) σ h</code> but <i>is</i> <code>h = Heap.singleton l v₁</code> — Lean prints the folded form and computes with the unfolded one. To see the unfolded form, re-ascribe: <code>have h1\' : h = Heap.singleton l v₁ := h1</code> is accepted and displays unfolded. Do <b>not</b> reach for <code>show</code>, which retypes the <i>goal</i> and never a hypothesis: <code>show h = Heap.singleton l v₁</code> here fails with <i>\'show\' tactic failed, pattern <code>h = Heap.singleton l v₁</code> is not definitionally equal to target <code>fact (fun x =&gt; v₁ = v₂) σ h</code></i>.' },
            { tac: 'have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]',
              state: `l : Loc
v₁ v₂ : Val
σ : Store
h : Heap
h1 : (l ↦ v₁) σ h
h2 : (l ↦ v₂) σ h
this : Heap.singleton l v₁ l = Heap.singleton l v₂ l
⊢ fact (fun x => v₁ = v₂) σ h`,
              h: 'The goal is untouched and <code>this</code> has appeared. A second anonymous <code>have</code> would shadow it — which is what happens in the second theorem, harmlessly, the first <code>this</code> being dead by then.' },
            { tac: 'rw [singleton_same, singleton_same] at this',
              state: `l : Loc
v₁ v₂ : Val
σ : Store
h : Heap
h1 : (l ↦ v₁) σ h
h2 : (l ↦ v₂) σ h
this : some v₁ = some v₂
⊢ fact (fun x => v₁ = v₂) σ h`,
              h: 'Heaps are now entirely gone from <code>this</code>; what remains is a statement about <code>Option Val</code>.' },
            { tac: 'exact Option.some.inj this',
              state: 'No goals.',
              h: 'The gap between <code>v₁ = v₂</code> and <code>fact (fun x =&gt; v₁ = v₂) σ h</code> is closed by <code>exact</code>’s definitional check, not by any tactic you wrote.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'Inside the <code>have</code>: what the arrow does',
          start: `l : Loc
v₁ v₂ : Val
σ : Store
h : Heap
h1 : (l ↦ v₁) σ h
h2 : (l ↦ v₂) σ h
⊢ Heap.singleton l v₁ l = Heap.singleton l v₂ l`,
          steps: [
            { tac: 'rw [← h1]',
              state: `l : Loc
v₁ v₂ : Val
σ : Store
h : Heap
h1 : (l ↦ v₁) σ h
h2 : (l ↦ v₂) σ h
⊢ h l = Heap.singleton l v₂ l`,
              h: 'There is a second thing this step quietly depends on. <code>h1</code> is <i>displayed</i> as <code>(l ↦ v₁) σ h</code>, which is not syntactically an equation at all, and <code>rw</code> only rewrites with an <code>Eq</code> or an <code>Iff</code>. It works because <code>rw</code> unfolds <code>pointsTo</code> far enough to find the <code>Eq</code> underneath — the same courtesy <code>intro</code> and <code>exact</code> extend, and exactly the one <code>simp</code> refuses in the pitfall below.' },
            { tac: 'rw [← h2]',
              state: 'No goals.',
              h: 'The right-hand side becomes <code>h l</code> as well, so the goal is <code>h l = h l</code> and the trailing <code>rfl</code> closes it. That is why the <code>have</code> body is one tactic and not two.' }
          ],
          done: 'No goals.' },
        { t: 'cmp',
          left: { t: '<code>rw [← h1, ← h2]</code> — works', kind: 'good',
            h: 'Right-to-left: hunt for <code>Heap.singleton l v₁</code>, find it, put <code>h</code> there. The goal collapses to <code>h l = h l</code>.' },
          right: { t: '<code>rw [h1, h2]</code> — fails', kind: 'bad',
            h: 'Left-to-right: hunt for <code>h</code>, which the <code>have</code>’s goal deliberately does not mention.',
            src: `error: Tactic \`rewrite\` failed: Did not find an occurrence of the pattern
  h
in the target expression
  Heap.singleton l v₁ l = Heap.singleton l v₂ l`,
            tag: 'sketch' } },
        { t: 'trace', title: 'pointsTo_not_emp — how to refute an entailment',
          start: `l : Loc
v : Val
⊢ ¬l ↦ v ⊢ emp`,
          steps: [
            { tac: 'intro hcontra',
              state: `l : Loc
v : Val
hcontra : l ↦ v ⊢ emp
⊢ False`,
              h: 'The start line is the display to stare at: <code>¬l ↦ v ⊢ emp</code> is <code>¬ ((l ↦ v) ⊢ emp)</code>, the second turnstile being <code>Entails</code>. After <code>intro</code> it moves into the context and the goal is honest <code>False</code>.' },
            { tac: 'have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl',
              state: `l : Loc
v : Val
hcontra : l ↦ v ⊢ emp
h : emp (fun x => 0) (Heap.singleton l v)
⊢ False`,
              h: 'One universally quantified entailment, instantiated at one carefully chosen state. Nothing else in the proof is creative. Note that you had to <i>invent</i> a store: <code>Store</code> has no canonical element in scope, and any <code>Nat → Nat</code> does, because both assertions ignore it.' },
            { tac: 'have : Heap.singleton l v l = Heap.empty l := by rw [h]',
              state: `l : Loc
v : Val
hcontra : l ↦ v ⊢ emp
h : emp (fun x => 0) (Heap.singleton l v)
this : Heap.singleton l v l = Heap.empty l
⊢ False`,
              h: '<code>h</code> is an equation between functions, so to get a contradiction you apply both sides to an argument, and the informative argument is <code>l</code>.' },
            { tac: 'rw [singleton_same] at this',
              state: `l : Loc
v : Val
hcontra : l ↦ v ⊢ emp
h : emp (fun x => 0) (Heap.singleton l v)
this : some v = Heap.empty l
⊢ False`,
              h: 'The left side computes; the right side stays folded until the last line reduces it to <code>none</code>.' },
            { tac: 'exact absurd this (by simp [Heap.empty])',
              state: 'No goals.',
              h: '<code>some v = none</code> is false because <code>Option</code>’s constructors are disjoint, which <code>simp</code> knows.' }
          ],
          done: 'No goals.' },
        { t: 'code', tag: 'illustration',
          src: `theorem bad_is_false (l : Loc) (v : Val) :
    ¬ (aAnd (l ↦ v) (l ↦ v) ⊢ pure (fun _ => v = v)) := by
  intro hbad
  have h := hbad (fun _ => 0) (Heap.singleton l v) ⟨rfl, rfl⟩
  have : Heap.singleton l v l = Heap.empty l := by rw [h.2]
  rw [singleton_same] at this
  exact absurd this (by simp [Heap.empty])`,
          cap: '<code>bad</code>, refuted head-on. Compiles against the M3 prelude. Two things changed from <code>pointsTo_not_emp</code>: the premise witness is <code>⟨rfl, rfl⟩</code> because the premise is a conjunction, and <code>h.2</code> picks the <code>emp</code> half out of <code>pure</code>. Note where the contradiction comes from — nothing about <code>v</code> or the store is involved. The premise <i>owns a cell</i> and <code>pure</code> demands you own nothing. An entailment may throw information away; it may never throw resources away, because the conclusion has to describe the same heap.' },
        { t: 'detail', title: 'When the values differ — or the locations do — the premise has no models at all', tag: 'aside', open: false,
          blocks: [
            { t: 'code', tag: 'illustration',
              src: `theorem aAnd_pointsTo_ne (l : Loc) (v₁ v₂ : Val) (hne : v₁ ≠ v₂) :
    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ aFalse := by
  intro σ h hpq
  exact hne (pointsTo_value_unique l v₁ v₂ σ h hpq)`,
              cap: 'Compiles against the M3 prelude.' },
            { t: 'p', h: 'Read the second line carefully: <code>pointsTo_value_unique l v₁ v₂</code> is an entailment, therefore a function, so applying it to <code>σ</code>, <code>h</code> and <code>hpq</code> yields a proof of <code>v₁ = v₂</code>, which <code>hne</code> eats. Applying a proved entailment as a function is the everyday way to use these lemmas — <code>entails_trans</code> is that move, packaged.' },
            { t: 'p', h: 'Different <i>locations</i> collapse the premise too, and this one has to be proved from scratch, with <code>singleton_other</code> doing on the right what <code>singleton_same</code> does on the left:' },
            { t: 'code', tag: 'illustration',
              src: `theorem aAnd_pointsTo_ne_loc (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ aFalse := by
  intro σ h ⟨ha, hb⟩
  have : Heap.singleton l₁ v₁ l₁ = Heap.singleton l₂ v₂ l₁ := by rw [← ha, ← hb]
  rw [singleton_same, singleton_other l₂ l₁ v₂ hne] at this
  exact absurd this (by simp)`,
              cap: 'Compiles against the M3 prelude. <code>singleton_other</code> wants its arguments as <code>l₂ l₁ v₂</code> with a proof of <code>l₁ ≠ l₂</code>: its hypothesis is <code>x ≠ l</code>, probe location first.' },
            { t: 'p', h: 'So <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂)</code> entails <code>aFalse</code>, hence entails everything — which is why the <code>l₁ ≠ l₂</code> version of the main theorem is provable and worthless.' }
          ] }
      ],

      pitfall: 'The last line is where people stick, and the cause is a mismatch between what <code>exact</code> can see and what <code>simp</code> can. Holding <code>this : some v₁ = some v₂</code> against a goal displayed as <code>fact (fun x =&gt; v₁ = v₂) σ h</code>, <code>exact this</code> fails — <i>Type mismatch: <code>this</code> has type <code>some v₁ = some v₂</code> but is expected to have type <code>fact (fun x =&gt; v₁ = v₂) σ h</code></i> — correctly, and <code>Option.some.inj</code> is the fix. But <code>simpa using this</code> <b>also</b> fails (<code>simpa using e</code> is <code>simp</code> on the goal and on <code>e</code>, then <code>exact</code> — the trailing <code>a</code> being <i>assumption</i>, as in <code>rwa</code>), and its message spells out how close it got: <i>Type mismatch: After simplification, term <code>this</code> has type <code>v₁ = v₂</code> but is expected to have type <code>fact (fun x =&gt; v₁ = v₂) σ h</code></i>. <code>simp</code> reduced <code>this</code> to literally the proposition the goal denotes and still refused, because it does not unfold <code>fact</code> and so cannot see that the goal already <i>is</i> <code>v₁ = v₂</code>. The cure is to say what the goal really is: <code>show v₁ = v₂</code>, and then <code>simpa using this</code> works. Reach for <code>show</code> whenever a tactic refuses a goal you can see is right.',
      variants: '<b>Weaken <code>fact</code> to <code>pure</code>:</b> false, refuted head-on by <code>bad_is_false</code> and generically by <code>pointsTo_not_emp</code>. The single failing point is that the premise owns a cell.<br><br><b>Strengthen <code>emp</code> to <code>aTrue</code> in the second theorem:</b> <code>(l ↦ v) ⊢ aTrue</code> is true, by <code>fun _ _ _ =&gt; trivial</code>. <code>aTrue</code> makes no claim on the heap and <code>emp</code> makes the strongest one; forgetting they differ is the same slip as confusing <code>fact</code> with <code>pure</code>.<br><br><b>Replace <code>∧</code> by <code>∗</code>:</b> the entailment becomes <i>provable</i>, and vacuously. <code>(l ↦ v₁) ∗ (l ↦ v₂)</code> asks for two disjoint heaps both containing <code>l</code>, which by <code>singleton_disjoint_iff</code> forces <code>l ≠ l</code>. The premise is unsatisfiable so it entails everything, <code>pure</code> and <code>aFalse</code> included.<br><br><b>Let the locations differ:</b> <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ fact (fun _ =&gt; v₁ = v₂)</code> stays <b>provable</b> when <code>l₁ ≠ l₂</code>, again for the uninteresting reason — one heap cannot equal two singletons at different locations. (An unsatisfiable premise makes an entailment <i>true</i>, not false; if you wrote “false” here, re-read <code>Entails</code>.) So the content of <code>pointsTo_value_unique</code> is not really that the values agree. It is that <code>∧</code> <b>forces</b> aliasing where <code>∗</code> forbids it, and exactly one of those two connectives gives you a usable specification language.'
    },

    /* ================================================================
       5 — what is now sayable, and the one symbol still missing
       ================================================================ */

    { t: 'sec', s: 'One symbol short' },

    { t: 'p', h: 'The argument that <code>P ∗ P</code> has no models was missing three things: an assertion, a property some assertions have and others do not, and a way to say an assertion has no model. All three are in hand. The property is <code>Exact P</code>, and <code>exact_pointsTo</code> discharges it for <code>l ↦ v</code>. Owning something is <code>¬ (P ⊢ emp)</code>, discharged for <code>l ↦ v</code> by the second half of the exercise you have just done. Having no model needs no new machinery whatsoever: it is <code>P ⊢ aFalse</code>, and <code>aAnd (l ↦ v₁) (l ↦ v₂)</code> with <code>v₁ ≠ v₂</code> is one assertion that satisfies it.' },

    { t: 'p', h: 'What is left is the connective.' },

    { t: 'code', tag: 'sketch',
      src: `theorem star_self_emp (P : Assertion) (hex : Exact P) : P ∗ P ⊢ emp :=
  sorry   -- ∗ is the one thing M3 does not have`,
      cap: 'Does not compile, and only for one reason: <code>∗</code> does not exist yet. Every other symbol on the line does.' },

    { t: 'p', h: 'Whatever <code>∗</code> turns out to be, this proof will be three steps and all three are already available: <code>P ∗ P</code> hands over a splitting with <code>P</code> on both halves, <code>hex</code> makes the halves equal, and a heap disjoint from itself is empty. The concrete case will not even need <code>Exact</code> — M4’s <code>two_cells_distinct</code>, with both locations taken to be the same <code>l</code>, concludes <code>fact (fun _ =&gt; l ≠ l)</code>, so <code>(l ↦ v) ∗ (l ↦ v) ⊢ aFalse</code> falls out of a lemma about non-aliasing.' },

    { t: 'p', h: 'So <code>∗</code> is not a sixth entry in the list of connectives. It is the only one whose definition has to mention the heap twice, which is why it will need all nine laws of M2 and why nothing above needed any of them. And it has to be a definition under which <code>P ∗ Q ⊢ P</code> fails while <code>P ∗ emp ⊢ P</code> holds. Those two pull in opposite directions, and getting both is M4’s first exercise.' },

    { t: 'dod', h: 'You can state an assertion, prove an entailment as a term, refute one at a single state, and say in Lean what it means for an assertion to own exactly its own heap.' }

  ]
});
