/* M6 — Hoare triples
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m6",
  "num": "M6",
  "phase": "Phase 2 · Program logic",
  "title": "Hoare triples",
  "blurb": "Connecting assertions to execution — and the structural rules that let you stop unfolding the semantics.",

  "orient": {
    "youWill": [
      "Read <code>Hoare P c Q</code> as the statement it unfolds to, and produce that unfolding on paper before Lean shows it to you.",
      "Prove the three structural rules — consequence, skip, sequencing — directly from the <code>Exec</code> relation of M5.",
      "State the assignment axiom without ever defining syntactic substitution, and see why a shallow embedding makes that free.",
      "Verify a two-command program by choosing an intermediate assertion, and recognise that choosing it <i>is</i> the proof.",
      "Use <code>show</code> deliberately: to turn a goal that displays as <code>fact …</code> into the arithmetic statement it definitionally is.",
      "Say precisely what the existential in <code>Hoare</code> rules out, and exhibit a command for which it fails."
    ],
    "needs": [
      "M3 — <code>Assertion := Store → Heap → Prop</code>, <code>emp</code>, <code>fact</code>, <code>aAnd</code>, and <code>Entails</code> written <code>⊢</code>. In particular that an entailment hypothesis is applied to <i>three</i> arguments: <code>hpre σ h hp</code>.",
      "M5 — <code>Cmd</code>, the <code>State</code> structure, and the inductive relation <code>Exec c s s'</code>. Above all: a missing derivation means <i>stuck or diverging</i>, and that is the only way faults are modelled.",
      "M0 — <code>intro</code>, <code>obtain</code>, <code>refine</code> with <code>?_</code> holes, <code>exact</code>, <code>constructor</code>, <code>show</code>, and the anonymous constructor <code>⟨…⟩</code> with its automatic flattening."
    ],
    "payoff": "After this chapter you never unfold <code>Exec</code> again except to prove a primitive rule; every later verification is composition of triples, and M7–M9 are exactly that."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "Phase 1 gave you assertions: predicates on a store and a heap, with an ownership reading. M5 gave you execution: an inductive relation whose derivations <i>are</i> the terminating runs. Neither mentions the other. A Hoare triple is the single definition that joins them, and it is short enough to read in one breath."
    },
    {
      "t": "code",
      "src": "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap"
    },
    {
      "t": "quote",
      "h": "From <b>every</b> state satisfying <code>P</code>, the command runs without getting stuck and lands in a state satisfying <code>Q</code>."
    },
    {
      "t": "anat",
      "src": "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap",
      "parts": [
        {
          "m": ": Prop",
          "h": "A triple is a <i>proposition</i>, not a piece of syntax and not an inductively generated judgement. There is no derivation system here: <code>Hoare P c Q</code> is a statement about the semantics, and the \"rules\" you prove below are ordinary theorems about that statement. This is the difference between a <b>semantic</b> and a <b>syntactic</b> program logic, and it is why you will never have to prove a soundness theorem: soundness is the definition."
        },
        {
          "m": "∀ σ h",
          "h": "Two separate binders, a store and a heap — not one binder of type <code>State</code>. That is forced by M3: an <code>Assertion</code> is <code>Store → Heap → Prop</code>, so it eats its two arguments separately. Quantifying over a <code>State</code> instead would mean writing <code>P s.store s.heap</code> everywhere in the precondition, which is uglier at exactly the point where it matters most."
        },
        {
          "m": "P σ h →",
          "h": "The precondition is a hypothesis, so it is only ever <i>used</i>, never proved. Consequently a triple with an unsatisfiable precondition is trivially true — <code>Hoare aFalse c Q</code> holds for every <code>c</code> and <code>Q</code>, by <code>intro σ h hp</code> then <code>exact hp.elim</code>. That is not a bug; it is the degenerate end of the contravariance that <code>hoare_consequence</code> makes official. Note the asymmetry: an <i>unsatisfiable precondition</i> makes a triple vacuous, but an <i>uninformative postcondition</i> does not — <code>Hoare P c aTrue</code> still demands that <code>c</code> run to completion, and two commands later in this chapter fail it."
        },
        {
          "m": "∃ s'",
          "h": "The load-bearing quantifier of the whole chapter. Asserting that a final state <i>exists</i> is asserting that a derivation of <code>Exec</code> exists, and M5 built <code>Exec</code> so that no derivation exists for a faulting or a diverging run. So this one symbol simultaneously claims: no memory fault, and termination."
        },
        {
          "m": "Exec c ⟨σ, h⟩ s'",
          "h": "<code>⟨σ, h⟩</code> is the anonymous constructor building a <code>State</code> from its two fields. You need it because <code>Exec</code> relates states while assertions consume components; the triple is the seam where the two representations meet, and the conversion has to happen somewhere. Lean prints this back to you as <code>{ store := σ, heap := h }</code>, which is the same term written out."
        },
        {
          "m": "Q s'.store s'.heap",
          "h": "And here the conversion runs the other way: <code>s'</code> is a <code>State</code>, <code>Q</code> wants a store and a heap, so you project. Every goal in this chapter will display those projections literally, sometimes applied to a state you just built — Lean is happy to print <code>{ store := σ.set x 10, heap := h }.store</code> rather than simplify it, and you have to learn to read past that."
        }
      ]
    },
    {
      "t": "detail",
      "title": "Why the projections do not get in your way: structure eta",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "A goal or hypothesis containing <code>{ store := σ, heap := h }.store</code> looks like it needs a simplification step. It does not. Lean reduces projections of an explicit constructor automatically (iota reduction), so that term <i>is</i> <code>σ</code> as far as the type checker is concerned."
        },
        {
          "t": "p",
          "h": "The reverse direction is the one that surprises people. In the <code>hoare_seq</code> proof below you will obtain a hypothesis of type <code>Exec c₂ { store := s₁.store, heap := s₁.heap } s₂</code> and feed it to a constructor that wants <code>Exec c₂ s₁ s₂</code>. That works because Lean 4 has <b>eta for structures</b>: rebuilding a structure from its own projections gives back a term definitionally equal to the original, even when the original is an opaque variable."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "-- structure eta: a state is its own two projections, by rfl\nexample (s : State) : ({ store := s.store, heap := s.heap } : State) = s := rfl",
          "cap": "Compiles against the M6 prelude. On paper you would not even write this down; in Lean it is the reason <code>exact</code> succeeds where you expected a mismatch."
        },
        {
          "t": "p",
          "h": "Without structure eta you would need an explicit lemma <code>State.eta</code> and a rewrite in the middle of every sequencing proof. Worth knowing it is there, precisely so that you do not go looking for the rewrite."
        }
      ]
    },
    {
      "t": "p",
      "h": "Notice how much that existential is doing. It asserts, simultaneously: no memory fault, no divergence, and the postcondition. For the loop-free fragment that is automatic; once loops arrive in M13 it becomes a genuine <b>total correctness</b> claim, and we will need a separate partial-correctness triple for comparison:"
    },
    {
      "t": "code",
      "src": "def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap"
    },
    {
      "t": "cmp",
      "left": {
        "t": "<code>Hoare</code> — total correctness",
        "h": "<code>s'</code> is bound by <code>∃</code> and <code>Exec</code> sits on the <i>right</i> of the arrow, so you must <b>produce</b> a run. Nothing is vacuous: to prove the triple you exhibit a derivation.",
        "kind": "good"
      },
      "right": {
        "t": "<code>PartialHoare</code> — partial correctness",
        "h": "<code>s'</code> is bound by <code>∀</code> and <code>Exec</code> is a <i>hypothesis</i>, so you may <b>assume</b> a run. If no run exists the statement is vacuously true, which is exactly the escape hatch that makes non-terminating programs satisfiable."
      }
    },
    {
      "t": "p",
      "h": "That difference is not a technicality, and it is worth breaking the rule to see it. Two commands have no derivations at all, for two different reasons; both satisfy every partial triple and no total one."
    },
    {
      "t": "h4",
      "s": "Failure one — the memory fault"
    },
    {
      "t": "code",
      "tag": "illustration",
      "src": "-- a load from the empty heap satisfies every partial triple, vacuously\ntheorem partial_load_emp (x : Var) (l : Loc) (Q : Assertion) :\n    PartialHoare emp (.load x l) Q := by\n  intro σ h s' he hex\n  cases hex with\n  | load hl => rw [he] at hl; simp [Heap.empty] at hl\n\n-- but no total triple, not even with the weakest possible postcondition\ntheorem not_hoare_load_emp (x : Var) (l : Loc) :\n    ¬ Hoare emp (.load x l) aTrue := by\n  intro hc\n  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | load hl => simp [Heap.empty] at hl",
      "cap": "Compiles against the M6 prelude. <code>cases hex</code> asks which constructor could have produced the derivation; only <code>Exec.load</code> can, and it carries <code>hl : h l = some v</code>, which contradicts <code>h = Heap.empty</code>."
    },
    {
      "t": "h4",
      "s": "Failure two — divergence"
    },
    {
      "t": "code",
      "tag": "illustration",
      "src": "def forever : Cmd := .loop (.equals (.const 0) (.const 0)) .skip\n\ntheorem no_exec_forever : ∀ {c : Cmd} {s s' : State}, c = forever → Exec c s s' → False := by\n  intro c s s' hc hex\n  induction hex with\n  | loopFalse hb =>\n      cases hc; simp [BExpr.eval, Atom.eval] at hb\n  | loopTrue hb hbody hrest ihb ihr => exact ihr hc\n  | _ => cases hc\n\ntheorem partial_forever (P Q : Assertion) : PartialHoare P forever Q := by\n  intro σ h s' hp hex\n  exact (no_exec_forever rfl hex).elim\n\ntheorem not_hoare_forever : ¬ Hoare emp forever aTrue := by\n  intro hc\n  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty rfl\n  exact no_exec_forever rfl hex",
      "cap": "Compiles against the M6 prelude. The induction is on the <i>derivation</i>: <code>loopFalse</code> needs the guard false, which <code>simp</code> refutes; <code>loopTrue</code> hands you an induction hypothesis for the same loop, so the argument closes on itself. Every other constructor is killed by the equation <code>hc</code>."
    },
    {
      "t": "detail",
      "title": "Why <code>no_exec_forever</code> is stated with an equation instead of just <code>¬ Exec forever s s'</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "The statement you would write on paper is <code>Exec forever s s' → False</code>. Write that in Lean and <code>induction</code> refuses before you have typed a single case:"
        },
        {
          "t": "state",
          "src": "error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)\n  forever",
          "cap": "Produced by <code>intro hex; induction hex</code> on the direct statement."
        },
        {
          "t": "p",
          "h": "<code>Exec</code> is an inductive family indexed by the command. The recursor generalises over that index, so <code>induction</code> can only be applied when the index is a local variable — otherwise the induction hypothesis it would have to generate is not even well-formed. Here the index is the literal constant <code>forever</code>."
        },
        {
          "t": "p",
          "h": "The standard fix is to generalise the index by hand and record what it was in an equation. That is what <code>{c : Cmd} → c = forever → Exec c s s' → False</code> does: <code>c</code> is now a variable, so the induction goes through, and each case begins by using <code>hc : c = forever</code> — either to specialise (<code>cases hc</code> in the <code>loopFalse</code> branch, turning the guard into <code>0 == 0</code>) or to derive a contradiction (<code>cases hc</code> in the catch-all, where <code>hc</code> equates two different constructors of <code>Cmd</code>). You will see the same manoeuvre again in M13."
        }
      ]
    },
    {
      "t": "p",
      "h": "Big-step semantics cannot tell these two apart — both are simply \"no derivation\" — and neither can <code>PartialHoare</code>. That is the price of the big-step presentation, and M13 is where it is paid. In the other direction there is nothing to pay: a total triple always implies the partial one, using determinism from M5."
    },
    {
      "t": "code",
      "tag": "illustration",
      "src": "theorem partial_of_total {P Q : Assertion} {c : Cmd} (ht : Hoare P c Q) :\n    PartialHoare P c Q := by\n  intro σ h s' hp hex\n  obtain ⟨s'', hex'', hq⟩ := ht σ h hp\n  have hs : s' = s'' := exec_deterministic hex hex''\n  subst hs\n  exact hq",
      "cap": "Compiles against the M6 prelude. <code>exec_deterministic</code> is doing the only real work: <code>PartialHoare</code> hands you an <i>arbitrary</i> run <code>s'</code>, while your total triple produced a run to some <code>s''</code> of its own choosing, and nothing but determinism identifies the two. <code>subst hs</code> then rewrites <code>s'</code> away, leaving <code>hq</code> to close the goal."
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "The notation you cannot have",
      "h": "You cannot write <code>⦃P⦄ c ⦃Q⦄</code> in Lean 4: <code>⦃ ⦄</code> is already the syntax for strict-implicit binders, and the parser will not give it up. <code>{P} c {Q}</code> collides with structure-instance and set-builder notation. Pick something else (<code>⟪P⟫ c ⟪Q⟫</code> works) or just write <code>Hoare P c Q</code>, which is what the verified development does."
    },
    {
      "t": "p",
      "h": "Living without the braces costs you nothing except familiarity. It does cost you one habit: because <code>Hoare</code> is an ordinary application, the arguments are positional, and a triple whose pre- and postcondition you swap by accident is still well-typed. Read the order off the definition — <code>Hoare P c Q</code>, precondition first — and check it once per proof."
    },
    {
      "t": "h3",
      "s": "Substitution, done semantically"
    },
    {
      "t": "p",
      "h": "The classical assignment axiom is <code>{Q[e/x]} x := e {Q}</code>, and the awkward part in a formal development is <code>Q[e/x]</code> — syntactic substitution into an assertion. Because our assertions are <i>functions</i>, we can sidestep syntax entirely:"
    },
    {
      "t": "code",
      "src": "def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ h => Q (Store.set σ x (e.eval σ)) h"
    },
    {
      "t": "anat",
      "src": "def subst (x : Var) (e : Atom) (Q : Assertion) : Assertion :=\n  fun σ h => Q (Store.set σ x (e.eval σ)) h",
      "parts": [
        {
          "m": "(e : Atom)",
          "h": "The expression stays syntax — it is an <code>Atom</code>, an element of the inductive type from M5. Only the assertion is semantic. That asymmetry is the whole trick: you need syntax for the thing the program executes, and you do not need syntax for the thing you assert."
        },
        {
          "m": "fun σ h =>",
          "h": "<code>subst x e Q</code> is itself an <code>Assertion</code>, so it must be a function of a store and a heap. Building it as a lambda rather than by recursion on the structure of <code>Q</code> is what makes the definition three tokens long."
        },
        {
          "m": "Store.set σ x (e.eval σ)",
          "h": "The store you would get after running <code>x := e</code>. Two things are worth separating. First, <code>e.eval σ</code> uses the <i>old</i> store — the right-hand side is read before the write, which is what the assignment axiom means. Second, capture: in a syntactic <code>Q[e/x]</code> you must worry about a binder inside <code>Q</code> capturing a variable free in <code>e</code>. Here <code>Q</code> has no binders over program variables at all — it is a function of the whole store — so there is nothing to capture and no side condition to state."
        },
        {
          "m": "Q (Store.set σ x (e.eval σ)) h",
          "h": "The heap <code>h</code> is passed through untouched — assignment does not touch memory. When you meet <code>hoare_load</code> in M7 the corresponding rule cannot be phrased this way, because a load reads the heap; that is why M7 goes back to first principles."
        }
      ]
    },
    {
      "t": "p",
      "h": "That is: “<code>Q</code> holds in the store you would get after the assignment”. No syntax, no capture, no substitution lemma. This is one of the quiet advantages of a shallow embedding."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Deep embedding — assertions are syntax",
        "h": "You define an inductive type <code>Form</code> of assertion syntax, a semantics <code>⟦·⟧ : Form → Assertion</code>, a capture-avoiding <code>Form.subst</code>, and then a <b>substitution lemma</b> saying <code>⟦Q[e/x]⟧ σ h ↔ ⟦Q⟧ (σ[x ↦ e]) h</code>, proved by induction over <code>Form</code> with a side condition about free variables. Then the assignment rule becomes provable. Every new connective you add reopens that induction.",
        "kind": "bad"
      },
      "right": {
        "t": "Shallow embedding — assertions are functions",
        "h": "<code>subst</code> is the substitution lemma, by definition. There is no induction, no capture, no free-variable predicate, and adding a connective costs nothing because connectives are just functions on <code>Prop</code>.",
        "src": "example (x : Var) (e : Atom) (Q : Assertion) (σ : Store) (h : Heap) :\n    subst x e Q σ h = Q (Store.set σ x (e.eval σ)) h := rfl",
        "kind": "good"
      }
    },
    {
      "t": "p",
      "h": "That <code>rfl</code> compiles against the M6 prelude, and it is the entire content of the comparison. The price of the shallow embedding is paid elsewhere: you cannot do induction over the structure of an assertion, so you cannot state a theorem like “every assertion is equivalent to one in normal form”. Nothing in this workbook wants such a theorem, so the trade is free here. It is not free in general — a paper about decidability of an assertion language needs the deep embedding."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>Hoare P c Q</code>",
          "h": "Total correctness. Unfolds to <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>. You never need <code>unfold Hoare</code>: <code>intro</code> sees through it."
        },
        {
          "k": "<code>PartialHoare P c Q</code>",
          "h": "Partial correctness. Defined here for contrast; used seriously only in M13."
        },
        {
          "k": "<code>subst x e Q</code>",
          "h": "Semantic substitution — <code>Q</code> evaluated in the post-assignment store. The precondition of the assignment axiom."
        },
        {
          "k": "<code>P ⊢ Q</code> (<code>Entails</code>, M3)",
          "h": "<code>∀ σ h, P σ h → Q σ h</code>. Applied to three arguments: <code>hpre σ h hp</code>. Forgetting the first two is the most common error in this chapter."
        },
        {
          "k": "<code>fact φ</code>, <code>emp</code>, <code>aAnd</code> (M3)",
          "h": "<code>fact φ σ h</code> is definitionally <code>φ σ</code>; <code>emp σ h</code> is <code>h = Heap.empty</code>; <code>aAnd P Q σ h</code> is a conjunction. All three are transparent to <code>show</code> and opaque to <code>simp</code> unless you name them."
        },
        {
          "k": "<code>Exec.skip</code>, <code>Exec.assign</code>, <code>Exec.seq</code> (M5)",
          "h": "The three constructors you need here. <code>Exec.assign</code> takes no arguments — the resulting state is determined by the indices — so it appears bare inside an anonymous constructor."
        },
        {
          "k": "<code>Store.set σ x v</code> (M5)",
          "h": "<code>fun y => if y = x then v else σ y</code>. Lean pretty-prints it as <code>σ.set x v</code>, which is the same term. Note the order inside the <code>if</code>: the <i>queried</i> variable is on the left."
        }
      ]
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "Prove a triple by producing a witness: the final state, the derivation that reaches it, and the postcondition at it. Everything in this chapter is <code>intro σ h hp</code>, then a single <code>⟨…⟩</code> with those three things in it. When the third component is itself a conjunction the brackets flatten, and you get <code>⟨state, exec, left, right⟩</code> — four entries for a three-part obligation."
    },
    {
      "t": "sec",
      "s": "Exercises · structural rules"
    },
    {
      "t": "ex",
      "id": "m6-1",
      "name": "hoare_consequence",
      "hard": false,
      "why": "Strengthen the precondition, weaken the postcondition. This is the rule that connects the program logic to Phase 1: every entailment you proved about <code>∗</code> becomes usable here. It is also the only structural rule that changes the <i>shape</i> of a specification without touching the program, which is why it is what you reach for whenever a primitive rule from M7 nearly matches the goal — M9 is largely applications of it, usually in the form <code>hoare_consequence (entails_refl _) step ?_</code>, tidying the postcondition with the <code>∗</code>-algebra of M4.",
      "setup": "In scope: <code>Hoare</code> from this chapter and <code>Entails</code> (written <code>⊢</code>) from M3. No lemma about <code>Exec</code> is needed — the command <code>c</code> is completely opaque here, and that is the point.",
      "goal": "theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare P c Q) (hpost : Q ⊢ Q') : Hoare P' c Q'",
      "hints": [
        "There is nothing to apply and nothing to case on. Start with <code>intro σ h hp</code> and read what the goal turns into — <code>intro</code> unfolds <code>Hoare</code> for you, so you never write <code>unfold</code>.",
        "You now have <code>hp : P' σ h</code> and you need to run <code>hc</code>, which wants <code>P σ h</code>. That is what <code>hpre</code> is for. But <code>hpre : P' ⊢ P</code> is by definition <code>∀ σ h, P' σ h → P σ h</code>, so it takes <b>three</b> arguments: <code>hpre σ h hp</code>.",
        "<code>hc σ h (hpre σ h hp)</code> is an existential. Take it apart with <code>obtain ⟨s', hex, hq⟩ := …</code>; the three names correspond to the witness state, the execution derivation, and the postcondition at that state.",
        "Rebuild the goal with the <i>same</i> witness and the <i>same</i> derivation, changing only the last component: <code>exact ⟨s', hex, hpost s'.store s'.heap hq⟩</code>. Unfold, apply <code>hpre</code> to get into <code>P</code>, run <code>hc</code>, apply <code>hpost</code> to the result."
      ],
      "sol": "theorem hoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : Hoare (P) (c) (Q)) (hpost : Q ⊢ Q') : Hoare (P') (c) (Q') := by\n  intro σ h hp\n  obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)\n  exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
      "expl": "Pure plumbing, but note the variance: <code>P'</code> must be <i>stronger</i> than <code>P</code> and <code>Q'</code> <i>weaker</i> than <code>Q</code>. Hoare triples are contravariant in the precondition and covariant in the postcondition — the same variance as a function type, for the same reason. The proof never inspects <code>c</code>, which is why the rule holds for every command including the ones we have not written yet.",
      "walk": [
        {
          "tac": "intro σ h hp",
          "h": "The goal displayed as <code>Hoare P' c Q'</code>, which is not visibly a <code>∀</code>. <code>intro</code> nevertheless succeeds: it unfolds definitions on demand until it finds a binder. Three binders come off at once — the store, the heap, and the precondition hypothesis — and the goal becomes the raw existential."
        },
        {
          "tac": "obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)",
          "h": "Two things happen in one line. <code>hpre σ h hp : P σ h</code> converts the precondition; <code>hc σ h …</code> then runs the triple you were given, producing <code>∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>. <code>obtain</code> destructs the pair-of-pair in one pattern: <code>s'</code> is the witness, <code>hex</code> the left conjunct, <code>hq</code> the right."
        },
        {
          "tac": "exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
          "h": "The goal wants the same shape with <code>Q'</code> instead of <code>Q</code>. Supply the same witness and the same derivation — nothing about the run changed — and post-compose the last component with <code>hpost</code>, again applied to store, heap and proof."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_consequence, tactic by tactic",
          "start": "P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\n⊢ Hoare P' c Q'",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\nσ : Store\nh : Heap\nhp : P' σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q' s'.store s'.heap",
              "h": "This is the moment worth pausing on: the goal you were shown as <code>Hoare P' c Q'</code> is <i>this</i>. Note <code>{ store := σ, heap := h }</code> — Lean prints the anonymous constructor <code>⟨σ, h⟩</code> from the definition in structure-instance form. Same term, different rendering."
            },
            {
              "tac": "obtain ⟨s', hex, hq⟩ := hc σ h (hpre σ h hp)",
              "state": "P P' Q Q' : Assertion\nc : Cmd\nhpre : P' ⊢ P\nhc : Hoare P c Q\nhpost : Q ⊢ Q'\nσ : Store\nh : Heap\nhp : P' σ h\ns' : State\nhex : Exec c { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ Q' s'.store s'.heap",
              "h": "The goal is unchanged; the context grew by exactly the three pieces you need. Compare <code>hex</code> against the left conjunct of the goal — identical. Compare <code>hq</code> against the right conjunct — <code>Q</code> where the goal wants <code>Q'</code>. That single mismatch is the whole remaining obligation."
            },
            {
              "tac": "exact ⟨s', hex, hpost s'.store s'.heap hq⟩",
              "state": "No goals.",
              "h": "The anonymous constructor builds <code>Exists.intro s' (And.intro hex …)</code>; it flattens automatically, which is why three entries suffice for a nested pair."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "Why the variance is what it is",
          "items": [
            {
              "k": "A triple is a function type in disguise",
              "h": "Unfolded, <code>Hoare P c Q</code> is <code>∀ σ h, P σ h → (something about Q)</code>. <code>P</code> occurs to the left of an arrow, <code>Q</code> to the right."
            },
            {
              "k": "Left of an arrow is contravariant",
              "h": "To weaken <code>A → B</code> you may strengthen <code>A</code>. Hence a <i>stronger</i> precondition gives a weaker — that is, more widely applicable — obligation, so <code>P' ⊢ P</code> is the direction that lets you conclude."
            },
            {
              "k": "Right of an arrow is covariant",
              "h": "To weaken <code>A → B</code> you may weaken <code>B</code>. Hence <code>Q ⊢ Q'</code>: you may promise less than you proved."
            },
            {
              "k": "The mnemonic",
              "h": "You may always demand more of the caller and promise less to them. Every step in that direction is sound; the reverse direction is exactly the collection of false statements below."
            }
          ]
        },
        {
          "t": "detail",
          "title": "What the reversed rule would let you prove",
          "tag": "counterexample",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Suppose the rule read <code>(hpre : P ⊢ P') → Hoare P c Q → Hoare P' c Q</code> — precondition weakened rather than strengthened. Instantiate <code>P := emp</code>, <code>P' := aTrue</code>, <code>c := .skip</code>, <code>Q := emp</code>. The hypothesis <code>emp ⊢ aTrue</code> is trivial and <code>Hoare emp .skip emp</code> is <code>hoare_skip</code>, so the reversed rule would deliver <code>Hoare aTrue .skip emp</code>: “from any state, <code>skip</code> leaves you owning nothing”. That is false, and here is the heap that witnesses it."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem not_hoare_true_skip_emp : ¬ Hoare aTrue Cmd.skip emp := by\n  intro hc\n  obtain ⟨s', hex, he⟩ := hc (fun _ => 0) (Heap.singleton 0 0) trivial\n  cases hex\n  have he' : Heap.singleton 0 0 = Heap.empty := he\n  have h0 : Heap.singleton 0 0 0 = Heap.empty 0 := by rw [he']\n  rw [singleton_same] at h0\n  exact absurd h0 (by simp [Heap.empty])",
              "cap": "Compiles against the M6 prelude. The <code>have he' : … := he</code> line is not a no-op: <code>he</code> has the type <code>emp { store := …, heap := Heap.singleton 0 0 }.store { … }.heap</code>, and restating it at the definitionally equal type <code>Heap.singleton 0 0 = Heap.empty</code> is what makes <code>rw</code> able to find the pattern. Delete the line and <code>rw [he]</code> reports <code>Did not find an occurrence of the pattern { store := fun x => 0, heap := Heap.singleton 0 0 }.heap</code>. That is the standing rule: <code>exact</code> and <code>have</code> work up to definitional equality, <code>rw</code> and <code>simp</code> match syntax."
            },
            {
              "t": "p",
              "h": "The same counterexample refutes the reversed postcondition rule: take <code>P := aTrue</code>, <code>Q := aTrue</code>, <code>Q' := emp</code>, and note <code>emp ⊢ aTrue</code>."
            }
          ]
        }
      ],
      "pitfall": "Applying an entailment to one argument. <code>hpre</code> looks like an implication, so you write <code>hpre hp</code> — and Lean tells you it wanted a <code>Store</code>: <br><code>Application type mismatch: The argument hp has type P' σ h of sort `Prop` but is expected to have type Store of sort `Type` in the application hpre hp</code>. <br>The fix is <code>hpre σ h hp</code>. The same mistake recurs with <code>hpost hq</code>, where the fix is <code>hpost s'.store s'.heap hq</code> — and note that here the two arguments are <i>projections</i> of the witness state, not the original <code>σ</code> and <code>h</code>, because the postcondition is evaluated after the run.",
      "variants": "Drop <code>hpre</code> entirely and the statement becomes false as soon as <code>P'</code> is satisfiable outside <code>P</code>: <code>Hoare emp .skip emp</code> would give <code>Hoare aTrue .skip emp</code>, refuted above. Drop <code>hpost</code> and you cannot even state the conclusion. Reverse either entailment and you get the same counterexample. Drop both and try to prove <code>Hoare P' c Q'</code> from <code>Hoare P c Q</code> alone: the proof stalls at the second tactic, because <code>hc</code> wants <code>P σ h</code> and all you have is <code>hp : P' σ h</code>. The point where each hypothesis is consumed is visible in the trace: <code>hpre</code> at line 2, <code>hpost</code> at line 3, and <code>hc</code> is what supplies the witness neither of them could."
    },
    {
      "t": "ex",
      "id": "m6-2",
      "name": "hoare_skip / hoare_seq",
      "hard": false,
      "why": "The two rules that turn a list of triples into a proof of a program. <code>hoare_skip</code> is the base case you will barely notice; <code>hoare_seq</code> is the rule you will use in every remaining chapter, and it is the first place where <i>you</i> have to invent something — the intermediate assertion is not determined by the statement.",
      "setup": "In scope: <code>Hoare</code>, and from M5 the constructors <code>Exec.skip</code> and <code>Exec.seq</code>. Recall <code>Exec.seq</code> has type <code>Exec c₁ s s' → Exec c₂ s' s'' → Exec (c₁ ;; c₂) s s''</code>: it glues two derivations that agree at the middle state.",
      "goal": "theorem hoare_skip (P : Assertion) : Hoare P .skip P\n\ntheorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare P c₁ Q) (h₂ : Hoare Q c₂ R) : Hoare P (c₁ ;; c₂) R",
      "hints": [
        "For <code>hoare_skip</code>, ask what the witness state has to be. <code>skip</code> changes nothing, so the final state is the initial one: <code>⟨σ, h⟩</code>. Everything else follows.",
        "<code>hoare_skip</code> needs no tactics at all. A proof of <code>∀ σ h, P σ h → …</code> is a function <code>fun σ h hp => …</code>, and the body is a single anonymous constructor with three entries.",
        "For <code>hoare_seq</code>, run <code>h₁</code> on the initial store and heap to get an intermediate state <code>s₁</code>. Then run <code>h₂</code> — but <code>h₂</code> wants a store and a heap, not a state, so feed it <code>s₁.store s₁.heap</code>.",
        "<code>hoare_skip</code> is a one-line term. For <code>hoare_seq</code>, run <code>h₁</code>, feed its final state to <code>h₂</code>, and glue the derivations with <code>Exec.seq</code>."
      ],
      "sol": "theorem hoare_skip (P : Assertion) : Hoare (P) (.skip) (P) :=\n  fun σ h hp => ⟨⟨σ, h⟩, Exec.skip, hp⟩\n\ntheorem hoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : Hoare (P) (c₁) (Q)) (h₂ : Hoare (Q) (c₂) (R)) : Hoare (P) ((c₁ ;; c₂)) (R) := by\n  intro σ h hp\n  obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp\n  obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq\n  exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩",
      "expl": "<code>hoare_seq</code> is where the intermediate assertion <code>Q</code> appears, and in Lean you usually have to supply it explicitly: <code>hoare_seq (Q := …) h₁ h₂</code>. Choosing that intermediate assertion <i>is</i> the act of verifying a program; everything else is mechanical.",
      "walk": [
        {
          "tac": "fun σ h hp =>",
          "h": "<code>hoare_skip</code> is proved as a term, not with <code>by</code>. A proof of a <code>∀</code>-statement is a function, so the three binders of the unfolded <code>Hoare</code> become three lambda arguments. Lean accepts this because it checks the body against the unfolded type; no <code>unfold</code> or <code>show</code> is needed."
        },
        {
          "tac": "⟨⟨σ, h⟩, Exec.skip, hp⟩",
          "h": "Three entries for the existential-of-conjunction. The inner <code>⟨σ, h⟩</code> is the <code>State</code>; the flattening of the outer brackets is what lets <code>Exec.skip</code> and <code>hp</code> sit at the same level. <code>Exec.skip</code> takes no explicit argument: its type <code>Exec .skip s s</code> forces the two states to coincide, and unification picks <code>s := ⟨σ, h⟩</code>. And <code>hp : P σ h</code> is accepted as a proof of <code>P ⟨σ, h⟩.store ⟨σ, h⟩.heap</code> because those projections reduce."
        },
        {
          "tac": "intro σ h hp",
          "h": "<code>hoare_seq</code> starts the same way: peel the three binders, exposing the existential over the final state of the whole sequence."
        },
        {
          "tac": "obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp",
          "h": "Run the first triple. <code>s₁</code> is the state after <code>c₁</code>, <code>hex₁ : Exec c₁ ⟨σ, h⟩ s₁</code>, and <code>hq : Q s₁.store s₁.heap</code> — the intermediate assertion holds exactly where you would expect."
        },
        {
          "tac": "obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq",
          "h": "Run the second triple <i>from</i> <code>s₁</code>. Because <code>Hoare</code> quantifies over a store and a heap separately, you must project; the derivation you get back is therefore stated at <code>{ store := s₁.store, heap := s₁.heap }</code> rather than at <code>s₁</code>."
        },
        {
          "tac": "exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩",
          "h": "<code>Exec.seq</code> wants <code>Exec c₂ s₁ s₂</code> and you are handing it <code>Exec c₂ { store := s₁.store, heap := s₁.heap } s₂</code>. Structure eta makes those the same type, so <code>exact</code> — which checks up to definitional equality — accepts it without a rewrite."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_seq, tactic by tactic",
          "start": "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\n⊢ Hoare P (c₁ ;; c₂) R",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
              "h": "One existential, for the final state of the <i>whole</i> sequence. The intermediate state is nowhere in the goal — it exists only in the derivation you are about to build."
            },
            {
              "tac": "obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp",
              "state": "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\nσ : Store\nh : Heap\nhp : P σ h\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\nhq : Q s₁.store s₁.heap\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
              "h": "<code>s₁</code> is now a genuine object in the context. This is the only place the intermediate assertion is used, and it is used exactly once — as the input to <code>h₂</code>."
            },
            {
              "tac": "obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq",
              "state": "P Q R : Assertion\nc₁ c₂ : Cmd\nh₁ : Hoare P c₁ Q\nh₂ : Hoare Q c₂ R\nσ : Store\nh : Heap\nhp : P σ h\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\nhq : Q s₁.store s₁.heap\ns₂ : State\nhex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂\nhr : R s₂.store s₂.heap\n⊢ ∃ s', Exec (c₁ ;; c₂) { store := σ, heap := h } s' ∧ R s'.store s'.heap",
              "h": "Look hard at <code>hex₂</code>. Its source state is <code>{ store := s₁.store, heap := s₁.heap }</code>, not <code>s₁</code> — the round trip through the projections left a visible scar. <code>Exec.seq</code> will nevertheless accept it against <code>hex₁</code>, whose target is <code>s₁</code> on the nose."
            },
            {
              "tac": "exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩",
              "state": "No goals.",
              "h": "Witness <code>s₂</code>, derivation <code>Exec.seq hex₁ hex₂</code>, postcondition <code>hr</code>. The two derivations are glued at <code>s₁</code>, which is where the eta reduction silently happens."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Named arguments: what <code>(Q := …)</code> means",
          "tag": "syntax",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "<code>Q</code> in <code>hoare_seq</code> is an <i>implicit</i> argument, written <code>{P Q R : Assertion}</code>. Implicit arguments are normally solved by unification against the goal — but the goal is <code>Hoare P (c₁ ;; c₂) R</code>, in which <code>Q</code> does not occur at all. Unification has nothing to work with, so you must say what it is."
            },
            {
              "t": "p",
              "h": "The syntax for that is a named argument: <code>hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_</code>. It sets one implicit by name and leaves the rest to unification. Omit it and Lean tells you exactly what is missing:"
            },
            {
              "t": "state",
              "src": "error: don't know how to synthesize implicit argument `Q`\n  @hoare_seq emp ?m.12 (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp) (Cmd.assign x (Atom.const 3))\n    (Cmd.assign y (Atom.var x)) ?m.16 ?m.17\ncontext:\nx y : Var\n⊢ Assertion",
              "cap": "What <code>refine hoare_seq ?_ ?_</code> produces on the M6-5 goal. The <code>?m.12</code> sitting in the second position is the unsolved <code>Q</code>, and the reported context <code>⊢ Assertion</code> is Lean asking you for it."
            },
            {
              "t": "p",
              "h": "There is a second way — <code>apply hoare_seq</code> and let the metavariable stay open, filling it in later by whatever the subgoals force. Avoid it here. The intermediate assertion is a design decision, and postponing a design decision until unification guesses it is how you end up with a proof you cannot read."
            }
          ]
        },
        {
          "t": "detail",
          "title": "The same rule for partial correctness",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Worth writing once, because the direction of every arrow flips and the proof gets shorter rather than longer."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem partial_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) : PartialHoare P (c₁ ;; c₂) R := by\n  intro σ h s' hp hex\n  cases hex with\n  | seq hex₁ hex₂ => exact h₂ _ _ _ (h₁ σ h _ hp hex₁) hex₂",
              "cap": "Compiles against the M6 prelude. You are <i>given</i> a derivation of the sequence, so <code>cases</code> takes it apart — and the intermediate state comes out of the derivation rather than out of a triple you had to run. That is why no witness has to be produced."
            },
            {
              "t": "p",
              "h": "The trade is visible: the total version had to build <code>Exec.seq hex₁ hex₂</code>, and building it is exactly the work of proving termination. The partial version never builds anything."
            }
          ]
        }
      ],
      "pitfall": "Feeding <code>h₂</code> a state instead of a store and a heap. Writing <code>h₂ s₁ hq</code> looks natural — <code>s₁</code> is the state you just produced — and Lean answers <br><code>Application type mismatch: The argument s₁ has type State but is expected to have type Store in the application h₂ s₁</code>. <br>The fix is <code>h₂ s₁.store s₁.heap hq</code>. This is the one place where the decision to have <code>Hoare</code> quantify over <code>σ</code> and <code>h</code> separately actually costs you something, and the cost is one projection per sequencing step.",
      "variants": "<code>hoare_skip</code> looks too weak to be worth stating — why the same <code>P</code> on both sides? Because that one instance generates all the others: <code>Hoare P .skip Q</code> holds <b>if and only if</b> <code>P ⊢ Q</code>, the backward direction being <code>hoare_consequence (entails_refl P) (hoare_skip P) he</code> and the forward direction being <code>cases</code> on the derivation, which forces the final state to be the initial one. So <code>hoare_skip</code> at <code>P</code> is the strongest true triple for <code>skip</code>, and everything else is consequence. <br><br><code>hoare_seq</code> is the interesting one. It does <b>not</b> require the two commands to touch disjoint memory, nor <code>Q</code> to be anything in particular — any assertion both halves agree on works. Both extremes are legal and useless, but not symmetrically so. Take <code>Q := aFalse</code>: the second premise <code>Hoare aFalse c₂ R</code> is vacuously true and the first is unprovable unless <code>P</code> is itself unsatisfiable. Take <code>Q := aTrue</code>: the second premise <code>Hoare aTrue c₂ R</code> is normally unprovable, and the first, <code>Hoare P c₁ aTrue</code>, is <i>not</i> trivial — it still asserts that <code>c₁</code> terminates without faulting from every <code>P</code>-state, which is exactly what <code>¬ Hoare emp (.load x l) aTrue</code> and <code>¬ Hoare emp forever aTrue</code> above deny. It is the informative part of <code>Q</code> that is gone, not the work. The skill is picking the <code>Q</code> in between. <br><br>If you replace <code>Hoare</code> by <code>PartialHoare</code> throughout, the same rule holds and the proof gets <i>shorter</i>, because you receive the composite derivation and take it apart with <code>cases</code> instead of building it."
    },
    {
      "t": "ex",
      "id": "m6-3",
      "name": "hoare_assign",
      "hard": false,
      "why": "The assignment axiom, and with the semantic <code>subst</code> it is almost a tautology — which is the point. It is also your template for backwards reasoning: given a postcondition, <code>subst</code> computes the precondition, and M12 turns that observation into a weakest-precondition calculus.",
      "setup": "In scope: <code>subst</code> from this chapter, <code>Store.set</code> and <code>Exec.assign</code> from M5. Recall <code>Exec.assign</code> is indexed so that the final state is forced to be <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code> — you do not get to choose it.",
      "goal": "theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (subst x e Q) (.assign x e) Q",
      "hints": [
        "Write down the witness first. What state does <code>x := e</code> produce from <code>⟨σ, h⟩</code>? The heap is untouched and the store gets one entry updated.",
        "Having introduced <code>hq : subst x e Q σ h</code>, unfold that in your head: it is <code>Q (Store.set σ x (e.eval σ)) h</code> — literally the postcondition at the state you just wrote down. No conversion is needed; <code>hq</code> already has the right type.",
        "The final state is <code>⟨Store.set σ x (e.eval σ), h⟩</code>, and <code>subst x e Q σ h</code> is <i>by definition</i> <code>Q</code> at that state."
      ],
      "sol": "theorem hoare_assign (x : Var) (e : Atom) (Q : Assertion) :\n    Hoare (subst x e Q) ((.assign x e)) (Q) := by\n  intro σ h hq\n  exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
      "expl": "Three lines, and two of them are boilerplate. Compare this with the pain of a deep embedding, where you would need a substitution function on assertion syntax plus a lemma relating it to the semantics. Here the precondition and the postcondition-at-the-final-state are the <i>same term</i>, so <code>hq</code> is handed straight back.",
      "walk": [
        {
          "tac": "intro σ h hq",
          "h": "The usual three binders. <code>hq : subst x e Q σ h</code> — note that Lean displays it folded, as <code>subst x e Q σ h</code>, not as the store-update it unfolds to. That folded display is fine here precisely because you never need to look inside."
        },
        {
          "tac": "exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
          "h": "Witness, derivation, postcondition. Strictly speaking the witness is redundant here — <code>exact ⟨_, Exec.assign, hq⟩</code> also compiles, because <code>Exec.assign</code>'s indices determine the final state and unification reads it off. Write it out anyway: it is the state the theorem is <i>about</i>, and from M7 on the derivation will not always pin it down. And <code>hq</code> closes the third component because <code>subst x e Q σ h</code> and <code>Q ⟨Store.set σ x (e.eval σ), h⟩.store ⟨…⟩.heap</code> are definitionally identical — unfold <code>subst</code> (delta), apply the resulting lambda to <code>σ</code> and <code>h</code> (beta), and reduce the two projections of an explicit constructor (iota). Three reduction rules, no tactic."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_assign, tactic by tactic",
          "start": "x : Var\ne : Atom\nQ : Assertion\n⊢ Hoare (subst x e Q) (Cmd.assign x e) Q",
          "steps": [
            {
              "tac": "intro σ h hq",
              "state": "x : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\nhq : subst x e Q σ h\n⊢ ∃ s', Exec (Cmd.assign x e) { store := σ, heap := h } s' ∧ Q s'.store s'.heap",
              "h": "Everything you need is now on screen. The existential asks for a state; <code>Exec.assign</code> determines which one; <code>hq</code> is already the postcondition there. There is nothing left to prove, only to write down."
            },
            {
              "tac": "exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
              "state": "No goals.",
              "h": "If you write a witness that is not the state the assignment produces, this is where Lean complains — <code>Exec.assign</code> fails to unify, not <code>hq</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "The rule in anger: backwards reasoning on <code>assign_constant</code>",
          "tag": "worked example",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Exercise M6-4 below proves <code>assign_constant</code> from scratch, by producing the run. Here is the same theorem proved the way you will do it from M9 onwards: apply the axiom, and let <code>hoare_consequence</code> leave you a pure entailment — a <i>verification condition</i> — with no program in it."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem assign_constant' (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  refine hoare_consequence ?_ (hoare_assign x (.const 10) _) (entails_refl _)\n  intro σ h he\n  show Store.set σ x 10 x = 10 ∧ h = Heap.empty\n  exact ⟨by simp [Store.set], he⟩",
              "cap": "Compiles against the M6 prelude. <code>entails_refl</code> is from M3."
            },
            {
              "t": "trace",
              "title": "What the verification condition looks like",
              "start": "x : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 10)) (aAnd (fact fun σ => σ x = 10) emp)",
              "steps": [
                {
                  "tac": "refine hoare_consequence ?_ (hoare_assign x (.const 10) _) (entails_refl _)",
                  "state": "x : Var\n⊢ emp ⊢ subst x (Atom.const 10) (aAnd (fact fun σ => σ x = 10) emp)",
                  "h": "Two turnstiles in one line: the outer <code>⊢</code> is Lean's goal marker, the inner one is <code>Entails</code>. The command has vanished — everything that remains is a statement about assertions, and <code>subst</code> has already computed the precondition for you."
                },
                {
                  "tac": "intro σ h he",
                  "state": "x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ subst x (Atom.const 10) (aAnd (fact fun σ => σ x = 10) emp) σ h",
                  "h": "Still folded. <code>simp</code> cannot make progress on this, and neither can <code>exact</code>, because you cannot see what to supply."
                },
                {
                  "tac": "show Store.set σ x 10 x = 10 ∧ h = Heap.empty",
                  "state": "x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 10 x = 10 ∧ h = Heap.empty",
                  "h": "One <code>show</code> unfolds <code>subst</code>, <code>aAnd</code>, <code>fact</code> and <code>emp</code> at once, because all four are definitional. Lean re-prints <code>Store.set σ x 10</code> as <code>σ.set x 10</code> — generalised field notation, same term."
                },
                {
                  "tac": "exact ⟨by simp [Store.set], he⟩",
                  "state": "No goals.",
                  "h": "The left conjunct is the same one-liner as before; the right is <code>he</code>, unchanged, because assignment does not touch the heap."
                }
              ],
              "done": "No goals."
            },
            {
              "t": "p",
              "h": "That is the shape of every proof from M9 on: structural rules push the program out of the goal, and what is left is mathematics about stores and heaps. M12 automates the pushing."
            }
          ]
        }
      ],
      "pitfall": "<code>subst</code> is a name collision, and it will bite you. In this chapter <code>subst</code> is the definition above; in Lean it is also a core <i>tactic</i>, the one that eliminates an equational hypothesis. So the natural-looking move “open up <code>hq</code>” is spelled <code>unfold subst at hq</code>, and if you type <code>subst hq</code> instead you get: <br><code>Tactic `subst` failed: did not find equation for eliminating 'hq'</code>. <br>The tactic is not confused about your definition; it is looking for an <code>a = b</code> and finding an assertion. (For what it is worth, <code>unfold subst at hq</code> is harmless — the proof still closes, because <code>exact</code> works up to definitional equality either way. It is simply never necessary, and a hypothesis displayed as <code>subst x e Q σ h</code> is easier to match against the theorem statement than one displayed as <code>Q (σ.set x (Atom.eval σ e)) h</code>.)",
      "variants": "Change the witness heap from <code>h</code> to anything else and <code>Exec.assign</code> stops unifying — assignment is defined to preserve the heap, and that is what makes this rule frame-friendly in M8. Now move the precondition. Replace <code>subst x e Q</code> by <code>Q</code> itself — that is, claim <code>Hoare Q (.assign x e) Q</code> — and the theorem is false as soon as <code>Q</code> mentions <code>x</code>: take <code>Q := fact (fun σ => σ x = 0)</code> and <code>e := .const 1</code>, and the postcondition asserts <code>1 = 0</code>. Weaken it further, to <code>aTrue</code>, and the same instance still refutes it, since every state satisfies <code>aTrue</code>. Strengthen it to <code>aFalse</code> and the triple becomes true and worthless. <code>subst x e Q</code> is the unique choice that is neither, and the precise statement of that is: it is strong enough that the triple holds, and every <i>other</i> precondition for which the triple holds entails it. That is what “weakest precondition” means, and M12 states it as <code>wp (.assign x e) Q ⊣⊢ subst x e Q</code>."
    },
    {
      "t": "sec",
      "s": "Exercises · small applications"
    },
    {
      "t": "p",
      "h": "The two exercises below are the first time you prove something about a specific program rather than about the logic. Both are done from first principles — building the <code>Exec</code> derivation by hand — because that is the last time you will have to. From M7 on you compose rules."
    },
    {
      "t": "ex",
      "id": "m6-4",
      "name": "assign_constant",
      "hard": false,
      "why": "Your first concrete specification. It is also the exercise that teaches you the single most useful tactic in this workbook for reading goals: <code>show</code>. The postcondition is an <code>aAnd</code> of a <code>fact</code> and an <code>emp</code>, and until you say <code>show</code> the goal is unreadable.",
      "setup": "In scope: <code>emp</code>, <code>aAnd</code>, <code>fact</code> from M3; <code>Store.set</code> and <code>Exec.assign</code> from M5. Recall <code>fact φ σ h</code> is definitionally <code>φ σ</code>, and <code>Store.set σ x v</code> is <code>fun y => if y = x then v else σ y</code>.",
      "goal": "theorem assign_constant (x : Var) :\n    Hoare emp (.assign x (.const 10))\n      (aAnd (fact (fun σ => σ x = 10)) emp)",
      "hints": [
        "Same opening as <code>hoare_assign</code>: <code>intro σ h he</code>, then name the final state. Nothing touches the heap, so the heap component of the witness is the <code>h</code> you were given, and <code>he</code> proves the <code>emp</code> half of the postcondition unchanged.",
        "Use <code>refine</code> rather than <code>exact</code>, so you can supply everything you know and leave a hole for the part you have not proved. The anonymous constructor flattens, so the postcondition's conjunction contributes two entries: <code>refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩</code>.",
        "The remaining goal displays as <code>fact (fun σ => σ x = 10) { store := σ.set x 10, heap := h }.store …</code>. That is definitionally an equation about numbers. Say so with <code>show</code>.",
        "After <code>refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩</code> the remaining goal displays as <code>fact …</code>. Use <code>show Store.set σ x 10 x = 10</code> to make it readable, then <code>simp [Store.set]</code>."
      ],
      "sol": "theorem assign_constant (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  intro σ h he\n  refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩\n  show Store.set σ x 10 x = 10\n  simp [Store.set]",
      "expl": "The <code>show</code> is the trick worth stealing. <code>fact φ σ h</code> is definitionally <code>φ σ</code>, but <code>simp</code> will not see through <code>fact</code> unless you tell it to — and <code>show</code> is cheaper and clearer than adding <code>fact</code> to the simp set.",
      "walk": [
        {
          "tac": "intro σ h he",
          "h": "Three binders as always. <code>he : emp σ h</code>, which is definitionally <code>h = Heap.empty</code> — you will hand it back untouched, so there is no need to unfold it."
        },
        {
          "tac": "refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩",
          "h": "Four entries for what is nominally a triple: witness, derivation, and then the postcondition <code>aAnd A B</code> flattens into its two conjuncts. The <code>?_</code> is a named hole for the first conjunct, which is the only thing you actually have to prove; <code>he</code> discharges the second on the spot. Note that <code>.const 10</code> evaluates to <code>10</code> definitionally, which is why you may write <code>Store.set σ x 10</code> rather than <code>Store.set σ x ((Atom.const 10).eval σ)</code>."
        },
        {
          "tac": "show Store.set σ x 10 x = 10",
          "h": "The goal was <code>fact (fun σ => σ x = 10) { … }.store { … }.heap</code>. <code>show</code> replaces a goal by any definitionally equal one; here that strips <code>fact</code>, applies the lambda, and reduces the two projections in a single step. Logically nothing happened. Practically, the goal became something you can act on."
        },
        {
          "tac": "simp [Store.set]",
          "h": "Two rewrites, and <code>simp?</code> will name them for you: <code>simp only [Store.set, ↓reduceIte]</code>. The first unfolds the definition, giving <code>(if x = x then 10 else σ x) = 10</code>; the second is <code>simp</code>'s built-in evaluator for <code>ite</code>, which computes the <code>Decidable (x = x)</code> instance to <code>isTrue</code> and takes the branch. This is the same one-liner as <code>update_same</code> in M0, and for the same reason."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "assign_constant, tactic by tactic",
          "start": "x : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 10)) (aAnd (fact fun σ => σ x = 10) emp)",
          "steps": [
            {
              "tac": "intro σ h he",
              "state": "x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign x (Atom.const 10)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 10) emp s'.store s'.heap",
              "h": "The goal wraps over three lines. Read it as: some state, reached by the assignment, at which the conjunction holds."
            },
            {
              "tac": "refine ⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_, he⟩",
              "state": "x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) { store := σ.set x 10, heap := h }.store { store := σ.set x 10, heap := h }.heap",
              "h": "This is what an unreadable goal looks like. The projections were not reduced, <code>fact</code> was not unfolded, and the bound <code>σ</code> inside the lambda shadows the <code>σ</code> in the context. All three problems are cosmetic and all three are fixed by one <code>show</code>."
            },
            {
              "tac": "show Store.set σ x 10 x = 10",
              "state": "x : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 10 x = 10",
              "h": "Now it is an equation between natural numbers. Lean prints <code>σ.set x 10</code>, which is its preferred rendering of <code>Store.set σ x 10</code> — generalised field notation, not a different function."
            },
            {
              "tac": "simp [Store.set]",
              "state": "No goals.",
              "h": ""
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "Without the <code>show</code>",
            "h": "<code>simp [Store.set]</code> normalises the projections but stops at <code>fact</code>, which is not in its simp set. It then reports the goal unsolved <i>and</i> warns that your simp argument was never used — a confusing pair of messages, because the argument was fine and the problem was the wrapper.",
            "src": "error: unsolved goals\nx : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 10) (σ.set x 10) h\n\nwarning: This simp argument is unused:\n  Store.set",
            "kind": "bad"
          },
          "right": {
            "t": "With the <code>show</code>",
            "h": "<code>fact</code> is gone before <code>simp</code> ever runs, so <code>Store.set</code> is the only thing left to unfold and it does get used. You could instead write <code>simp [fact, Store.set]</code> and it works — but then the proof does not record what the goal <i>was</i>, and the next reader has to re-derive it.",
            "src": "show Store.set σ x 10 x = 10\nsimp [Store.set]",
            "kind": "good"
          }
        },
        {
          "t": "detail",
          "title": "Why the brackets take four entries",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The obligation is <code>∃ s', A ∧ (B ∧ C)</code>. Fully explicit, a proof is <code>Exists.intro w (And.intro a (And.intro b c))</code>. The anonymous constructor flattens right-nested applications, so <code>⟨w, a, b, c⟩</code> means exactly that. Here is the same proof written out."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "example (x : Var) :\n    Hoare emp (.assign x (.const 10)) (aAnd (fact (fun σ => σ x = 10)) emp) := by\n  intro σ h he\n  exact Exists.intro ⟨Store.set σ x 10, h⟩\n    (And.intro Exec.assign (And.intro (by show Store.set σ x 10 x = 10; simp [Store.set]) he))",
              "cap": "Compiles against the M6 prelude. Nobody writes proofs this way; write it once so that the flattening stops being magic."
            },
            {
              "t": "p",
              "h": "The flattening is by <i>position</i>, not by type, so if you get the order of the two conjuncts wrong Lean reports the mismatch against whichever component it reached. Swapping the last two entries gives <code>Application type mismatch: The argument he has type emp σ h but is expected to have type fact (fun σ => σ x = 10) …</code> — the error names <code>And.intro</code>, not the outer existential, which tells you exactly how deep the problem is."
            }
          ]
        }
      ],
      "pitfall": "Reaching for <code>simp [Store.set]</code> without the <code>show</code>, and then believing the warning. Lean says <code>This simp argument is unused: Store.set</code>, which reads like an invitation to delete it — but <code>Store.set</code> is not the problem, <code>fact</code> is. The goal <code>fact (fun σ => σ x = 10) (σ.set x 10) h</code> is an application of a constant <code>simp</code> has never been told to unfold, so it never reaches the store update underneath. Either add <code>fact</code> to the simp set or, better, put the <code>show</code> in.",
      "variants": "Weaken the postcondition to <code>fact (fun σ => σ x = 10)</code> alone and the <code>refine</code> loses one entry — it becomes <code>⟨⟨Store.set σ x 10, h⟩, Exec.assign, ?_⟩</code>, and <code>he</code> is never used. The proof is no shorter in lines and one degree less useful: you have dropped the record that the heap is still empty, so the triple can no longer be sequenced with anything that needs <code>emp</code>. <br><br>Rewrite the postcondition as <code>pure (fun σ => σ x = 10)</code> and <i>nothing</i> changes — not the proof, not even the goal up to unfolding — because M3 <i>defines</i> <code>pure φ := aAnd (fact φ) emp</code>. That is a renaming, not a strengthening. <br><br>Replace <code>emp</code> in the precondition by <code>aTrue</code> and the theorem becomes <b>false</b>. Trace where: <code>he</code> in the <code>refine</code> is the only thing that ever proves the <code>emp</code> in the postcondition, and it exists only because the precondition supplied it. With <code>aTrue</code> you get <code>trivial</code> instead, which proves nothing about the heap — and a starting heap of <code>Heap.singleton 0 0</code> refutes the triple outright, by the same argument as <code>not_hoare_true_skip_emp</code> in M6-1. Assignment does not clear memory."
    },
    {
      "t": "ex",
      "id": "m6-5",
      "name": "assign_twice",
      "hard": false,
      "why": "Your first two-command proof. The interesting part is what you <i>do not</i> need. It is also the exercise where you choose an intermediate assertion for the first time, which is the skill the rest of the workbook is built on.",
      "setup": "In scope: <code>hoare_seq</code> from M6-2, plus everything used in M6-4. The program is <code>x := 3 ;; y := x</code>. Note <code>x</code> and <code>y</code> are arbitrary variables — nothing says they are distinct.",
      "goal": "theorem assign_twice (x y : Var) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp)",
      "hints": [
        "Do not start with <code>intro</code>. The command is a sequence, so the first move is <code>hoare_seq</code>, and that decides the shape of everything after it.",
        "<code>hoare_seq</code> cannot guess the intermediate assertion — it does not appear in the goal. Supply it by name: <code>refine hoare_seq (Q := …) ?_ ?_</code>. What is true after <code>x := 3</code> and enough to finish?",
        "The intermediate assertion should say what you learned and keep what you still own: <code>x</code> is <code>3</code>, and the heap is still empty. Each of the two subgoals is then a single-assignment proof in the style of M6-4.",
        "In the second subgoal you will have to prove a conjunction. <code>show</code> it into a readable form first, then <code>constructor</code>, then <code>show</code> each side into the explicit <code>if</code> it unfolds to. Look at the first one carefully before you simplify it.",
        "Use <code>hoare_seq</code> with intermediate assertion <code>aAnd (fact (fun σ => σ x = 3)) emp</code>."
      ],
      "sol": "theorem assign_twice (x y : Var) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.var x))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp) := by\n  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_\n  · intro σ h he\n    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 3 x = 3\n    simp [Store.set]\n  · intro σ h hpre\n    obtain ⟨hx, he⟩ := hpre\n    have hx' : σ x = 3 := hx\n    refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3\n    constructor\n    · show (if x = y then σ x else σ x) = 3\n      simp [hx']\n    · show (if y = y then σ x else σ y) = 3\n      simp [hx']",
      "expl": "Look at the hypothesis list: there is <b>no</b> <code>x ≠ y</code>. You will be tempted to add it, and Lean will tell you it is unused. The reason is that <code>y := x</code> copies the value of <code>x</code>, so even in the degenerate case <code>x = y</code> the store still maps both to <code>3</code>. In the proof this shows up as the goal <code>(if x = y then σ x else σ x) = 3</code>, where both branches coincide. A small but instructive example of the formalisation catching a side condition you assumed you needed.",
      "walk": [
        {
          "tac": "refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_",
          "h": "The whole design decision of the proof, in one line. <code>(Q := …)</code> fixes the implicit intermediate assertion, which unification could never find because <code>Q</code> does not occur in the conclusion of <code>hoare_seq</code>. The two <code>?_</code> become goals <code>refine_1</code> and <code>refine_2</code>."
        },
        {
          "tac": "· intro σ h he",
          "h": "First bullet, first subgoal: <code>Hoare emp (x := 3) (aAnd (fact (fun σ => σ x = 3)) emp)</code>. This is <code>assign_constant</code> with <code>3</code> for <code>10</code>, so the proof is the same four lines."
        },
        {
          "tac": "refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩",
          "h": "Witness, derivation, hole for the fact, and <code>he</code> for the <code>emp</code>. The heap is untouched by an assignment, so the <code>emp</code> that came in goes straight back out."
        },
        {
          "tac": "show Store.set σ x 3 x = 3",
          "h": "Strips <code>fact</code> and the two state projections."
        },
        {
          "tac": "simp [Store.set]",
          "h": "Closes <code>if x = x then 3 else σ x = 3</code>. First subgoal done."
        },
        {
          "tac": "· intro σ h hpre",
          "h": "Second bullet: <code>Hoare (aAnd (fact (fun σ => σ x = 3)) emp) (y := x) (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp)</code>. Now the precondition is informative, so <code>hpre</code> is something you take apart rather than pass on."
        },
        {
          "tac": "obtain ⟨hx, he⟩ := hpre",
          "h": "<code>aAnd</code> is definitionally a conjunction, so <code>obtain</code> splits it without any unfolding: <code>hx : fact (fun σ => σ x = 3) σ h</code> and <code>he : emp σ h</code>."
        },
        {
          "tac": "have hx' : σ x = 3 := hx",
          "h": "The <code>show</code> trick applied to a hypothesis instead of a goal. <code>hx</code> is already a proof of <code>σ x = 3</code> definitionally, but it is <i>displayed</i> as <code>fact (fun σ => σ x = 3) σ h</code>, and <code>simp [hx]</code> would refuse to use it as a rewrite rule in that form. Restating it at the transparent type gives <code>simp</code> something it can fire on."
        },
        {
          "tac": "refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩",
          "h": "The witness store is <code>Store.set σ y (σ x)</code> because <code>(Atom.var x).eval σ</code> reduces to <code>σ x</code>. Note it is <code>σ x</code>, not <code>3</code> — the semantics copies whatever is there, and connecting it to <code>3</code> is your job."
        },
        {
          "tac": "show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3",
          "h": "Strips <code>fact</code> and the projections, exposing the conjunction underneath. Both conjuncts are now statements about the post-assignment store."
        },
        {
          "tac": "constructor",
          "h": "Splits <code>A ∧ B</code> into two goals, named <code>left</code> and <code>right</code>. (<code>constructor</code> applies the unique constructor of the goal's inductive type, which for <code>And</code> is <code>And.intro</code>.)"
        },
        {
          "tac": "· show (if x = y then σ x else σ x) = 3",
          "h": "The interesting line of the whole exercise. Unfolding <code>Store.set σ y (σ x)</code> at the point <code>x</code> gives <code>if x = y then σ x else σ x</code> — and <b>both branches are the same</b>. That is the formal content of \"you do not need <code>x ≠ y</code>\": in the aliased case <code>y</code> was just overwritten with what <code>x</code> held, which is what <code>x</code> holds."
        },
        {
          "tac": "simp [hx']",
          "h": "<code>simp?</code> reports <code>simp only [hx', ite_self]</code>. <code>ite_self</code> is the library lemma <code>(if c then a else a) = a</code> — it holds for <i>any</i> decidable <code>c</code>, which is precisely why the guard never has to be decided. Then <code>hx'</code> turns <code>σ x</code> into <code>3</code>."
        },
        {
          "tac": "· show (if y = y then σ x else σ y) = 3",
          "h": "The second conjunct. Here the guard is <code>y = y</code>, true by reflexivity, so the branch taken is <code>σ x</code> regardless."
        },
        {
          "tac": "simp [hx']",
          "h": "Same finish, different first step: here <code>simp?</code> reports <code>simp only [↓reduceIte, hx']</code> — the guard <code>y = y</code> <i>is</i> decided, by evaluating its <code>Decidable</code> instance, and only then does <code>hx'</code> fire. Compare with the previous branch, where <code>ite_self</code> meant no decision was ever made."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "assign_twice, the states that matter",
          "start": "x y : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 3) ;; Cmd.assign y (Atom.var x)) (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp)",
          "steps": [
            {
              "tac": "refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_",
              "state": "case refine_1\nx y : Var\n⊢ Hoare emp (Cmd.assign x (Atom.const 3)) (aAnd (fact fun σ => σ x = 3) emp)\n\ncase refine_2\nx y : Var\n⊢ Hoare (aAnd (fact fun σ => σ x = 3) emp) (Cmd.assign y (Atom.var x)) (aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp)",
              "h": "Two goals, and the assertion you chose appears as the postcondition of the first and the precondition of the second. That is the entire mechanism of sequencing: your <code>Q</code> is the handshake."
            },
            {
              "tac": "· intro σ h he",
              "state": "case refine_1\nx y : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign x (Atom.const 3)) { store := σ, heap := h } s' ∧ aAnd (fact fun σ => σ x = 3) emp s'.store s'.heap",
              "h": "Identical in shape to M6-4."
            },
            {
              "tac": "refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩",
              "state": "case refine_1\nx y : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ fact (fun σ => σ x = 3) { store := σ.set x 3, heap := h }.store { store := σ.set x 3, heap := h }.heap",
              "h": "The same unreadable <code>fact</code> goal, for the same reason."
            },
            {
              "tac": "show Store.set σ x 3 x = 3",
              "state": "case refine_1\nx y : Var\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ σ.set x 3 x = 3",
              "h": "Closed by <code>simp [Store.set]</code>. Now the second bullet."
            },
            {
              "tac": "· intro σ h hpre",
              "state": "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhpre : aAnd (fact fun σ => σ x = 3) emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
              "h": "Note <code>σ</code> and <code>h</code> here are <i>fresh</i> — they are the state at the start of the second command, unrelated to the ones in the first bullet. That is exactly what <code>hoare_seq</code> bought: the two halves never have to mention each other's states."
            },
            {
              "tac": "obtain ⟨hx, he⟩ := hpre",
              "state": "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
              "h": "<code>hx</code> is displayed folded. It is already a proof of <code>σ x = 3</code>; the <code>have hx'</code> on the next line is purely so that the display matches."
            },
            {
              "tac": "have hx' : σ x = 3 := hx",
              "state": "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ ∃ s',\n    Exec (Cmd.assign y (Atom.var x)) { store := σ, heap := h } s' ∧\n      aAnd (fact fun σ => σ x = 3 ∧ σ y = 3) emp s'.store s'.heap",
              "h": "The goal did not move. The context gained <code>hx'</code>, whose <i>proof term</i> is literally <code>hx</code> — nothing was computed, only re-typed at a transparent type. That is the whole purpose of the line, and it is the hypothesis-side twin of <code>show</code>."
            },
            {
              "tac": "refine ⟨⟨Store.set σ y (σ x), h⟩, Exec.assign, ?_, he⟩",
              "state": "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ fact (fun σ => σ x = 3 ∧ σ y = 3) { store := σ.set y (σ x), heap := h }.store\n    { store := σ.set y (σ x), heap := h }.heap",
              "h": "The witness store copies <code>σ x</code> into <code>y</code>. Nothing in the goal yet knows that <code>σ x</code> is <code>3</code>."
            },
            {
              "tac": "show Store.set σ y (σ x) x = 3 ∧ Store.set σ y (σ x) y = 3",
              "state": "case refine_2\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ σ.set y (σ x) x = 3 ∧ σ.set y (σ x) y = 3",
              "h": "Readable at last."
            },
            {
              "tac": "constructor",
              "state": "case refine_2.left\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ σ.set y (σ x) x = 3\n\ncase refine_2.right\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ σ.set y (σ x) y = 3",
              "h": "Two goals, named <code>left</code> and <code>right</code> under the <code>refine_2</code> they came from. Each is an equation about the same updated store, read at a different variable."
            },
            {
              "tac": "· show (if x = y then σ x else σ x) = 3",
              "state": "case refine_2.left\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ (if x = y then σ x else σ x) = 3",
              "h": "This is the goal worth photographing. The <code>if</code> is there because <code>Store.set</code> is defined with one, and both branches are <code>σ x</code> because the value being written is <code>σ x</code>. No case analysis is needed — and no disequality hypothesis could help, because there is nothing to distinguish."
            },
            {
              "tac": "· show (if y = y then σ x else σ y) = 3",
              "state": "case refine_2.right\nx y : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 3) σ h\nhe : emp σ h\nhx' : σ x = 3\n⊢ (if y = y then σ x else σ y) = 3",
              "h": "Guard true by reflexivity; <code>simp [hx']</code> finishes. Note the branches here are <i>not</i> equal, so this conjunct genuinely depends on the assignment having happened."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "Why no <code>x ≠ y</code> is needed — the argument, without Lean",
          "items": [
            {
              "k": "What we must show",
              "h": "After <code>y := x</code> from a store where <code>σ x = 3</code>: both <code>x</code> and <code>y</code> hold <code>3</code> in the new store <code>σ[y ↦ σ x]</code>."
            },
            {
              "k": "The value of y",
              "h": "<code>σ[y ↦ σ x] y = σ x = 3</code>. Unconditional."
            },
            {
              "k": "The value of x — case x ≠ y",
              "h": "The update misses <code>x</code>, so <code>σ[y ↦ σ x] x = σ x = 3</code>."
            },
            {
              "k": "The value of x — case x = y",
              "h": "The update hits <code>x</code>, so <code>σ[y ↦ σ x] x = σ x = 3</code>. The <i>same answer</i>, because the value written was read from <code>x</code> in the first place."
            },
            {
              "k": "Conclusion",
              "h": "The case split is vacuous. Lean makes this visible by presenting the two branches as one goal <code>(if x = y then σ x else σ x) = 3</code> rather than as two cases — the <code>if</code> never needs to be decided."
            }
          ]
        },
        {
          "t": "cmp",
          "left": {
            "t": "The explicit route (the solution)",
            "h": "Two <code>show</code>s expose the <code>if</code>s. Slower to write, and it forces you to look at <code>(if x = y then σ x else σ x)</code> — which is the only interesting fact in the exercise.",
            "src": "· show (if x = y then σ x else σ x) = 3\n  simp [hx']\n· show (if y = y then σ x else σ y) = 3\n  simp [hx']",
            "kind": "good"
          },
          "right": {
            "t": "The automatic route",
            "h": "Also compiles. <code>simp</code> collapses <code>if c then a else a</code> via <code>ite_self</code> and never shows you that it did. Fine in production, bad the first time: you would finish the exercise without noticing that aliasing was handled.",
            "src": "· simp [Store.set, hx']\n· simp [Store.set, hx']"
          }
        },
        {
          "t": "detail",
          "title": "What Lean says if you add the hypothesis anyway",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Add <code>(hxy : x ≠ y)</code> to the statement, leave the proof unchanged, and it still compiles — with a linter warning:"
            },
            {
              "t": "state",
              "src": "warning: Variable name `hxy` is not explicitly referenced.\n\nThe binding can be removed (if unused) or named `_` (if used implicitly).\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`",
              "cap": "The unused-variable linter is doing mathematics for you: it is telling you the theorem is stronger than you stated it."
            },
            {
              "t": "p",
              "h": "Treat that warning as a result, not as noise. Whenever it fires on a hypothesis you added from intuition, it is telling you that the intuition was about a different theorem — the side condition is not doing any work, and the statement you actually proved is stronger than the one you meant to state."
            }
          ]
        },
        {
          "t": "detail",
          "title": "Where <code>x ≠ y</code> <i>is</i> genuinely needed",
          "tag": "counterexample",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The intuition that wanted a disequality was not wrong in general, only about this program. Change the second command from a copy to a second constant — <code>x := 3 ;; y := 5</code> — and the side condition becomes load-bearing."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem assign_two_constants (x y : Var) (hxy : x ≠ y) :\n    Hoare emp (.assign x (.const 3) ;; .assign y (.const 5))\n      (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 5)) emp) := by\n  refine hoare_seq (Q := aAnd (fact (fun σ => σ x = 3)) emp) ?_ ?_\n  · intro σ h he\n    refine ⟨⟨Store.set σ x 3, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 3 x = 3\n    simp [Store.set]\n  · intro σ h hpre\n    obtain ⟨hx, he⟩ := hpre\n    have hx' : σ x = 3 := hx\n    refine ⟨⟨Store.set σ y 5, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ y 5 x = 3 ∧ Store.set σ y 5 y = 5\n    constructor\n    · show (if x = y then 5 else σ x) = 3\n      simp [hxy, hx']\n    · show (if y = y then 5 else σ y) = 5\n      simp\n\n-- and without the hypothesis it is false: instantiate x and y to the same variable\ntheorem not_assign_two_constants :\n    ¬ (∀ (x y : Var), Hoare emp (.assign x (.const 3) ;; .assign y (.const 5))\n        (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 5)) emp)) := by\n  intro hall\n  obtain ⟨s', _, hq, _⟩ := hall 0 0 (fun _ => 0) Heap.empty rfl\n  have h35 : (3 : Nat) = 5 := by rw [← hq.1, ← hq.2]\n  exact absurd h35 (by simp)\n\n-- for contrast: reversing the original program fails for a different reason\ntheorem not_assign_reversed :\n    ¬ (∀ (x y : Var), Hoare emp (.assign y (.var x) ;; .assign x (.const 3))\n        (aAnd (fact (fun σ => σ x = 3 ∧ σ y = 3)) emp)) := by\n  intro hall\n  obtain ⟨s', hex, hq, _⟩ := hall 0 1 (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | seq h₁ h₂ =>\n      cases h₁\n      cases h₂\n      have h0 : (0 : Nat) = 3 := hq.2\n      exact absurd h0 (by simp)",
              "cap": "All three compile against the M6 prelude. <code>simp [hxy, hx']</code> in the left branch really does use <code>hxy</code>: remove it and <code>simp</code> stops with <code>⊢ ¬x = y</code> unproved. The third theorem is the one discussed under <b>variants</b> — the two <code>cases</code> on the sequenced derivation compute the final store, after which <code>hq.2</code> reads <code>0 = 3</code>."
            },
            {
              "t": "p",
              "h": "The difference between the two exercises is one goal, and it is exactly the goal the <code>show</code> exposes:"
            },
            {
              "t": "cmp",
              "left": {
                "t": "<code>x := 3 ;; y := x</code> — no hypothesis needed",
                "h": "Both branches are the same term. There is nothing for a disequality to decide, so none is required.",
                "src": "⊢ (if x = y then σ x else σ x) = 3",
                "kind": "good"
              },
              "right": {
                "t": "<code>x := 3 ;; y := 5</code> — hypothesis needed",
                "h": "The branches differ, so the <code>if</code> has to be decided. <code>simp [hxy, hx']</code> runs as <code>simp only [hxy, ↓reduceIte, hx']</code>: <code>hxy</code> rewrites the guard to <code>False</code>, and only then can the <code>else</code> branch be taken. Drop <code>hxy</code> from the simp set and <code>simp</code> leaves you the residual goal <code>⊢ ¬x = y</code>, which is unprovable — that residue <i>is</i> the side condition.",
                "src": "⊢ (if x = y then 5 else σ x) = 3"
              }
            },
            {
              "t": "p",
              "h": "Both goal displays are Lean's, copied from the two proofs. Read them as the criterion: a side condition is needed exactly when the two branches of the <code>ite</code> that <code>Store.set</code> generates are not the same term."
            }
          ]
        }
      ],
      "pitfall": "Getting the <code>if</code> guard backwards in the <code>show</code>. <code>Store.set σ y v</code> is <code>fun z => if z = y then v else σ z</code>, so applying it at <code>x</code> gives <code>if x = y then …</code> — the <i>queried</i> variable on the left, the <i>updated</i> one on the right. Write <code>show (if y = x then σ x else σ x) = 3</code> and Lean refuses: <br><code>'show' tactic failed, pattern (if y = x then σ x else σ x) = 3 is not definitionally equal to target σ.set y (σ x) x = 3</code>. <br>Equality on <code>Var</code> is symmetric, but <code>show</code> checks definitional equality of terms, and <code>x = y</code> and <code>y = x</code> are different terms.",
      "variants": "Drop the second assignment and you are back at <code>assign_constant</code>. <br><br>Change the second command to <code>y := 5</code> and the side condition becomes real: <code>x := 3 ;; y := 5</code> needs <code>x ≠ y</code>, because with <code>x = y</code> the postcondition asserts <code>3 = 5</code>. Both the theorem and its refutation are mechanised in the aside above — that is the honest version of the hypothesis you were tempted to add here. <br><br>Reverse the program to <code>y := x ;; x := 3</code> and it fails, but <i>not</i> for an aliasing reason, so do not use it as the counterexample. After the copy, <code>y</code> holds the initial value of <code>x</code>, and the precondition <code>emp</code> says nothing about that value; the second assignment then fixes <code>x</code> and leaves <code>y</code> alone. So <code>σ y = 3</code> is unprovable whenever <code>x ≠ y</code> — take <code>x := 0</code>, <code>y := 1</code>, and the initial store <code>fun _ => 0</code>. In the <i>aliased</i> case <code>x = y</code> the triple is true again, for the trivial reason that there is only one variable. Adding <code>x ≠ y</code> makes that program worse, not better. <br><br>Change the intermediate assertion to <code>fact (fun σ => σ x = 3)</code> without the <code>emp</code> and the first subgoal still goes through, but the second cannot produce the <code>emp</code> in the final postcondition — <code>he</code> would have nowhere to come from. That is the general rule for intermediate assertions: they must carry forward everything the tail still needs, ownership included."
    },
    {
      "t": "p",
      "h": "Two things are conspicuously missing. There is no rule yet for <code>load</code>, <code>write</code> or <code>free</code> — everything so far has ignored the heap or passed it through untouched — and there is no way to prove a triple about a big heap from a triple about a small one. M7 supplies the first, in the smallest form that is true. M8 supplies the second, and shows that it is not free: the frame rule needs a locality property of the semantics, and there are perfectly reasonable commands for which it fails."
    },
    {
      "t": "dod",
      "h": "You can derive program proofs by composing triples, instead of unfolding <code>Exec</code> every time."
    }
  ]
});
