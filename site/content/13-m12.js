/* M12 — Weakest preconditions
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m12",
  "num": "M12",
  "phase": "Phase 3 · Advanced separation logic",
  "title": "Weakest preconditions",
  "blurb": "Turning verification from a search for proofs into a calculation.",

  "orient": {
    "youWill": [
      "Read <code>wp c Q</code> as an ordinary assertion, and prove its four structural equations — <code>wp_skip</code>, <code>wp_assign</code>, <code>wp_seq</code>, <code>wp_mono</code> — by taking <code>Exec</code> derivations apart and putting them back together.",
      "Move between a Hoare triple and an entailment into <code>wp</code> without proving anything, because in this development they are literally the same proposition.",
      "<i>Compute</i> the weakest precondition of a heap command instead of guessing it, and recognise the existential quantifier that appears over exactly the data the command never reads.",
      "Decide whether a precondition you wrote by hand is genuinely the weakest one — and exhibit the heap that proves it is not."
    ],
    "needs": [
      "<code>Hoare</code> and <code>Exec</code> from M5–M6. <code>wp</code> is defined straight out of <code>Exec</code>, so every proof here is an inversion or a construction of a derivation.",
      "Inversion of an inductive predicate: <code>cases hex with | free hl =&gt; …</code>, as used since M5.",
      "<code>funext</code>, <code>by_cases</code> and <code>subst</code> from M1–M2, together with the pointwise heap lemmas <code>singleton_other</code>, <code>write_other</code>, <code>erase_other</code>.",
      "The anonymous constructor <code>⟨…⟩</code> in both roles: as a term that builds an <code>∃</code>/<code>∧</code>, and as a pattern in <code>intro</code>."
    ],
    "payoff": "Every mechanised verification tool you are likely to meet — Dafny, Why3, Viper, Iris's proof mode — is a <code>wp</code> calculator; after this chapter you know what it is calculating, why the answer is forced rather than invented, and what it means for a precondition to be the honest one."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "Everything so far has been a <i>proof system</i>: you write down a triple, and then you hunt for a derivation. That is fine for six-line programs and hopeless for six-hundred-line ones. The alternative is to make the precondition an <b>output</b> rather than an input — given a command and a postcondition, compute the assertion that must hold beforehand. That is the weakest precondition."
    },
    {
      "t": "code",
      "src": "def wp (c : Cmd) (Q : Assertion) : Assertion :=\n  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap"
    },
    {
      "t": "anat",
      "src": "def wp (c : Cmd) (Q : Assertion) : Assertion :=\n  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap",
      "parts": [
        {
          "m": "(Q : Assertion)",
          "h": "The postcondition is an ordinary assertion — a <code>Store → Heap → Prop</code>. Nothing about it is syntactic, so there is no substitution machinery anywhere in this chapter."
        },
        {
          "m": ": Assertion :=",
          "h": "And the <i>result</i> is again an assertion. So <code>wp c</code> is a map from assertions to assertions: an <b>assertion transformer</b>. That is the whole design. The Hoare triple relates three things; <code>wp</code> turns one of them into a function of the other two."
        },
        {
          "m": "fun σ h =>",
          "h": "An assertion is a function of a store and a heap, so to define one you write a lambda in exactly those two arguments. Compare <code>emp</code> and <code>pointsTo</code> in M3: same shape."
        },
        {
          "m": "∃ s'",
          "h": "The existential is doing three jobs at once, exactly as it does in <code>Hoare</code>: it says the command does not get stuck on a missing cell, that it terminates, and that the state it reaches satisfies <code>Q</code>. Read <code>wp</code> as “safe, terminating, and lands in <code>Q</code>”."
        },
        {
          "m": "Exec c ⟨σ, h⟩ s'",
          "h": "<code>⟨σ, h⟩</code> is the anonymous constructor for the two-field structure <code>State</code>, with the fields given positionally in declaration order (<code>store</code>, then <code>heap</code>). Lean accepts the bare brackets because it knows from <code>Exec</code>'s type that a <code>State</code> is wanted here. Its pretty-printer will show the term back to you as <code>{ store := σ, heap := h }</code> — get used to that now, it appears in every goal below."
        },
        {
          "m": "Q s'.store s'.heap",
          "h": "<code>Q</code> wants a store and a heap, and <code>s'</code> is a <code>State</code>, so it is applied to the two projections. This is the small friction of using a structure for states and a curried pair for assertions; it costs one <code>.store</code> and one <code>.heap</code> everywhere, and buys pattern-matching on states everywhere else."
        }
      ]
    },
    {
      "t": "p",
      "h": "<code>wp c Q</code> is the set of states from which <code>c</code> runs safely and lands in <code>Q</code>. It is “weakest” because it is the <i>largest</i> such set: any valid precondition entails it."
    },
    {
      "t": "defn",
      "term": "weakest precondition",
      "h": "<code>wp c Q</code> is the greatest element of <code>{P | Hoare P c Q}</code> in the entailment order — <i>greatest</i> meaning weakest, since <code>P ⊢ P'</code> reads “<code>P</code> is at least as strong as <code>P'</code>”. Two things have to hold for that phrase to mean anything: <code>wp c Q</code> must itself be in the set, and every other member must entail it. Both are true <i>by definition</i> here, which is the next block. (The set is also downward closed — if <code>P ⊢ P'</code> and <code>P'</code> works then <code>P</code> works — which is precondition strengthening, <code>hoare_consequence</code>'s first argument.) Entailment is a preorder, not a partial order, so “greatest” is unique only up to <code>⊣⊢</code>."
    },
    {
      "t": "p",
      "h": "Notice that <code>wp</code> and <code>Hoare</code> are, in our formulation, the <b>same definition read two ways</b>:"
    },
    {
      "t": "code",
      "src": "theorem hoare_iff_entails_wp (P Q : Assertion) (c : Cmd) :\n    Hoare P c Q ↔ P ⊢ wp c Q := Iff.rfl"
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "That proof is <code>Iff.rfl</code> — not a theorem so much as an observation. <code>Hoare P c Q</code> unfolds to <code>∀ σ h, P σ h → (∃ s', …)</code>, and <code>P ⊢ wp c Q</code> unfolds to exactly the same thing. Forward Hoare reasoning and backward weakest-precondition reasoning are two readings of one statement."
    },
    {
      "t": "detail",
      "title": "Why <code>Iff.rfl</code> is allowed to work here",
      "tag": "Lean",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "<code>Iff.rfl : ?a ↔ ?a</code> proves an iff whose two sides Lean can see are the <i>same proposition</i>. Not equivalent — the same. So this is a claim about definitional unfolding, and it is worth doing the unfolding by hand once."
        },
        {
          "t": "txt",
          "src": "  Hoare P c Q\n= ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap      -- unfold Hoare\n\n  P ⊢ wp c Q\n= Entails P (wp c Q)\n= ∀ σ h, P σ h → wp c Q σ h                                        -- unfold Entails\n= ∀ σ h, P σ h → (fun σ h => ∃ s', …) σ h                          -- unfold wp\n= ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap       -- beta"
        },
        {
          "t": "p",
          "h": "Three <code>def</code> unfoldings and one beta-reduction, all of which Lean performs silently when it checks a term against a type. So the two sides really are one expression, and <code>Iff.rfl</code> typechecks."
        },
        {
          "t": "p",
          "h": "You can push this further: the two <i>types</i> are equal, not merely inter-provable, so even <code>rfl</code> works — an equation <i>between propositions</i>, at type <code>Prop</code>, rather than an iff between them."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "example (P Q : Assertion) (c : Cmd) : Hoare P c Q = (P ⊢ wp c Q) := rfl"
        },
        {
          "t": "p",
          "h": "And here is the boundary. Swap <code>Hoare</code> for <code>PartialHoare</code> and the same proof fails, because <code>PartialHoare</code> quantifies over <code>s'</code> universally and outside the implication — a genuinely different proposition, not a different spelling."
        },
        {
          "t": "code",
          "tag": "sketch",
          "src": "example (P Q : Assertion) (c : Cmd) : PartialHoare P c Q ↔ P ⊢ wp c Q := Iff.rfl"
        },
        {
          "t": "state",
          "cap": "what Lean actually says",
          "src": "error: Type mismatch\n  Iff.rfl\nhas type\n  ?m.1 ↔ ?m.1\nbut is expected to have type\n  PartialHoare P c Q ↔ P ⊢ wp c Q"
        },
        {
          "t": "p",
          "h": "The metavariable display <code>?m.1 ↔ ?m.1</code> is Lean telling you what it wanted: one proposition, used twice. It could not find one that fits both slots."
        }
      ]
    },
    {
      "t": "p",
      "h": "The practical difference is directional. A Hoare-triple proof goes <i>forwards</i>: you push the precondition through the program and hope to arrive at something entailing the postcondition. A <code>wp</code> proof goes <i>backwards</i>: you push the postcondition through the program and end up with an assertion to be checked against the precondition. Backwards is usually more mechanical, which is why every practical verification tool — Dafny, Why3, Iris's proof mode — is built on <code>wp</code>."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Forwards (M6–M9)",
        "h": "Split the program with <code>hoare_seq (Q := …)</code>. <b>You</b> must invent the intermediate assertion at every join. Guess wrong and the second half does not close, and you have to go back and guess again. Verification is a search.",
        "tag": "sketch",
        "src": "hoare_seq (Q := ???)\n  step₁_spec\n  step₂_spec"
      },
      "right": {
        "t": "Backwards (this chapter)",
        "h": "Start at the postcondition and apply <code>wp_seq</code> repeatedly. The intermediate assertion is <i>produced</i>, never chosen. What is left at the front is a single entailment between the given precondition and the computed one — a pure logic problem with no program in it.",
        "kind": "good",
        "tag": "sketch",
        "src": "wp (c₁ ;; c₂) Q\n  ⊣⊢ wp c₁ (wp c₂ Q)\n         └── computed, not guessed"
      }
    },
    {
      "t": "steps",
      "title": "Calculating backwards, on the smallest interesting example",
      "items": [
        {
          "k": "Write the program and the postcondition",
          "h": "Take <code>x := 3 ;; y := x</code> and an arbitrary postcondition <code>Q</code>. We want the weakest <code>P</code> making the triple hold."
        },
        {
          "k": "Peel the last command first",
          "h": "<code>wp_seq</code> turns <code>wp (c₁ ;; c₂) Q</code> into <code>wp c₁ (wp c₂ Q)</code>. Note the order: the <i>inner</i> application is the <i>later</i> command. Backwards reasoning is a right fold."
        },
        {
          "k": "Replace each wp by its equation",
          "h": [
            {
              "t": "p",
              "h": "<code>wp_assign</code> says <code>wp (.assign x e) Q ⊣⊢ subst x e Q</code>. Apply it to the inner one, then the outer one:"
            },
            {
              "t": "txt",
              "src": "  wp (x := 3 ;; y := x) Q\n⊣⊢ wp (x := 3) (wp (y := x) Q)          -- wp_seq\n⊣⊢ wp (x := 3) (subst y (var x) Q)      -- wp_assign, inner\n⊣⊢ subst x (const 3) (subst y (var x) Q) -- wp_assign, outer"
            }
          ]
        },
        {
          "k": "Nothing was invented",
          "h": "The last line is the weakest precondition. Of course it depends on <code>Q</code> — <code>Q</code> is sitting inside it. What does <i>not</i> depend on <code>Q</code> is the calculation: at each step the equation to apply was determined by the outermost command and nothing else, so the same fold works for every postcondition you might care to substitute. That is what “calculus” means here. In Lean the same chain is four lemma applications glued with <code>entails_trans</code>, once in each direction."
        }
      ]
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "the calculation above, done in Lean; compiles against the M12 prelude",
      "src": "example (x y : Var) (Q : Assertion) :\n    wp (.assign x (.const 3) ;; .assign y (.var x)) Q\n      ⊣⊢ subst x (.const 3) (subst y (.var x) Q) := by\n  constructor\n  · refine entails_trans (wp_seq _ _ Q).1 ?_\n    refine entails_trans (wp_mono _ (wp_assign y (.var x) Q).1) ?_\n    exact (wp_assign x (.const 3) _).1\n  · refine entails_trans (wp_assign x (.const 3) _).2 ?_\n    refine entails_trans (wp_mono _ (wp_assign y (.var x) Q).2) ?_\n    exact (wp_seq _ _ Q).2"
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "Reading <code>.1</code> and <code>.2</code> off an <code>⊣⊢</code>",
      "h": "<code>AssertionEquiv P Q</code> is defined as <code>Entails P Q ∧ Entails Q P</code> — a bare <code>And</code>. So an <code>⊣⊢</code> lemma is a pair, and <code>.1</code> / <code>.2</code> are the two entailments. There is no special <code>Iff</code> machinery to learn; <code>(wp_seq c₁ c₂ Q).1</code> is just <code>And.left</code> applied to a theorem. Two forward references in that snippet: <code>wp_mono</code> is exercise m12-3, and it is what lets the middle line rewrite the <i>inner</i> <code>wp</code> while leaving the outer one alone. <code>entails_trans</code> is M3's composition of entailments, and <code>refine … ?_</code> supplies its first argument while leaving the second as the next goal — which is what makes a chain of them read top to bottom."
    },
    {
      "t": "h4",
      "s": "Which equations exist, and which are work"
    },
    {
      "t": "tbl",
      "cap": "the wp calculus for our language; the five rows carrying an exercise id are proved here, and they are the ones that make the rest routine",
      "head": ["command", "<code>wp c Q</code>", "status"],
      "rows": [
        ["<code>skip</code>", "<code>Q</code>", "m12-1"],
        ["<code>x := e</code>", "<code>subst x e Q</code>", "m12-1"],
        ["<code>c₁ ;; c₂</code>", "<code>wp c₁ (wp c₂ Q)</code>", "m12-2"],
        ["<code>free l</code>, with <code>Q = emp</code>", "<code>∃ v, l ↦ v</code>", "m12-4"],
        ["<code>[l] := new</code>, with <code>Q = l ↦ new</code>", "<code>∃ old, l ↦ old</code>", "m12-5"],
        ["<code>x := [l]</code>, general <code>Q</code>", "<code>∃ v, ⌜h l = some v⌝ ∧ Q[σ[x ↦ v]]</code>", "six lines; see the aside below"],
        ["<code>if b then c₁ else c₂</code>", "<code>(b ∧ wp c₁ Q) ∨ (¬b ∧ wp c₂ Q)</code>", "same pattern, two constructors; in the aside below"],
        ["<code>while b do c</code>", "<b>least</b> fixed point of <code>X ↦ (b ∧ wp c X) ∨ (¬b ∧ Q)</code>", "not an equation — M13 uses invariants instead"]
      ]
    },
    {
      "t": "detail",
      "title": "The two missing equations: <code>wp</code> of a load, and of an <code>if</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "The corpus does not prove a general <code>wp</code> equation for <code>load</code>, but the shape is worth seeing once, because it is the shape of <i>every</i> heap command: an existential over the value the command reads, a footprint condition saying that value is really there, and the postcondition evaluated after the effect."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem wp_load (x : Var) (l : Loc) (Q : Assertion) :\n    wp (.load x l) Q ⊣⊢\n      aExists (fun v => aAnd (fun _ h => h l = some v)\n                             (fun σ h => Q (Store.set σ x v) h)) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | load hl => rename_i v; exact ⟨v, hl, hq⟩\n  · intro σ h ⟨v, hl, hq⟩\n    exact ⟨⟨Store.set σ x v, h⟩, Exec.load hl, hq⟩"
        },
        {
          "t": "p",
          "h": "Six lines, and only two of them are content: forwards, invert the derivation and read the value off it; backwards, build the derivation from the value. Exercises m12-4 and m12-5 are this same proof, specialised to a particular <code>Q</code> and with the extra work of proving that the resulting heap condition <i>is</i> a points-to."
        },
        {
          "t": "p",
          "h": "The conditional is the same move once more, with two constructors to invert instead of one. This is the equation the table above claims; here it is, so that “same pattern” is a checked statement rather than a promise."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem wp_ite (b : BExpr) (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (.ite b c₁ c₂) Q ⊣⊢\n      aOr (aAnd (fact (fun σ => b.eval σ = true))  (wp c₁ Q))\n          (aAnd (fact (fun σ => b.eval σ = false)) (wp c₂ Q)) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | iteTrue  hb hc => exact Or.inl ⟨hb, s', hc, hq⟩\n    | iteFalse hb hc => exact Or.inr ⟨hb, s', hc, hq⟩\n  · intro σ h hor\n    cases hor with\n    | inl hl => obtain ⟨hb, s', hc, hq⟩ := hl; exact ⟨s', Exec.iteTrue  hb hc, hq⟩\n    | inr hr => obtain ⟨hb, s', hc, hq⟩ := hr; exact ⟨s', Exec.iteFalse hb hc, hq⟩"
        },
        {
          "t": "p",
          "h": "The <code>∧</code> here is <code>aAnd</code> and the guard is wrapped in <code>fact</code>, both from M3: <code>fact φ</code> is the assertion <code>fun σ _ => φ σ</code>, a fact about the store that says nothing about the heap. Note that <code>cases hor</code> in the backward direction is inverting an <code>Or</code>, not an <code>Exec</code> — the two constructors are <code>inl</code> and <code>inr</code>. Every command whose semantics has <i>k</i> constructors gets a <code>wp</code> equation with <i>k</i> disjuncts; <code>loop</code> is the exception only because one of its two constructors is recursive."
        }
      ]
    },
    {
      "t": "sec",
      "s": "Exercises · the equations of wp"
    },
    {
      "t": "ex",
      "id": "m12-1",
      "name": "wp_skip / wp_assign",
      "hard": false,
      "why": "The two base cases. <code>wp_assign</code> is the assignment axiom in its natural, backwards form — and now the semantic <code>subst</code> looks obviously right rather than clever. They are also the place to learn the rhythm every proof in this chapter follows: forwards you <b>take a derivation apart</b>, backwards you <b>build one</b>.",
      "setup": "In scope: <code>wp</code>, <code>Hoare</code>, <code>subst</code> from M6, the <code>Exec</code> constructors from M5, and <code>⊣⊢</code> (which is a bare <code>And</code> of two <code>Entails</code>). You will need <code>Exec.skip</code> and <code>Exec.assign</code>.",
      "goal": "theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q\ntheorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :\n    wp (.assign x e) Q ⊣⊢ subst x e Q",
      "hints": [
        "<code>⊣⊢</code> is a conjunction of two entailments. Start with <code>constructor</code> and treat the two directions completely separately — they are different proofs, not two halves of one.",
        "Forwards you are <i>given</i> a run and must say where it ended. The only way to learn that is to invert the <code>Exec</code> derivation: <code>cases hex</code>. There is exactly one constructor that could have produced it, so you get exactly one subgoal.",
        "Backwards you must <i>supply</i> the final state, a derivation reaching it, and a proof of <code>Q</code> there — three things, so an anonymous constructor with three components. For <code>skip</code> the final state is <code>⟨σ, h⟩</code>; for <code>assign</code> it is <code>⟨Store.set σ x (e.eval σ), h⟩</code>, which is precisely the state <code>subst</code> was defined to talk about.",
        "Each direction: forwards, <code>cases hex</code> to see what the final state was; backwards, supply the state and the derivation."
      ],
      "sol": "theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex; exact hq\n  · intro σ h hq\n    exact ⟨⟨σ, h⟩, Exec.skip, hq⟩\n\ntheorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :\n    wp (.assign x e) Q ⊣⊢ subst x e Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex; exact hq\n  · intro σ h hq\n    exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
      "expl": "Both theorems have the same five-line skeleton, and the interesting move is <code>cases hex</code>. It is not there to do case analysis — there is only one case. It is there to <b>learn an equation</b>: inverting <code>Exec .skip ⟨σ,h⟩ s'</code> forces <code>s'</code> to be <code>⟨σ,h⟩</code>, and inverting <code>Exec (.assign x e) ⟨σ,h⟩ s'</code> forces it to be the updated state. Once Lean knows that, <code>hq</code> already has the type the goal wants — up to unfolding, which is the whole subtlety and is spelled out in the trace below.",
      "walk": [
        {
          "tac": "constructor",
          "h": "The goal <code>wp .skip Q ⊣⊢ Q</code> is <code>AssertionEquiv</code>, which is <code>And</code>. <code>constructor</code> applies the only constructor <code>And.intro</code>, splitting into <code>case left</code> (<code>wp .skip Q ⊢ Q</code>) and <code>case right</code> (<code>Q ⊢ wp .skip Q</code>)."
        },
        {
          "tac": "· intro σ h ⟨s', hex, hq⟩",
          "h": "<code>Entails P Q</code> unfolds to <code>∀ σ h, P σ h → Q σ h</code>, so <code>intro</code> takes three things. The third is destructured on the spot: <code>wp .skip Q σ h</code> is <code>∃ s', Exec … ∧ Q …</code>, so the pattern <code>⟨s', hex, hq⟩</code> names the witness, the derivation and the postcondition proof in one move. This is <code>obtain</code> folded into <code>intro</code>."
        },
        {
          "tac": "cases hex; exact hq",
          "h": "<code>cases hex</code> asks: which constructor of <code>Exec</code> could have concluded <code>Exec .skip ⟨σ,h⟩ s'</code>? Only <code>Exec.skip</code>, and it forces <code>s' := ⟨σ,h⟩</code>. So <code>hq</code>, whose type mentioned the unknown <code>s'</code>, now mentions <code>⟨σ,h⟩</code>, and its projections reduce to <code>σ</code> and <code>h</code>. <code>exact hq</code> closes the goal by definitional unfolding — see the trace."
        },
        {
          "tac": "· intro σ h hq",
          "h": "The other direction. Here <code>hq : Q σ h</code> needs no destructuring; the work is all in the goal, which is <code>wp .skip Q σ h</code> — an existential to be built."
        },
        {
          "tac": "exact ⟨⟨σ, h⟩, Exec.skip, hq⟩",
          "h": "Three components for <code>∃ s', Exec .skip ⟨σ,h⟩ s' ∧ Q s'.store s'.heap</code>: the witness <code>⟨σ, h⟩</code> (itself an anonymous constructor, this time for <code>State</code>), the derivation <code>Exec.skip</code>, and <code>hq</code>. Lean flattens <code>⟨a, b, c⟩</code> into <code>⟨a, ⟨b, c⟩⟩</code> automatically, which is why an <code>∃</code>-then-<code>∧</code> takes three slots rather than two."
        },
        {
          "tac": "theorem wp_assign (x : Var) (e : Atom) (Q : Assertion) : wp (.assign x e) Q ⊣⊢ subst x e Q := by",
          "h": "Second theorem, same skeleton. The only new ingredient is that the right-hand side is <code>subst x e Q</code>, which by definition is <code>fun σ h => Q (Store.set σ x (e.eval σ)) h</code> — an assertion about the <i>post</i>-assignment store."
        },
        {
          "tac": "constructor",
          "h": "Split into the two entailments again."
        },
        {
          "tac": "· intro σ h ⟨s', hex, hq⟩",
          "h": "Same destructuring intro; the goal becomes <code>subst x e Q σ h</code>."
        },
        {
          "tac": "cases hex; exact hq",
          "h": "Inverting <code>Exec (.assign x e) ⟨σ,h⟩ s'</code> forces <code>s'</code> to be <code>⟨Store.set σ x (e.eval σ), h⟩</code>. Now <code>hq</code>'s type is <code>Q</code> at that state, and <code>subst x e Q σ h</code> unfolds to exactly that. <code>exact hq</code> — the assignment axiom is a tautology once <code>subst</code> is semantic."
        },
        {
          "tac": "· intro σ h hq",
          "h": "Backwards. <code>hq : subst x e Q σ h</code>, which is <i>already</i> a proof of <code>Q</code> at the post-state; nothing needs converting."
        },
        {
          "tac": "exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
          "h": "Supply the post-state explicitly, the constructor <code>Exec.assign</code> (which takes no explicit arguments — the state is determined by the implicit ones), and <code>hq</code>. Note that you must write the post-state out; Lean will not guess it from <code>Exec.assign</code> before it has unified the existential."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "wp_skip, tactic by tactic",
          "start": "Q : Assertion\n⊢ wp Cmd.skip Q ⊣⊢ Q",
          "steps": [
            {
              "tac": "constructor",
              "state": "case left\nQ : Assertion\n⊢ wp Cmd.skip Q ⊢ Q\n\ncase right\nQ : Assertion\n⊢ Q ⊢ wp Cmd.skip Q",
              "h": "Two goals. Lean names them after the constructor's argument names, <code>left</code> and <code>right</code> of <code>And.intro</code>. Note it prints <code>Cmd.skip</code> where the source wrote <code>.skip</code> — dot notation is elaboration sugar and does not survive into the goal display."
            },
            {
              "tac": "intro σ h ⟨s', hex, hq⟩",
              "state": "case left\nQ : Assertion\nσ : Store\nh : Heap\ns' : State\nhex : Exec Cmd.skip { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ Q σ h",
              "h": "Three <code>intro</code>s, the third destructured. <code>⟨σ, h⟩</code> from the definition of <code>wp</code> now prints as <code>{ store := σ, heap := h }</code>. The goal is <code>Q σ h</code>; the hypothesis is <code>Q s'.store s'.heap</code>. These are not the same until we know what <code>s'</code> is."
            },
            {
              "tac": "cases hex",
              "state": "case left.skip\nQ : Assertion\nσ : Store\nh : Heap\nhq : Q { store := σ, heap := h }.store { store := σ, heap := h }.heap\n⊢ Q σ h",
              "h": "Here is the move. <code>s'</code> and <code>hex</code> are gone; every occurrence of <code>s'</code> has been replaced by the literal <code>{ store := σ, heap := h }</code>. The case is named <code>left.skip</code> — the outer goal name, then the constructor. And look at <code>hq</code>: Lean does <i>not</i> simplify <code>{ store := σ, heap := h }.store</code> to <code>σ</code> in the display, even though it will happily do so when checking."
            },
            {
              "tac": "exact hq",
              "state": "No goals.",
              "h": "It works because projection-of-a-literal is a definitional reduction (an iota rule): <code>{ store := σ, heap := h }.store</code> reduces to <code>σ</code>. <code>exact</code> checks up to definitional equality, so it accepts. This is the single most common source of “but those look different!” in this chapter — the displayed type and the accepted type differ by reductions Lean does not bother to print."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "wp_assign, the forward direction — and a spectacular goal display",
          "start": "case left\nx : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.assign x e) { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ subst x e Q σ h",
          "steps": [
            {
              "tac": "cases hex",
              "state": "case left.assign\nx : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\nhq :\n  Q\n    { store := { store := σ, heap := h }.store.set x (Atom.eval { store := σ, heap := h }.store e),\n        heap := { store := σ, heap := h }.heap }.store\n    { store := { store := σ, heap := h }.store.set x (Atom.eval { store := σ, heap := h }.store e),\n        heap := { store := σ, heap := h }.heap }.heap\n⊢ subst x e Q σ h",
              "h": "This is what the <code>Exec.assign</code> constructor's conclusion looks like when its implicit <code>s</code> has been instantiated to <code>{ store := σ, heap := h }</code> and nothing has been reduced. Three things to notice. <b>(1)</b> <code>Store.set σ x v</code> prints as <code>σ.set x v</code>: Lean's pretty-printer turns any application <code>Foo.bar a …</code> back into <code>a.bar …</code> when <code>a</code>'s type is <code>Foo</code> — so a name you wrote in prefix form comes back at you in dot form. <b>(2)</b> Conversely, the source's <code>e.eval σ</code> prints as <code>Atom.eval σ e</code>, and does <i>not</i> collapse to dot notation, because <code>Atom.eval</code> declares the store first (<code>def Atom.eval (σ : Store) : Atom → Val</code>); the <code>Atom</code> is not the first explicit argument, so the printer leaves it prefix. The two rules together mean you cannot predict which spelling you will see — read them as the same term and move on. <b>(3)</b> Nothing was simplified."
            },
            {
              "tac": "exact hq",
              "state": "No goals.",
              "h": "Reduce the projections and this hypothesis is <code>Q (Store.set σ x (e.eval σ)) h</code>. Unfold <code>subst</code> in the goal and it is <code>Q (Store.set σ x (e.eval σ)) h</code>. Same term. Lean does both reductions during the check and never shows you either."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "What a beginner tries",
            "kind": "bad",
            "h": "Skip the inversion — surely <code>hq</code> is what we want? It is not: <code>s'</code> is still an opaque variable, so <code>Q s'.store s'.heap</code> and <code>Q σ h</code> have nothing to do with each other.",
            "tag": "sketch",
            "src": "intro σ h ⟨s', hex, hq⟩\nexact hq\n\n-- error: Type mismatch\n--   hq\n-- has type\n--   Q s'.store s'.heap\n-- but is expected to have type\n--   Q σ h"
          },
          "right": {
            "t": "Why <code>simp</code> does not rescue you either",
            "h": "<code>simp [wp]</code> unfolds the definition and stops. It cannot invert an inductive predicate — that is <code>cases</code>'s job, not a rewrite. Reaching for <code>simp</code> when the obstacle is an inductive hypothesis is the classic wrong reflex.",
            "tag": "sketch",
            "src": "intro σ h hw\nsimp [wp] at hw\n-- hw : ∃ s', Exec Cmd.skip { store := σ, heap := h } s' ∧ Q s'.store s'.heap\n-- ⊢ Q σ h        (unchanged)"
          }
        },
        {
          "t": "detail",
          "title": "Why <code>⟨a, b, c⟩</code> has three slots for a two-argument connective",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The goal is <code>∃ s', Exec … s' ∧ Q …</code>, which is <code>Exists.intro</code> applied to a witness and a proof of an <code>And</code> — so strictly <code>⟨⟨σ,h⟩, ⟨Exec.skip, hq⟩⟩</code>. The anonymous constructor notation right-associates automatically: if you supply more components than the constructor takes, the surplus is bundled into the last argument, recursively. So <code>⟨a, b, c⟩</code>, <code>⟨a, ⟨b, c⟩⟩</code> and (where it applies) <code>⟨⟨a, b⟩, c⟩</code> can all elaborate, and which ones do depends on the type."
            },
            {
              "t": "p",
              "h": "The same flattening works in <code>intro</code> and <code>obtain</code> patterns, which is why <code>intro σ h ⟨s', hex, hq⟩</code> peels an <code>∃</code> and an <code>∧</code> with one pattern. You will see a five-deep version of this in <code>wp_seq</code>."
            }
          ]
        }
      ],
      "pitfall": "Writing <code>exact hq</code> before <code>cases hex</code>. The two types look close enough that it is tempting, but <code>s'</code> is a bound variable about which nothing is known until you invert the derivation; Lean reports <code>Type mismatch … has type Q s'.store s'.heap but is expected to have type Q σ h</code>. The reverse trap is the one that makes people distrust Lean: <i>after</i> <code>cases</code>, the displayed type of <code>hq</code> is a nest of projections that looks nothing like the goal, and <code>exact hq</code> works anyway. Displayed shape and definitional shape are different things — never conclude from the goal display that a term will not typecheck.",
      "variants": "Change <code>wp .skip Q ⊣⊢ Q</code> to <code>wp .skip Q ⊢ Q</code> and you keep only the interesting half; the converse is the half that needs a derivation to exist, i.e. the half that would fail for a command that can get stuck. Now try to prove the same statement for <code>.load x l</code> with the postcondition unchanged: <code>wp (.load x l) Q ⊢ Q</code> is <i>false</i>, because the run changes the store. And <code>Q ⊢ wp (.load x l) Q</code> is false for a different reason — the backward direction needs a derivation, and <code>Exec.load</code> demands <code>h l = some v</code>, which no assumption gives you. Those two failures are exactly the two jobs <code>wp</code> does: transport the postcondition, and assert safety."
    },
    {
      "t": "ex",
      "id": "m12-2",
      "name": "wp_seq",
      "hard": false,
      "why": "<b>The rule that makes backwards reasoning work.</b> It says <code>wp</code> of a sequence is the composition of the two transformers — so verifying a straight-line program becomes a fold from the end. Without it, <code>wp</code> would be a definition with no calculus attached; with it, the intermediate assertion at every <code>;;</code> stops being something you invent.",
      "setup": "You need the <code>seq</code> constructor of <code>Exec</code>, which takes two derivations and an intermediate state. Note that the intermediate state is an <i>implicit</i> argument of the constructor, which has a visible consequence in the proof.",
      "goal": "theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q)",
      "hints": [
        "Both directions are about the intermediate state. Forwards it is hidden inside the derivation you are given; backwards it is hidden inside the nested <code>wp</code> you are given. In each case, dig it out and hand it to the other side.",
        "Forwards: <code>cases hex with | seq h₁ h₂ =&gt;</code> names the two sub-derivations. It does <i>not</i> give you a name for the state between them, because that state is an implicit argument of the constructor. Use <code>_</code> and let unification find it — or <code>rename_i</code> if you prefer to name it.",
        "Backwards: the hypothesis is <code>wp c₁ (wp c₂ Q) σ h</code>, which unfolds to <code>∃ s₁, Exec c₁ … s₁ ∧ ∃ s₂, Exec c₂ … s₂ ∧ Q …</code>. A single flat pattern <code>⟨s₁, hex₁, s₂, hex₂, hq⟩</code> takes all five components at once. Then <code>Exec.seq hex₁ hex₂</code> glues.",
        "Forwards, invert the <code>seq</code> derivation. Backwards, glue with <code>Exec.seq</code>. No determinism is needed in either direction."
      ],
      "sol": "theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q) := by\n  constructor\n  · intro σ h ⟨s'', hex, hq⟩\n    cases hex with\n    | seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩\n  · intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩\n    exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",
      "expl": "It is worth noticing that determinism is <i>not</i> used. The equation holds for nondeterministic languages too, provided <code>wp</code> is read as “there exists a terminating run landing in <code>Q</code>” (angelic) rather than “all runs do” (demonic). Our definition is the angelic one; a demonic <code>wp</code> would use <code>∀</code> and would need <code>Exec</code> to be total.",
      "walk": [
        {
          "tac": "constructor",
          "h": "Split the <code>⊣⊢</code> into <code>case left</code> and <code>case right</code>."
        },
        {
          "tac": "· intro σ h ⟨s'', hex, hq⟩",
          "h": "<code>s''</code> is the <i>final</i> state of the whole sequence — two primes because it is the state after two commands. <code>hex : Exec (c₁ ;; c₂) ⟨σ,h⟩ s''</code>."
        },
        {
          "tac": "cases hex with",
          "h": "Invert. Only <code>Exec.seq</code> can conclude a <code>;;</code>, so there is one branch; the <code>with</code> form lets you name that branch's arguments instead of accepting <code>rename_i</code>-style anonymous ones."
        },
        {
          "tac": "| seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩",
          "h": "<code>h₁ : Exec c₁ ⟨σ,h⟩ s'✝</code> and <code>h₂ : Exec c₂ s'✝ s''</code>, where <code>s'✝</code> is the intermediate state — inaccessible, so you cannot type its name. The goal is <code>wp c₁ (wp c₂ Q) σ h</code>: supply the intermediate state (write <code>_</code>; unification reads it off <code>h₁</code>), then <code>h₁</code>, then a proof of <code>wp c₂ Q</code> at that state, which is <code>⟨s'', h₂, hq⟩</code>."
        },
        {
          "tac": "· intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩",
          "h": "The backward direction, with a five-component flat pattern: <code>s₁</code> the state after <code>c₁</code>, <code>hex₁</code> the first run, then the nested <code>wp c₂ Q</code> destructured into <code>s₂</code>, <code>hex₂</code>, <code>hq</code>. The flattening is the same rule as in m12-1, applied twice."
        },
        {
          "tac": "exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",
          "h": "The final state of the composite run is <code>s₂</code>; <code>Exec.seq</code> glues the two derivations by unifying its implicit middle state with <code>s₁</code>; <code>hq</code> is already about <code>s₂</code>. One subtlety, invisible here and explained in the trace: <code>hex₂</code>'s start state is displayed as <code>{ store := s₁.store, heap := s₁.heap }</code>, not <code>s₁</code>, and <code>Exec.seq</code> accepts it because structure eta makes those the same term."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "wp_seq, both directions",
          "start": "case left\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns'' : State\nhex : Exec (c₁ ;; c₂) { store := σ, heap := h } s''\nhq : Q s''.store s''.heap\n⊢ wp c₁ (wp c₂ Q) σ h",
          "steps": [
            {
              "tac": "cases hex with | seq h₁ h₂ =>",
              "state": "case left.seq\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns'' : State\nhq : Q s''.store s''.heap\ns'✝ : State\nh₁ : Exec c₁ { store := σ, heap := h } s'✝\nh₂ : Exec c₂ s'✝ s''\n⊢ wp c₁ (wp c₂ Q) σ h",
              "h": "There it is: <code>s'✝ : State</code>. The dagger marks an <b>inaccessible</b> name — Lean invented it because the constructor's binder <code>{s'}</code> is implicit and <code>cases … with | seq h₁ h₂</code> only named the two explicit arguments. You cannot write <code>s'✝</code> in source. That is why the solution writes <code>⟨_, h₁, …⟩</code>: the underscore is an instruction to unification, which recovers the state from the type of <code>h₁</code>. If you would rather name it, <code>rename_i sMid</code> immediately after the arrow renames the most recent inaccessible hypothesis, exactly as in <code>heapLocal_seq</code> back in M8."
            },
            {
              "tac": "exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩",
              "state": "No goals.",
              "h": "The nesting mirrors the statement: the outer triple is for <code>wp c₁ (…)</code>, the inner one for <code>wp c₂ Q</code> at the intermediate state. Writing it fully flat as <code>⟨_, h₁, s'', h₂, hq⟩</code> also works — the flattening rule does not care where the brackets were."
            },
            {
              "tac": "intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩",
              "state": "case right\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\ns₂ : State\nhex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂\nhq : Q s₂.store s₂.heap\n⊢ wp (c₁ ;; c₂) Q σ h",
              "h": "Look at <code>hex₂</code>: its start state is <code>{ store := s₁.store, heap := s₁.heap }</code>, not <code>s₁</code>. That is because <code>wp c₂ Q</code> was applied to <code>s₁.store</code> and <code>s₁.heap</code>, and <code>wp</code> repackages its two arguments into a <code>State</code>. The two are definitionally equal by <b>eta for structures</b>: any <code>s : State</code> is the same term as <code>{ store := s.store, heap := s.heap }</code>. This is why the next line typechecks with no massaging at all."
            },
            {
              "tac": "exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",
              "state": "No goals.",
              "h": "<code>Exec.seq</code> needs <code>Exec c₁ s s'</code> and <code>Exec c₂ s' s''</code> with a common <code>s'</code>. Unification takes <code>s' := s₁</code> from <code>hex₁</code> and then checks <code>hex₂</code> against <code>Exec c₂ s₁ s₂</code>, which holds up to eta."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The mathematics underneath, in one line each",
          "items": [
            {
              "k": "Forwards is associativity of “there is a run”",
              "h": "A run of <code>c₁ ;; c₂</code> from <code>s</code> to <code>s''</code> <i>is</i> a pair of runs through some middle state. Splitting it and re-bracketing the existentials is the whole proof: <code>∃ s'', (∃ s', R₁ s s' ∧ R₂ s' s'') ∧ Q s''</code> becomes <code>∃ s', R₁ s s' ∧ (∃ s'', R₂ s' s'' ∧ Q s'')</code>."
            },
            {
              "k": "Backwards is the same re-bracketing, read right to left",
              "h": "Which is why the two branches of the proof are near-mirror images and neither needs a lemma."
            },
            {
              "k": "So <code>wp</code> is a homomorphism",
              "h": "<code>wp (c₁ ;; c₂) = wp c₁ ∘ wp c₂</code> as assertion transformers, and <code>wp .skip = id</code> by m12-1. Sequencing is a monoid with <code>skip</code> as unit, transformers form a monoid under composition, and <code>wp</code> is a monoid map between them. That is “verification is compositional”, stated so that it can be checked."
            }
          ]
        },
        {
          "t": "detail",
          "title": "Angelic and demonic <code>wp</code>, and why they coincide here",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The <code>expl</code> above claims our <code>wp</code> is the angelic one. Here is the demonic reading written out — safety, plus <i>all</i> runs land in <code>Q</code> — together with a proof that in our deterministic language the two agree."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "def wpDemonic (c : Cmd) (Q : Assertion) : Assertion :=\n  fun σ h => (∃ s', Exec c ⟨σ, h⟩ s') ∧ ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap\n\ntheorem wp_eq_wpDemonic (c : Cmd) (Q : Assertion) : wp c Q ⊣⊢ wpDemonic c Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    refine ⟨⟨s', hex⟩, ?_⟩\n    intro s'' hex''\n    rw [exec_deterministic hex'' hex]\n    exact hq\n  · intro σ h ⟨⟨s', hex⟩, hall⟩\n    exact ⟨s', hex, hall s' hex⟩"
            },
            {
              "t": "p",
              "h": "The forward direction is the only one that uses anything: <code>exec_deterministic</code> from M5, to say that the run you were handed is the run you were promised. The backward direction is pure plumbing. That is the checked part, and it is the whole of it: <code>wp</code> and <code>wpDemonic</code> agree in <i>our</i> language. Everything in the next paragraph is about a language we do not have, so read it as orientation, not as theorem."
            },
            {
              "t": "p",
              "h": "Drop determinism and the forward direction is the one that breaks: “some run lands in <code>Q</code>” no longer implies “every run does”, so the angelic reading admits states the demonic one rejects and the equivalence becomes a one-way entailment. Which is the useful one depends on who chooses the run. If it is you — a scheduler you control, an oracle, a proof search — the angelic reading is what you want. If it is an adversary, you need the guarantee to hold for every run, so real tools take the demonic one. We can afford the angelic one only because our <code>Exec</code> leaves nothing to choose."
            },
            {
              "t": "p",
              "h": "Note also the <b>safety conjunct</b> in <code>wpDemonic</code>. Without <code>∃ s', Exec c ⟨σ,h⟩ s'</code>, a state from which <code>c</code> faults would vacuously satisfy <code>∀ s', … → Q</code>, and the transformer would happily certify a program that dereferences a dangling pointer. Separating that conjunct out is how the literature distinguishes partial from total correctness at the <code>wp</code> level."
            }
          ]
        }
      ],
      "pitfall": "Trying to name the intermediate state. <code>cases hex with | seq h₁ h₂ =&gt;</code> names two things, and the state between them is not one of them — it is implicit in the constructor, so Lean calls it <code>s'✝</code> and you cannot refer to it. The fix is either <code>_</code> in the term you build (unification finds it) or <code>rename_i sMid</code> on the line after the arrow. The second pitfall is subtler: in the backward direction you may be tempted to “fix up” <code>hex₂</code> because its start state prints as <code>{ store := s₁.store, heap := s₁.heap }</code> rather than <code>s₁</code>. Do not. Structure eta already makes them the same term, and any <code>show</code> or <code>rw</code> you add to repair it will be rejected for having nothing to rewrite.",
      "variants": "Reverse the composition — claim <code>wp (c₁ ;; c₂) Q ⊣⊢ wp c₂ (wp c₁ Q)</code> — and both directions fail, because the states no longer line up: <code>Exec c₂</code> would have to start where the whole program starts. The order is forced by the definition, and it is the reason backwards reasoning is a <i>right</i> fold. Separately, weaken the statement to the single entailment <code>wp c₁ (wp c₂ Q) ⊢ wp (c₁ ;; c₂) Q</code> and you keep only the gluing half; that half is what a verification tool actually needs, since it turns a computed precondition back into a claim about the whole program. The other half is what lets you compute in the first place."
    },
    {
      "t": "ex",
      "id": "m12-3",
      "name": "wp_mono",
      "hard": false,
      "why": "Monotonicity is what makes <code>wp</code> usable inside a bigger calculation: it lets you improve the postcondition of an <i>inner</i> command without touching anything around it. Concretely, it is the step that took the illustration at the top of this chapter from <code>wp c₁ (wp c₂ Q)</code> to <code>wp c₁ (subst y (.var x) Q)</code> — rewriting under a <code>wp</code>. Without it, the equations of m12-1 and m12-2 could only ever be applied at the outermost position, and the calculus would not compose.",
      "setup": "Two lines. The only thing to notice is that <code>h : Q ⊢ Q'</code> is a function of three arguments — <code>Entails</code> unfolds to <code>∀ σ h, Q σ h → Q' σ h</code> — so it is applied, not rewritten with.",
      "goal": "theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q'",
      "hints": [
        "The execution is irrelevant here: the same run witnesses both sides. Only the last component of the triple changes.",
        "Destructure the hypothesis with <code>intro σ hh ⟨s', hex, hq⟩</code>, then rebuild <code>⟨s', hex, ?_⟩</code> and fill the hole by applying <code>h</code>.",
        "<code>h</code> is a term, not a rewrite rule: <code>h s'.store s'.heap hq : Q' s'.store s'.heap</code>. Note that the heap argument is <code>s'.heap</code>, the heap <i>after</i> the run, not the <code>hh</code> you introduced."
      ],
      "sol": "theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q' := by\n  intro σ hh ⟨s', hex, hq⟩\n  exact ⟨s', hex, h s'.store s'.heap hq⟩",
      "expl": "<code>wp c</code> is a monotone assertion transformer. Together with <code>wp_seq</code> this says <code>wp</code> is a monoid homomorphism from programs (under <code>;;</code>) to monotone transformers (under composition) — the algebraic statement of “verification is compositional”.",
      "walk": [
        {
          "tac": "intro σ hh ⟨s', hex, hq⟩",
          "h": "Three <code>intro</code>s again; the heap is called <code>hh</code> here because <code>h</code> is already taken by the entailment hypothesis. The third argument is destructured into witness, derivation, and postcondition proof."
        },
        {
          "tac": "exact ⟨s', hex, h s'.store s'.heap hq⟩",
          "h": "Reuse the same final state and the same derivation — the command has not changed, so nothing about the run has to change. Only the third slot needs work: <code>h</code>, applied at the final store and heap, converts <code>hq : Q s'.store s'.heap</code> into the required <code>Q' s'.store s'.heap</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "wp_mono in two steps",
          "start": "Q Q' : Assertion\nc : Cmd\nh : Q ⊢ Q'\n⊢ wp c Q ⊢ wp c Q'",
          "steps": [
            {
              "tac": "intro σ hh ⟨s', hex, hq⟩",
              "state": "Q Q' : Assertion\nc : Cmd\nh : Q ⊢ Q'\nσ : Store\nhh : Heap\ns' : State\nhex : Exec c { store := σ, heap := hh } s'\nhq : Q s'.store s'.heap\n⊢ wp c Q' σ hh",
              "h": "The goal is still folded — Lean shows <code>wp c Q' σ hh</code> rather than the existential, because <code>intro</code> only unfolded far enough to consume its arguments. It will unfold the rest when <code>exact</code> checks the anonymous constructor against it."
            },
            {
              "tac": "exact ⟨s', hex, h s'.store s'.heap hq⟩",
              "state": "No goals.",
              "h": "Note where the entailment is applied: at <code>s'.store</code> and <code>s'.heap</code>, the state <i>after</i> the run, not at <code>σ</code> and <code>hh</code>. Applying it at <code>σ, hh</code> is the mistake to make once — it typechecks as a function application and then fails to match the goal."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "The same two lines prove far more than they look like. Combine <code>wp_mono</code> with the <code>Iff.rfl</code> from the top of the chapter and you get <code>hoare_consequence</code>'s postcondition half for free: <code>Hoare P c Q</code> is <code>P ⊢ wp c Q</code>, and composing that with <code>wp_mono c hpost : wp c Q ⊢ wp c Q'</code> by <code>entails_trans</code> gives <code>Hoare P c Q'</code>. Weakening the postcondition of a triple <i>is</i> monotonicity of <code>wp</code>."
        },
        {
          "t": "detail",
          "title": "The frame rule, stated for <code>wp</code>",
          "tag": "payoff",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Here is what the <code>Iff.rfl</code> buys you at full strength. The frame rule for <code>wp</code> says you may pull a separate resource <code>R</code> inside a <code>wp</code>. Its <i>triple</i> needs no new proof at all: instantiate <code>hoare_frame</code> from M8 at <code>P := wp c Q</code> and its first hypothesis <code>Hoare (wp c Q) c Q</code> becomes <code>wp c Q ⊢ wp c Q</code>, which is <code>entails_refl</code>."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem wp_frame {Q R : Assertion} {c : Cmd}\n    (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    wp c Q ∗ R ⊢ wp c (Q ∗ R) :=\n  hoare_frame (entails_refl (wp c Q)) hlocal hpres"
            },
            {
              "t": "p",
              "h": "One line, and it is the rule that lets a <code>wp</code>-based tool reason about a small footprint inside a large heap. The reason the line is this short is that <code>wp c Q</code> is by construction the greatest precondition, so “apply the frame rule to the best possible triple” needs no triple to be supplied."
            },
            {
              "t": "p",
              "h": "What is <i>not</i> free is the pair of side conditions. <code>hlocal : HeapLocal c</code> and <code>hpres : Preserves c R</code> survive unchanged into <code>wp_frame</code>'s statement, and they are exactly the M8 obligations: the command must not depend on heap it does not own, and it must not disturb the store <code>R</code> talks about. <code>Iff.rfl</code> removes the <i>triple</i> from the frame rule's hypotheses; it removes nothing about locality. If it did, M8's counterexamples would still be counterexamples and the rule would be unsound."
            }
          ]
        }
      ],
      "pitfall": "Applying <code>h</code> at the wrong state: <code>h σ hh hq</code> instead of <code>h s'.store s'.heap hq</code>. Both are well-typed applications of a three-argument function, so the error surfaces late and confusingly, as a mismatch on the third argument (<code>hq</code> is about <code>s'</code>, not about <code>σ, hh</code>). The rule of thumb: an entailment used inside a <code>wp</code> is always applied at the <i>post</i>-state, because that is where the postcondition lives.",
      "variants": "Try to prove the contravariant version, <code>wp c Q ⊢ wp c Q'</code> from <code>Q' ⊢ Q</code>, and it fails immediately: you would need to turn a proof of <code>Q</code> into a proof of <code>Q'</code> and the arrow points the wrong way. That asymmetry is not an accident — <code>wp c</code> is covariant because <code>Q</code> occurs positively in <code>∃ s', … ∧ Q …</code>. Now compare with the <i>precondition</i>: in <code>Hoare P c Q</code>, <code>P</code> occurs to the left of an implication, so triples are contravariant there. Same rule as function types, same reason, and it is worth checking against <code>hoare_consequence</code> in M6 that the variances agree."
    },
    {
      "t": "sec",
      "s": "Exercises · calculating weakest preconditions"
    },
    {
      "t": "p",
      "h": "Now the interesting part: for the heap commands, <code>wp</code> is not given by a rule, it is <b>computed</b>. And what comes out is exactly the small-footprint precondition, with the irrelevant data existentially quantified."
    },
    {
      "t": "p",
      "h": "That last clause is the whole content of the next two exercises, so it is worth stating sharply before you start. When you write a specification by hand you have to name every value you mention. The program does not: <code>free l</code> discards the contents of the cell without looking at them, and <code>[l] := new</code> overwrites them without looking. So the honest precondition cannot mention those values, and the only way to own a cell without naming its contents is an existential."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>aExists (fun v => l ↦ v)</code>",
          "h": "“I own the cell at <code>l</code>, and I decline to say what is in it.” Defined in M3 as <code>fun σ h => ∃ x, P x σ h</code> — the existential is <i>inside</i> the assertion, quantifying per-state, which is what makes it an assertion rather than a schema."
        },
        {
          "k": "<code>l ↦ v</code> for a fixed <code>v</code>",
          "h": "Strictly stronger. It is a perfectly good precondition for both commands, and it is the one M7 used, and it is not the weakest one. The gap between the two is the subject of m12-5."
        },
        {
          "k": "<code>heap_eq_singleton</code>",
          "h": "The extensionality lemma that turns a pointwise fact about a heap into an equation between heaps. Both exercises need one, because <code>l ↦ v</code> is an <i>equation</i> <code>h = Heap.singleton l v</code>, not a membership statement — exact ownership, as fixed back in M3."
        }
      ]
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Why the proofs get longer here",
      "h": "In m12-1 to m12-3 the postcondition was an opaque <code>Q</code> and there was nothing to compute. Here <code>Q</code> is concrete — <code>emp</code>, or <code>l ↦ new</code> — so after inverting the derivation you are left with a <i>heap equation</i> to solve, and heap equations are proved pointwise: <code>funext x</code>, then <code>by_cases hx : x = l</code>, then the M1 lemmas on each side. The separation-logic content is two lines; the rest is the extensionality argument you have done a dozen times since M1."
    },
    {
      "t": "ex",
      "id": "m12-4",
      "name": "wp_free_emp",
      "hard": true,
      "why": "“What must be true before <code>free l</code> so that afterwards I own nothing?” Answer: I own exactly that cell — and <i>the value does not matter</i>, hence the existential. This is the small-footprint free rule, derived rather than postulated. Compare with M7, where <code>Hoare (l ↦ v) (.free l) emp</code> was <i>stated</i> and then proved; here nobody had to guess the precondition, and the guess M7 made turns out to have been slightly too strong.",
      "setup": "You will need <code>Heap.erase</code> and two of its M1 lemmas, <code>erase_other</code> and <code>erase_singleton</code>, plus <code>singleton_same</code> and <code>singleton_other</code>. The helper lemma <code>heap_eq_singleton</code> is part of the exercise — prove it first, as a standalone theorem.",
      "goal": "theorem wp_free_emp (l : Loc) :\n    wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v)",
      "hints": [
        "Think about what the forward direction actually gives you. Inverting <code>Exec.free</code> yields <code>h l = some v</code> for some <code>v</code>, and the postcondition <code>emp</code> at the final state says <code>Heap.erase h l = Heap.empty</code>. Between them these pin <code>h</code> down completely. Say so as a lemma.",
        "That lemma is: if <code>h l = some v</code> and <code>Heap.erase h l = Heap.empty</code> then <code>h = Heap.singleton l v</code>. Prove it by <code>funext x</code> and <code>by_cases hx : x = l</code>. At <code>x = l</code> the first hypothesis does it; away from <code>l</code> you need the <i>pointwise</i> consequence of the second.",
        "To get the pointwise consequence of an equation between functions, use <code>congrFun</code>: if <code>hrest : Heap.erase h l = Heap.empty</code> then <code>congrFun hrest x : Heap.erase h l x = Heap.empty x</code>. Then <code>erase_other</code> rewrites the left side to <code>h x</code>, and the right side is <code>none</code> definitionally.",
        "With the lemma in hand: forwards, <code>refine ⟨_, heap_eq_singleton hl ?_⟩</code> — the underscore is the value, which is inaccessible after <code>cases</code>, and the remaining hole is exactly the <code>emp</code> hypothesis. Backwards, <code>subst</code> the points-to and hand Lean the erased singleton.",
        "You need one heap lemma first: a heap where <code>l</code> is allocated and erasing <code>l</code> leaves nothing is a singleton. Prove <code>heap_eq_singleton</code>, then the forward direction is immediate."
      ],
      "sol": "theorem heap_eq_singleton {h : Heap} {l : Loc} {v : Val}\n    (hl : h l = some v) (hrest : Heap.erase h l = Heap.empty) :\n    h = Heap.singleton l v := by\n  funext x\n  by_cases hx : x = l\n  · subst hx; rw [hl, singleton_same]\n  · rw [singleton_other l x v hx]\n    have := congrFun hrest x\n    rw [erase_other h l x hx] at this\n    exact this\n\ntheorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by\n  constructor\n  · intro σ h ⟨s', hex, he⟩\n    cases hex with\n    | free hl =>\n        refine ⟨_, heap_eq_singleton hl ?_⟩\n        exact he\n  · intro σ h ⟨v, hp⟩\n    subst hp\n    exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v),\n           erase_singleton l v⟩",
      "expl": "<code>heap_eq_singleton</code> is the mathematical content: <code>funext x</code>, and at <code>x = l</code> use the allocation hypothesis, elsewhere use <code>congrFun hrest x</code> together with <code>erase_other</code> to see that <code>h x = none</code>. It says that “allocated at <code>l</code> and empty after erasing <code>l</code>” characterises singletons — a small extensionality result about our heap representation.",
      "walk": [
        {
          "tac": "funext x",
          "h": "The goal is an equation between two <code>Heap</code>s, i.e. between two functions <code>Loc → Option Val</code>. <code>funext</code> reduces it to the pointwise claim at an arbitrary <code>x</code>. This is the move you have made since M1; it is needed because Lean's equality on functions is not definitionally pointwise."
        },
        {
          "tac": "by_cases hx : x = l",
          "h": "Two goals, tagged <code>case pos</code> (with <code>hx : x = l</code>) and <code>case neg</code> (with <code>hx : ¬x = l</code>). Note the shape Lean chooses for the negative hypothesis: <code>¬x = l</code>, which is the same as <code>x ≠ l</code> but matters when you feed it to a lemma expecting one spelling."
        },
        {
          "tac": "· subst hx; rw [hl, singleton_same]",
          "h": "In the positive case, <code>subst hx</code> eliminates one of the two variables. It eliminates <code>l</code> (replacing it by <code>x</code> everywhere), not the other way round — see the trace. Then <code>rw [hl]</code> turns the left side into <code>some v</code> and <code>rw [singleton_same]</code> turns the right side into <code>some v</code>; <code>rw</code> closes goals that become <code>rfl</code>."
        },
        {
          "tac": "· rw [singleton_other l x v hx]",
          "h": "In the negative case, deal with the right side first: away from <code>l</code>, a singleton is <code>none</code>. The goal becomes <code>h x = none</code>. Notice that <code>singleton_other</code> wants exactly <code>x ≠ l</code> in that order, and <code>hx</code> has that order — this is not an accident, the lemma was stated in M1 to match this use."
        },
        {
          "tac": "have := congrFun hrest x",
          "h": "<code>hrest</code> is an equation between two functions; <code>congrFun</code> applies both sides to <code>x</code>. This is the exact converse of <code>funext</code>, and it is the standard way to use a function equation you were <i>given</i> rather than one you must prove. The anonymous <code>have :=</code> names the result <code>this</code>."
        },
        {
          "tac": "rw [erase_other h l x hx] at this",
          "h": "Rewrite <i>in a hypothesis</i> rather than the goal. <code>erase_other</code> says that away from <code>l</code>, erasing changes nothing, so <code>this</code> becomes <code>h x = Heap.empty x</code>."
        },
        {
          "tac": "exact this",
          "h": "The goal is <code>h x = none</code> and <code>this</code> is <code>h x = Heap.empty x</code>. These are accepted as the same because <code>Heap.empty</code> is <code>fun _ => none</code>, so <code>Heap.empty x</code> beta-reduces to <code>none</code>. No rewrite needed; <code>exact</code> checks up to definitional equality."
        },
        {
          "tac": "theorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by",
          "h": "Now the theorem itself. Everything hard is already done."
        },
        {
          "tac": "constructor",
          "h": "Two entailments, as usual."
        },
        {
          "tac": "· intro σ h ⟨s', hex, he⟩",
          "h": "<code>he</code> is the <code>emp</code> at the final state — the postcondition — and <code>hex</code> is the run of <code>free l</code>."
        },
        {
          "tac": "cases hex with",
          "h": "Invert."
        },
        {
          "tac": "| free hl =>",
          "h": "One branch. <code>hl</code> is the side condition of the constructor, <code>s.heap l = some v</code> for a value <code>v</code> that Lean names <code>v✝</code> — inaccessible, because <code>Exec.free</code>'s <code>{v}</code> binder is implicit and we named only the explicit argument."
        },
        {
          "tac": "refine ⟨_, heap_eq_singleton hl ?_⟩",
          "h": "The goal <code>aExists (fun v => l ↦ v) σ h</code> is <code>∃ v, h = Heap.singleton l v</code>. Supply the witness as <code>_</code> — you cannot type <code>v✝</code>, and unification will read the witness off <code>hl</code> anyway. The proof component is <code>heap_eq_singleton</code> applied to <code>hl</code>, with its second argument deferred as <code>?_</code>. <code>refine</code> is <code>exact</code> that tolerates holes."
        },
        {
          "tac": "exact he",
          "h": "The hole has type <code>Heap.erase h l = Heap.empty</code>, and <code>he : emp …</code> is that, once <code>emp</code> is unfolded and the state projections reduced. Definitional equality again — the displayed types do not look alike at all."
        },
        {
          "tac": "· intro σ h ⟨v, hp⟩",
          "h": "The backward direction. <code>hp</code> is a proof of <code>(fun v => l ↦ v) v σ h</code>, which after beta and unfolding <code>pointsTo</code> is the equation <code>h = Heap.singleton l v</code>."
        },
        {
          "tac": "subst hp",
          "h": "Since <code>hp</code> is (definitionally) an equation whose left side is the local variable <code>h</code>, <code>subst</code> eliminates <code>h</code>, replacing it by <code>Heap.singleton l v</code> throughout. That <code>subst</code> sees through the beta-redex and the <code>pointsTo</code> definition is worth noticing; it whnf's the hypothesis before deciding."
        },
        {
          "tac": "exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v), erase_singleton l v⟩",
          "h": "Three components again. The final state is the singleton with <code>l</code> erased; the derivation is <code>Exec.free</code>, whose side condition <code>Heap.singleton l v l = some v</code> is <code>singleton_same</code>; and the postcondition <code>emp</code> at that state is <code>erase_singleton</code>, which says erasing the only cell of a singleton gives the empty heap."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "heap_eq_singleton, tactic by tactic",
          "start": "h : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\n⊢ h = Heap.singleton l v",
          "steps": [
            {
              "tac": "funext x",
              "state": "h : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\n⊢ h x = Heap.singleton l v x",
              "h": "Both sides are now applied to <code>x</code>. Note the printed form of <code>hrest</code>: <code>h.erase l</code>, not <code>Heap.erase h l</code> — Lean prefers generalised field notation in output. Same term."
            },
            {
              "tac": "by_cases hx : x = l",
              "state": "case pos\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : x = l\n⊢ h x = Heap.singleton l v x",
              "h": "The first of two goals. <code>case pos</code> carries <code>hx : x = l</code>; <code>case neg</code> below carries <code>hx : ¬x = l</code>. <code>by_cases</code> needs the proposition to be decidable, which <code>x = l</code> is because <code>Loc = Nat</code>."
            },
            {
              "tac": "subst hx",
              "state": "case pos\nh : Heap\nv : Val\nx : Loc\nhl : h x = some v\nhrest : h.erase x = Heap.empty\n⊢ h x = Heap.singleton x v x",
              "h": "Read this carefully: <code>l</code> has <b>disappeared</b> and <code>x</code> is everywhere. Given <code>hx : x = l</code> with both sides local variables, <code>subst</code> may eliminate either; here it eliminated <code>l</code>. If you had written the proof expecting to see <code>l</code>, every subsequent lemma reference would be against the wrong name. The following <code>rw [hl, singleton_same]</code> works precisely because <code>hl</code> is now stated at <code>x</code>."
            },
            {
              "tac": "rw [hl, singleton_same]",
              "state": "No goals.",
              "h": "<code>rw [hl]</code> makes the left side <code>some v</code>; <code>rw [singleton_same]</code> makes the right side <code>some v</code>; <code>rw</code> then tries <code>rfl</code> and succeeds. Two rewrites in one bracket are applied left to right."
            },
            {
              "tac": "(second branch) rw [singleton_other l x v hx]",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : ¬x = l\n⊢ h x = none",
              "h": "The right-hand side is gone. Everything that remains is: show <code>h</code> is empty away from <code>l</code>. That is what <code>hrest</code> says, but <code>hrest</code> is an equation between <i>functions</i>, and the goal is about a <i>value</i>."
            },
            {
              "tac": "have := congrFun hrest x",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : ¬x = l\nthis : h.erase l x = Heap.empty x\n⊢ h x = none",
              "h": "<code>congrFun : f = g → ∀ a, f a = g a</code>. This is the exact inverse of <code>funext</code>, and the pairing is worth memorising: <b><code>funext</code> to prove a function equation, <code>congrFun</code> to use one.</b>"
            },
            {
              "tac": "rw [erase_other h l x hx] at this",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : ¬x = l\nthis : h x = Heap.empty x\n⊢ h x = none",
              "h": "The <code>at this</code> suffix rewrites in the hypothesis instead of the goal. All four explicit arguments of <code>erase_other</code> are supplied because <code>rw</code> matches syntactically and we want no ambiguity about which <code>erase</code> is being rewritten."
            },
            {
              "tac": "exact this",
              "state": "No goals.",
              "h": "<code>Heap.empty x</code> is <code>(fun _ => none) x</code>, which beta-reduces to <code>none</code>. So <code>this</code> and the goal are the same proposition and <code>exact</code> accepts. You could also write <code>exact this</code> as <code>simpa [Heap.empty] using this</code>, but there is nothing to simplify — only to reduce."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "wp_free_emp, forwards and backwards",
          "start": "case left\nl : Loc\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.free l) { store := σ, heap := h } s'\nhe : emp s'.store s'.heap\n⊢ aExists (fun v => l ↦ v) σ h",
          "steps": [
            {
              "tac": "cases hex with | free hl =>",
              "state": "case left.free\nl : Loc\nσ : Store\nh : Heap\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhe :\n  emp { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap\n⊢ aExists (fun v => l ↦ v) σ h",
              "h": "Two inaccessible things at once. <code>v✝</code> is the value that was stored — implicit in <code>Exec.free</code>, hence unnameable, hence the <code>_</code> in the next line. And <code>hl</code>'s type is printed as <code>{ store := σ, heap := h }.heap l = some v✝</code>, unreduced, even though <code>heap_eq_singleton</code> wants <code>h l = some v✝</code>. It is accepted anyway: <code>heap_eq_singleton hl</code> elaborates because the projection reduces."
            },
            {
              "tac": "refine ⟨_, heap_eq_singleton hl ?_⟩",
              "state": "case left.free\nl : Loc\nσ : Store\nh : Heap\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhe :\n  emp { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap\n⊢ h.erase l = Heap.empty",
              "h": "The goal that is left is the <code>hrest</code> argument of <code>heap_eq_singleton</code>, and Lean has <b>reduced it for us</b>: <code>h.erase l = Heap.empty</code>. Meanwhile <code>he</code> is still displayed in its unreduced glory. They are the same proposition; unfolding <code>emp</code> gives <code>(state).heap = Heap.empty</code>, and that state's heap is <code>h.erase l</code>."
            },
            {
              "tac": "exact he",
              "state": "No goals.",
              "h": "One more instance of the theme of this chapter: a hypothesis whose display shares no visible structure with the goal closes it exactly."
            },
            {
              "tac": "intro σ h ⟨v, hp⟩",
              "state": "case right\nl : Loc\nσ : Store\nh : Heap\nv : Val\nhp : (fun v => l ↦ v) v σ h\n⊢ wp (Cmd.free l) emp σ h",
              "h": "The backward direction. <code>hp</code> is displayed as an unapplied beta-redex — Lean does not beta-reduce hypothesis types for display. Under it is the equation <code>h = Heap.singleton l v</code>."
            },
            {
              "tac": "subst hp",
              "state": "case right\nl : Loc\nσ : Store\nv : Val\n⊢ wp (Cmd.free l) emp σ (Heap.singleton l v)",
              "h": "<code>h</code> is gone from the context; every occurrence became <code>Heap.singleton l v</code>. <code>subst</code> found the equation despite the beta-redex and the <code>pointsTo</code> definition, because it reduces to weak head normal form before looking. Now the goal is completely concrete and can be discharged by supplying a run."
            },
            {
              "tac": "exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v), erase_singleton l v⟩",
              "state": "No goals.",
              "h": "Every component is forced: the state after freeing, the constructor with its side condition, and the <code>emp</code>. There is no choice to make anywhere, which is the sign that you have the right lemmas."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "Why the existential has to be there",
          "items": [
            {
              "k": "Start from the definition",
              "h": "<code>wp (.free l) emp σ h</code> holds iff there is a run of <code>free l</code> from <code>⟨σ,h⟩</code> ending in a state with empty heap."
            },
            {
              "k": "Unfold what a run requires",
              "h": "<code>Exec.free</code> requires <code>h l = some v</code> for <i>some</i> <code>v</code> — the constructor quantifies over it implicitly. Nothing constrains which."
            },
            {
              "k": "Unfold what the postcondition requires",
              "h": "<code>Heap.erase h l = Heap.empty</code>. Combined with the previous point, <code>heap_eq_singleton</code> says <code>h = Heap.singleton l v</code>."
            },
            {
              "k": "Collect",
              "h": "So the precondition is <code>∃ v, h = Heap.singleton l v</code> — the existential is inherited directly from the implicit argument of the constructor. It is not a stylistic choice; it is where the value went."
            }
          ]
        },
        {
          "t": "detail",
          "title": "The general <code>wp</code> of <code>free</code>, with an arbitrary postcondition",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "<code>wp_free_emp</code> is the case <code>Q := emp</code> of a general equation, and it is instructive to see that the general one is <i>shorter</i>: all the heap-extensionality work in <code>heap_eq_singleton</code> exists only to convert the general answer into the points-to language."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem wp_free (l : Loc) (Q : Assertion) :\n    wp (.free l) Q ⊣⊢\n      aExists (fun v => aAnd (fun _ h => h l = some v)\n                             (fun σ h => Q σ (Heap.erase h l))) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | free hl => rename_i v; exact ⟨v, hl, hq⟩\n  · intro σ h ⟨v, hl, hq⟩\n    exact ⟨⟨σ, Heap.erase h l⟩, Exec.free hl, hq⟩"
            },
            {
              "t": "p",
              "h": "Six tactic lines against seventeen. The lesson is not that the exercise is badly chosen — it is that <i>stating</i> a weakest precondition in the separation-logic vocabulary (points-to, <code>emp</code>, <code>∗</code>) is real work, over and above computing it. That translation step is where a tool like Iris spends most of its effort."
            }
          ]
        }
      ],
      "pitfall": "In <code>heap_eq_singleton</code>, reaching for <code>rw [hrest]</code> instead of <code>congrFun hrest x</code>. After <code>funext x</code> the goal contains <code>h x</code>, not <code>Heap.erase h l</code>, so there is nothing for <code>rw [hrest]</code> to match and it fails with “did not find an occurrence of the pattern”. The general rule: once you have gone pointwise, function-level equations must be brought pointwise too, and <code>congrFun</code> is the tool. The second trap is in the positive branch — after <code>subst hx</code> the variable that survives is <code>x</code>, not <code>l</code>, so a proof written as <code>rw [singleton_same l v]</code> with an explicit <code>l</code> will fail with an unknown identifier.",
      "variants": "Drop <code>hrest</code> from <code>heap_eq_singleton</code> and the theorem is plainly false: <code>h</code> could have a cell at some other location, and singletons are <i>exact</i> ownership (M3), not “at least this”. Drop <code>hl</code> instead and it is still false, but only at one point — <code>h</code> could be the empty heap, which satisfies <code>Heap.erase h l = Heap.empty</code> and is not any singleton. That single missing point is precisely the safety content of the free rule: without <code>hl</code> you have not established that the cell was allocated, and <code>free</code> on an unallocated cell has no <code>Exec</code> derivation at all. Now try replacing the postcondition <code>emp</code> by <code>aTrue</code>: the forward direction collapses, because <code>Heap.erase h l = Heap.empty</code> is no longer available and all you can conclude is <code>∃ v, h l = some v</code> — ownership of a cell inside a possibly-larger heap, which is not expressible with <code>↦</code> alone. That is exactly why the exercise fixes <code>Q := emp</code>."
    },
    {
      "t": "ex",
      "id": "m12-5",
      "name": "wp_write",
      "hard": true,
      "why": "Same pattern: you must own the cell, its previous contents are irrelevant. Compare with the manually-written precondition <code>l ↦ old</code> for a fixed <code>old</code> — that one is <i>sufficient</i> but not <i>weakest</i>, because it pins down a value it does not need. This is the exercise where the difference between “a specification that works” and “the specification” stops being a slogan.",
      "setup": "Same toolkit as m12-4, with <code>Heap.write</code> in place of <code>Heap.erase</code>: <code>write_other</code>, <code>write_singleton</code>, <code>singleton_same</code>, <code>singleton_other</code>. The command is <code>.write l (.const new)</code> — a literal constant, so that <code>e.eval σ</code> is <code>new</code> regardless of the store and the exercise is about the heap only.",
      "goal": "theorem wp_write (l : Loc) (new : Val) :\n    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old)",
      "hints": [
        "The forward direction is the same argument as m12-4 with a different final heap: you learn <code>h l = some old</code> from the derivation and <code>Heap.write h l new = Heap.singleton l new</code> from the postcondition, and you must conclude <code>h = Heap.singleton l old</code>.",
        "You cannot reuse <code>heap_eq_singleton</code> here — its second hypothesis is about <code>erase</code>. Do the <code>funext</code> / <code>by_cases</code> argument inline. Away from <code>l</code>, both <code>write_other</code> and <code>singleton_other</code> deliver <code>none</code>, which is what makes the negative branch close.",
        "Before you can <code>rw</code> with the hypotheses that came out of <code>cases</code>, restate them. <code>hl</code> is displayed as <code>{ store := σ, heap := h }.heap l = some old</code>, and <code>rw</code> matches syntactically, so it will not fire. Write <code>have hl' : h l = some old := hl</code> — a type ascription that costs nothing and is accepted by definitional equality.",
        "The value <code>old</code> is an inaccessible <code>old✝</code> after <code>cases hex with | write hl =&gt;</code>, and you need to <i>name</i> it because it appears in the existential you are building. <code>rename_i old</code> renames the most recent inaccessible hypothesis.",
        "Forwards: from <code>Heap.write h l new = Heap.singleton l new</code> and <code>h l = some old</code>, show <code>h = Heap.singleton l old</code> by <code>funext</code>; away from <code>l</code>, <code>write_other</code> and <code>singleton_other</code> both give <code>none</code>."
      ],
      "sol": "theorem wp_write (l : Loc) (new : Val) :\n    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | write hl =>\n        rename_i old\n        refine ⟨old, ?_⟩\n        have hl' : h l = some old := hl\n        have hq' : Heap.write h l new = Heap.singleton l new := hq\n        funext x\n        by_cases hx : x = l\n        · subst hx; rw [hl', singleton_same]\n        · rw [singleton_other l x old hx]\n          have := congrFun hq' x\n          rw [write_other h l x new hx, singleton_other l x new hx] at this\n          exact this\n  · intro σ h ⟨old, hp⟩\n    subst hp\n    exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩,\n           Exec.write (singleton_same l old), write_singleton l old new⟩",
      "expl": "This is the exercise that teaches the difference between a specification you wrote and the specification the program deserves. Ask the same question of <code>copyCell</code>: is <code>src ↦ a ∗ dst ↦ b</code> weakest? It is not — the value <code>b</code> is never read, so the weakest precondition existentially quantifies it. Pinning down irrelevant values is the most common way a hand-written specification is stronger than it needs to be, and it is exactly what makes it fail to compose later.",
      "walk": [
        {
          "tac": "constructor",
          "h": "Two entailments."
        },
        {
          "tac": "· intro σ h ⟨s', hex, hq⟩",
          "h": "Forwards. <code>hq</code> is the postcondition <code>l ↦ new</code> at the final state — that is, an equation saying the post-heap is exactly <code>Heap.singleton l new</code>."
        },
        {
          "tac": "cases hex with",
          "h": "Invert the run."
        },
        {
          "tac": "| write hl =>",
          "h": "<code>Exec.write</code>'s side condition <code>hl : s.heap l = some old</code> for an implicit <code>old</code>."
        },
        {
          "tac": "rename_i old",
          "h": "That implicit value arrived as <code>old✝</code>, which you cannot type. <code>rename_i old</code> renames the most recently introduced inaccessible variable, giving it a usable name. This is needed here (unlike in m12-4, where <code>_</code> sufficed) because the value is not determined by unification against the goal — it is the thing you are choosing to witness the existential."
        },
        {
          "tac": "refine ⟨old, ?_⟩",
          "h": "Commit to <code>old</code> as the witness. The remaining goal is <code>(fun old => l ↦ old) old σ h</code>, i.e. <code>h = Heap.singleton l old</code>."
        },
        {
          "tac": "have hl' : h l = some old := hl",
          "h": "A pure restatement. <code>hl</code>'s displayed type is <code>{ store := σ, heap := h }.heap l = some old</code>; the ascription forces the reduced form. Nothing is proved here — but <code>rw</code> works on syntax, so this line is what makes the rest of the proof possible."
        },
        {
          "tac": "have hq' : Heap.write h l new = Heap.singleton l new := hq",
          "h": "The same trick on the postcondition, and it does more work: it unfolds <code>pointsTo</code>, reduces the state projections, and evaluates <code>(Atom.const new).eval σ</code> to <code>new</code>, all by definitional equality, all invisibly. Compare the displayed type of <code>hq</code> in the trace — it is six lines long."
        },
        {
          "tac": "funext x",
          "h": "Now the goal is a heap equation, so go pointwise."
        },
        {
          "tac": "by_cases hx : x = l",
          "h": "Split at the written location."
        },
        {
          "tac": "· subst hx; rw [hl', singleton_same]",
          "h": "At <code>x = l</code>: after <code>subst</code>, <code>hl'</code> says <code>h x = some old</code> and <code>singleton_same</code> says the singleton at <code>x</code> is <code>some old</code>. Note this branch never mentions <code>new</code> — what was written is irrelevant to what was there before."
        },
        {
          "tac": "· rw [singleton_other l x old hx]",
          "h": "Away from <code>l</code>: the right side is <code>none</code>, so the goal becomes <code>h x = none</code>."
        },
        {
          "tac": "have := congrFun hq' x",
          "h": "Bring the post-heap equation pointwise: <code>Heap.write h l new x = Heap.singleton l new x</code>. This is where <code>hq'</code> rather than <code>hq</code> matters — <code>congrFun hq x</code> also elaborates, but produces the unreduced form, which the next rewrite cannot match."
        },
        {
          "tac": "rw [write_other h l x new hx, singleton_other l x new hx] at this",
          "h": "Two rewrites in the hypothesis. Left side: away from <code>l</code>, writing changed nothing, so it is <code>h x</code>. Right side: away from <code>l</code>, the singleton is <code>none</code>. <code>this</code> becomes <code>h x = none</code>."
        },
        {
          "tac": "exact this",
          "h": "Exactly the goal. The negative branch is the whole non-aliasing content of the proof: the only reason the untouched part of <code>h</code> is empty is that the post-heap was a singleton and writing did not create anything elsewhere."
        },
        {
          "tac": "· intro σ h ⟨old, hp⟩",
          "h": "The backward direction. <code>old</code> is now an ordinary named variable, because it came from the existential in the hypothesis rather than from a constructor."
        },
        {
          "tac": "subst hp",
          "h": "Replace <code>h</code> by <code>Heap.singleton l old</code> everywhere. The goal becomes fully concrete."
        },
        {
          "tac": "exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩, Exec.write (singleton_same l old), write_singleton l old new⟩",
          "h": "The final state, the derivation with its side condition, and the postcondition. <code>write_singleton l old new : Heap.write (Heap.singleton l old) l new = Heap.singleton l new</code> is exactly <code>l ↦ new</code> at that heap — the M1 lemma is doing the separation-logic work."
        }
      ],
      "deep": [
        {
          "t": "note",
          "kind": "info",
          "title": "How to read the trace below",
          "h": "Two hypotheses in this proof, <code>hl</code> and <code>hq</code>, arrive unreduced from <code>cases</code> and then sit there untouched for the rest of the proof — twelve lines of context that never change. They are printed in full once, in the first step, because that display <i>is</i> the point of the exercise. After that they are abbreviated <code>hl : ⋯</code> and <code>hq : ⋯</code>. Everything else in every state below is Lean's own output, unedited."
        },
        {
          "t": "trace",
          "title": "wp_write, forwards — and why the two <code>have</code>s exist",
          "start": "case left\nl : Loc\nnew : Val\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.write l (Atom.const new)) { store := σ, heap := h } s'\nhq : (l ↦ new) s'.store s'.heap\n⊢ aExists (fun old => l ↦ old) σ h",
          "steps": [
            {
              "tac": "cases hex with | write hl =>",
              "state": "case left.write\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhq :\n  (l ↦ new)\n    { store := { store := σ, heap := h }.store,\n        heap :=\n          { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store (Atom.const new)) }.store\n    { store := { store := σ, heap := h }.store,\n        heap :=\n          { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store (Atom.const new)) }.heap\n⊢ aExists (fun old => l ↦ old) σ h",
              "h": "This is the goal state that justifies the rest of the proof. <code>hq</code> is a six-line term in which nothing has been reduced: the state is a literal, its projections are unevaluated, and <code>Atom.eval … (Atom.const new)</code> has not been computed to <code>new</code>. Lean is perfectly happy to <i>use</i> this hypothesis; it is <code>rw</code> that will not, because <code>rw</code> matches syntax."
            },
            {
              "tac": "rename_i old",
              "h": "Renames <code>old✝</code> to <code>old</code>. The rest of the state is unchanged. Without this you cannot write the witness in the next line, and unification cannot supply it either, because the goal <code>aExists (fun old => l ↦ old) σ h</code> gives no clue what the value should be until the equation is proved."
            },
            {
              "tac": "refine ⟨old, ?_⟩",
              "h": "The goal becomes <code>(fun old => l ↦ old) old σ h</code> — the beta-redex is left unreduced in the display, as always. Underneath, it is <code>h = Heap.singleton l old</code>."
            },
            {
              "tac": "have hl' : h l = some old := hl",
              "h": "A restatement of <code>hl</code> at the type you wish it had. Nothing is proved: the elaborator checks the old proof against the new type, and definitional equality does the reducing. What lands in the context is <code>hl' : h l = some old</code>, in a shape <code>rw</code> can match."
            },
            {
              "tac": "have hq' : Heap.write h l new = Heap.singleton l new := hq",
              "state": "case left.write\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\n⊢ (fun old => l ↦ old) old σ h",
              "h": "The same trick on the postcondition, doing far more work: the ascription forces Lean to unfold <code>pointsTo</code>, reduce the state projections, and evaluate <code>Atom.eval σ (Atom.const new)</code> to <code>new</code>. All of that happens during the definitional-equality check and none of it is reported. (From here on <code>hl</code> and <code>hq</code> are still in the context, printing exactly as they did two steps ago; <code>⋯</code> stands for those twelve unchanged lines.)"
            },
            {
              "tac": "funext x  ·  by_cases hx : x = l  ·  (negative branch)",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\n⊢ h x = Heap.singleton l old x",
              "h": "The familiar pointwise split. The positive branch is two rewrites and closes immediately; the negative branch is where the content is."
            },
            {
              "tac": "rw [singleton_other l x old hx]",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\n⊢ h x = none",
              "h": "Right-hand side dispatched."
            },
            {
              "tac": "have := congrFun hq' x",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\nthis : h.write l new x = Heap.singleton l new x\n⊢ h x = none",
              "h": "Pointwise version of the post-heap equation. Compare with what <code>congrFun hq x</code> would have given: <code>{ store := …, heap := … }.heap x = Heap.singleton l new x</code>, with the whole unreduced state still in the way."
            },
            {
              "tac": "rw [write_other h l x new hx, singleton_other l x new hx] at this",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\nthis : h x = none\n⊢ h x = none",
              "h": "Both sides simplified away from <code>l</code>. <code>exact this</code> finishes."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "Without the restatements",
            "kind": "bad",
            "h": "Use <code>hl</code> and <code>hq</code> directly and both rewrites fail, with error messages that name a pattern you never wrote. This is the single most common way to get stuck in this exercise, and it is not a mathematical difficulty at all.",
            "tag": "sketch",
            "src": "· subst hx; rw [hl, singleton_same]\n-- error: Tactic `rewrite` failed:\n--   Did not find an occurrence of the pattern\n--     { store := σ, heap := h }.heap x\n--   in the target expression\n--     h x = Heap.singleton x old x\n\n  have := congrFun hq x\n  rw [write_other h l x new hx, …] at this\n-- error: Tactic `rewrite` failed:\n--   Did not find an occurrence of the pattern\n--     h.write l new x"
          },
          "right": {
            "t": "With them",
            "kind": "good",
            "h": "Two lines that prove nothing and enable everything. Read them as “re-elaborate this hypothesis at the type I actually want”; the definitional-equality check does the reduction, and what lands in the context is syntactically usable.",
            "tag": "sketch",
            "src": "have hl' : h l = some old := hl\nhave hq' : Heap.write h l new\n             = Heap.singleton l new := hq"
          }
        },
        {
          "t": "steps",
          "title": "Is <code>l ↦ old</code> weakest? No — and here is the witness",
          "items": [
            {
              "k": "It is sufficient",
              "h": "For any fixed <code>old</code>, <code>l ↦ old</code> entails the computed precondition, by supplying <code>old</code> as the witness. So the M7 rule is sound; nothing is wrong with it."
            },
            {
              "k": "It is not necessary",
              "h": "Take <code>old := 0</code>. The heap <code>Heap.singleton l 1</code> satisfies the weakest precondition — the write succeeds and lands in <code>l ↦ new</code> — and does not satisfy <code>l ↦ 0</code>. One heap is all it takes."
            },
            {
              "k": "In Lean",
              "h": [
                {
                  "t": "code",
                  "tag": "illustration",
                  "src": "-- sufficient: any fixed `old` entails the weakest precondition\nexample (l : Loc) (old new : Val) :\n    (l ↦ old) ⊢ wp (.write l (.const new)) (l ↦ new) :=\n  fun σ h hp => (wp_write l new).2 σ h ⟨old, hp⟩\n\n-- but not necessary: `l ↦ 0` is strictly stronger\nexample (l : Loc) (new : Val) :\n    ¬ (wp (.write l (.const new)) (l ↦ new) ⊢ (l ↦ 0)) := by\n  intro hcontra\n  have h1 : (l ↦ 1) ⊢ wp (.write l (.const new)) (l ↦ new) :=\n    fun σ hh hp => (wp_write l new).2 σ hh ⟨1, hp⟩\n  have h2 := hcontra (fun _ => 0) (Heap.singleton l 1)\n    (h1 (fun _ => 0) (Heap.singleton l 1) rfl)\n  have heq : Heap.singleton l 1 l = Heap.singleton l 0 l := by rw [h2]\n  rw [singleton_same, singleton_same] at heq\n  exact absurd (Option.some.inj heq) (by simp)"
                },
                {
                  "t": "p",
                  "h": "Four moves in that second block are worth naming, because none of them is separation logic. <code>fun σ h hp => …</code> is an entailment given as a term rather than by <code>intro</code>: <code>Entails P Q</code> is <code>∀ σ h, P σ h → Q σ h</code>, so a lambda in three arguments <i>is</i> a proof of it. <code>(fun _ => 0)</code> is a store — any store; the write does not read one, and the counterexample needs a concrete state, so pick the constant-zero store. The <code>rfl</code> at the end of the <code>h1</code> application proves <code>(l ↦ 1) (fun _ => 0) (Heap.singleton l 1)</code>, which unfolds to <code>Heap.singleton l 1 = Heap.singleton l 1</code> — <code>pointsTo</code> is an equation, so exhibiting the heap <i>is</i> the proof. And <code>Option.some.inj : some a = some b → a = b</code> is the injectivity lemma Lean generates for every constructor; it turns <code>some 1 = some 0</code> into <code>1 = 0</code>, which <code>simp</code> refutes."
                }
              ]
            },
            {
              "k": "Why it matters downstream",
              "h": "A precondition that names a value it never uses does not compose. If a caller owns <code>l ↦ 7</code> and your specification says <code>l ↦ 0</code>, the caller must first prove <code>7 = 0</code> or rewrite the specification. Existentially quantifying the unread value is what makes the rule apply on the first attempt every time."
            }
          ]
        },
        {
          "t": "note",
          "kind": "tip",
          "title": "A test you can apply to any specification you write",
          "h": "For each value named in the precondition, ask: does the program <i>read</i> it? If not, it should be existentially quantified. Run this on <code>copyCell_spec</code> from M9 — precondition <code>src ↦ a ∗ dst ↦ b</code> — and <code>b</code> fails the test at once: <code>copyCell</code> writes to <code>dst</code> without ever loading from it. The weakest precondition is <code>src ↦ a ∗ (∃ b, dst ↦ b)</code>."
        }
      ],
      "pitfall": "Skipping <code>have hq' : … := hq</code> and calling <code>congrFun hq x</code> directly. It elaborates — <code>congrFun</code> looks through the definitions to find the equation — but the hypothesis it produces still carries the unreduced state, so the very next line fails with <code>Did not find an occurrence of the pattern h.write l new x</code>. The confusing part is that the error names a pattern that <i>is</i> the term you are looking at, semantically. The rule to internalise: <code>exact</code>, <code>apply</code> and <code>refine</code> work up to definitional equality; <code>rw</code>, <code>simp only</code> and <code>congrFun</code>'s output do not. When a hypothesis comes out of <code>cases</code> and you intend to rewrite with it, restate it first. The mirror-image mistake is in the positive branch: <code>subst hx</code> eliminates <code>l</code> and keeps <code>x</code>, so after it the identifier <code>l</code> no longer exists. <code>rw [hl']</code> works; anything you write that still names <code>l</code> — <code>rw [singleton_same l old]</code>, say — fails with <code>Unknown identifier `l`</code>. That is why the solution's positive branch is <code>rw [hl', singleton_same]</code> with no explicit arguments at all.",
      "variants": "Replace the postcondition <code>l ↦ new</code> by <code>aTrue</code> and the equation becomes false in the forward direction: from a successful write you can only conclude <code>∃ old, h l = some old</code>, which does not pin <code>h</code> down to a singleton — the heap may contain anything else. Replace it by <code>(l ↦ new) ∗ R</code> for a fixed <code>R</code> and you get the framed version, which is <code>wp_frame</code> plus this exercise rather than a new proof. Now go the other way and <i>strengthen</i> the right-hand side to <code>l ↦ old</code> for a fixed <code>old</code>: the ⟸ direction still holds (that is the sufficiency above) but ⟹ fails, and the failing point is the single heap <code>Heap.singleton l v</code> for any <code>v ≠ old</code>. Finally, change the command's argument from <code>.const new</code> to <code>.var y</code>: the forward direction now has <code>Atom.eval σ (.var y)</code> where it had <code>new</code>, the restatement <code>have hq'</code> no longer reduces to a constant, and you need a pure side condition <code>σ y = new</code> — which is exactly why M9 introduced <code>hoare_write_val</code>."
    },
    {
      "t": "sec",
      "s": "What the calculus buys, and where it stops"
    },
    {
      "t": "p",
      "h": "Three things follow immediately from what you have just proved, and none of them needs a new idea."
    },
    {
      "t": "ul",
      "items": [
        "<b>Every triple is an entailment.</b> <code>hoare_iff_entails_wp</code> is <code>Iff.rfl</code>, so a verification is: compute <code>wp c Q</code> by folding the equations from the end of the program, then discharge one entailment <code>P ⊢ (the computed thing)</code>. The program has disappeared from the second half.",
        "<b>The frame rule needs no triple.</b> <code>wp c Q ∗ R ⊢ wp c (Q ∗ R)</code> is <code>hoare_frame</code> instantiated at the best possible triple, and that triple's proof is <code>entails_refl</code>. The M8 side conditions <code>HeapLocal c</code> and <code>Preserves c R</code> are still required, and still carry all the content. See the aside in m12-3.",
        "<b>Weakest means weakest.</b> If you can prove <code>Hoare P c Q</code> at all, then <code>P ⊢ wp c Q</code> — with no proof, because they are the same statement. So <code>wp c Q</code> really is the greatest precondition, and “is my specification the honest one?” becomes a checkable entailment rather than a matter of taste."
      ]
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "Where the equations run out",
      "h": "There is no equation for <code>loop</code>. <code>wp (.loop b c) Q</code> is a fixed point — the <b>least</b> <code>X</code> with <code>X ⊣⊢ (b ∧ wp c X) ∨ (¬b ∧ Q)</code> — and a fixed point is not something you can fold over the syntax of a program. That is why M13 goes back to <i>supplying</i> an invariant rather than computing one, and why the invariant is the one part of a verification that no tool can infer for you in general. Everything else in this chapter is mechanical; that one thing is where the mathematics is."
    },
    {
      "t": "detail",
      "title": "Least, not greatest — and the loop that shows the difference",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "Which fixed point is not a matter of taste, and it is easy to get backwards. <code>Exec</code> is an <code>inductive</code> relation, so a run is a <i>finite</i> derivation tree, and <code>wp</code>'s <code>∃ s', Exec c ⟨σ,h⟩ s' ∧ …</code> therefore asserts termination. That forces the <b>least</b> fixed point. The greatest one is what you get for <i>partial</i> correctness — <code>PartialHoare</code>, where a non-terminating run satisfies everything vacuously — and it is traditionally written <code>wlp</code>."
        },
        {
          "t": "p",
          "h": "The two differ, and the smallest witness is M6's <code>forever</code>: a loop whose guard is <code>0 = 0</code> and whose body is <code>skip</code>. Its loop equation degenerates to <code>X ⊣⊢ X</code>, which <i>every</i> assertion solves. <code>wp forever Q</code> is the smallest solution, <code>aFalse</code> — no state at all, because no run of <code>forever</code> terminates. The greatest solution is <code>aTrue</code>, and it would certify a program that never returns."
        },
        {
          "t": "code",
          "tag": "illustration",
          "cap": "compiles against the M12 prelude; forever and no_exec_forever are M6's, repeated so the snippet stands alone",
          "src": "def forever : Cmd := .loop (.equals (.const 0) (.const 0)) .skip\n\ntheorem no_exec_forever : ∀ {c : Cmd} {s s' : State}, c = forever → Exec c s s' → False := by\n  intro c s s' hc hex\n  induction hex with\n  | loopFalse hb => cases hc; simp [BExpr.eval, Atom.eval] at hb\n  | loopTrue hb hbody hrest ihb ihr => exact ihr hc\n  | _ => cases hc\n\n-- the loop equation for `forever`, with X the unknown assertion\ndef loopEqn (Q X : Assertion) : Assertion :=\n  aOr (aAnd (fact (fun σ => BExpr.eval σ (.equals (.const 0) (.const 0)) = true))  (wp .skip X))\n      (aAnd (fact (fun σ => BExpr.eval σ (.equals (.const 0) (.const 0)) = false)) Q)\n\n-- `wp forever Q` is `aFalse`: no run terminates, so nothing satisfies it.\ntheorem wp_forever (Q : Assertion) : wp forever Q ⊣⊢ aFalse := by\n  constructor\n  · intro σ h ⟨s', hex, _⟩\n    exact (no_exec_forever rfl hex).elim\n  · intro σ h hf\n    exact hf.elim\n\n-- `aFalse` does solve the equation …\ntheorem aFalse_solves (Q : Assertion) : aFalse ⊣⊢ loopEqn Q aFalse := by\n  constructor\n  · intro σ h hf; exact hf.elim\n  · intro σ h hx\n    cases hx with\n    | inl hl => obtain ⟨_, _, _, hf⟩ := hl; exact hf\n    | inr hr =>\n        have hb : BExpr.eval σ (.equals (.const 0) (.const 0)) = false := hr.1\n        simp [BExpr.eval, Atom.eval] at hb\n\n-- … but so does `aTrue`, and `aTrue` is not `wp forever Q`.\ntheorem aTrue_solves (Q : Assertion) : aTrue ⊣⊢ loopEqn Q aTrue := by\n  constructor\n  · intro σ h _\n    exact Or.inl ⟨rfl, ⟨σ, h⟩, Exec.skip, trivial⟩\n  · intro σ h _\n    trivial"
        },
        {
          "t": "p",
          "h": "So the equation alone does not determine <code>wp</code>; you have to say <i>which</i> solution, and total correctness says the least. You can see the same split in M13's two loop rules. <code>partialHoare_while</code> (m13-3) takes a bare invariant <code>I</code> and concludes a <code>PartialHoare</code>. <code>hoare_while_variant</code> (m13-4) concludes a full <code>Hoare</code>, and to do it takes a <code>Nat</code>-indexed family <code>I : Nat → Assertion</code> instead — the index being a measure that strictly decreases each iteration. The extra data is what rules out the non-terminating states that the greatest solution would have let in."
        }
      ]
    },
    {
      "t": "dod",
      "h": "You can move freely between forward Hoare reasoning and backward weakest-precondition calculation, and you can tell whether a precondition you wrote is genuinely the weakest one."
    }
  ]
});
