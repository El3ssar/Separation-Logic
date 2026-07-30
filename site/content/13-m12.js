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
      "Define the precondition rather than guess it, and see that <code>Hoare P c Q</code> and <code>P ⊢ wp c Q</code> are one proposition spelled twice.",
      "Prove the four structural equations — <code>wp_skip</code>, <code>wp_assign</code>, <code>wp_seq</code>, <code>wp_mono</code> — and fold them over a two-command program to produce its precondition mechanically.",
      "Compute <code>wp</code> for a write and for a free, and read off the existential that appears over exactly the data the command never looks at.",
      "Exhibit the single heap that proves a precondition you wrote by hand is stronger than it had to be."
    ],
    "needs": [
      "<code>Exec</code> and its constructors, and inversion by <code>cases hex with | free hl =&gt; …</code>.",
      "<code>Hoare</code> and <code>subst</code> from M6; <code>hoare_frame</code> with its two side conditions, for the closing asides.",
      "<code>funext</code> and <code>congrFun</code>, <code>by_cases</code>, <code>subst</code>, and the M1 pointwise lemmas <code>singleton_other</code>, <code>write_other</code>, <code>erase_other</code>."
    ],
    "payoff": "Every mechanised verifier you are likely to meet — Dafny, Why3, Viper, Iris’s proof mode — is a <code>wp</code> calculator. After this chapter you know what it calculates, why the answer is forced rather than invented, and what it means for a specification to be the honest one."
  },

  "blocks": [

    { "t": "h3", "s": "The set of states that work" },

    { "t": "p",
      "h": "A weakest precondition, if there is one, is an assertion, and an assertion is a predicate on states. So stop asking which assertion to write and ask which states belong in it: the ones from which <code>c</code> runs without faulting, terminates, and finishes somewhere satisfying <code>Q</code>. Whether a given state qualifies is settled by <code>Exec</code>, not by your ingenuity, and collecting the ones that qualify takes two lines." },

    { "t": "code",
      "src": "def wp (c : Cmd) (Q : Assertion) : Assertion :=\n  fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap" },

    { "t": "p",
      "h": "<code>wp c</code> sends assertions to assertions, and unlike the <code>Q -∗ S</code> of the ramified frame rule it is fixed by <code>c</code> alone — nothing about it is yours to choose. Weakest means largest, and this set is largest for a trivial reason: qualifying <i>is</i> the entrance requirement, so no state that works has been left out." },

    { "t": "defn",
      "term": "weakest precondition",
      "h": "<code>wp c Q</code> is the greatest element of <code>{P | Hoare P c Q}</code> in the entailment order — <i>greatest</i> meaning weakest, since <code>P ⊢ P'</code> reads “<code>P</code> is at least as strong as <code>P'</code>”. Two claims are packed into that: <code>wp c Q</code> is itself in the set, and every other member entails it. The set is also downward closed, which is precondition strengthening. Entailment is a preorder, so “greatest” is unique only up to <code>⊣⊢</code>." },

    { "t": "p",
      "h": "Both hold, and neither needs a proof." },

    { "t": "code",
      "src": "theorem hoare_iff_entails_wp (P Q : Assertion) (c : Cmd) :\n    Hoare P c Q ↔ P ⊢ wp c Q := Iff.rfl" },

    { "t": "note", "kind": "key", "title": "The one thing to remember",
      "h": "<code>Iff.rfl</code> proves an <code>↔</code> whose two sides are the <i>same</i> proposition, not merely equivalent ones. So this is not a theorem relating triples to weakest preconditions; it is the observation that there is only one statement here. Forward reasoning about triples and backward reasoning about preconditions are that statement read from opposite ends." },

    { "t": "detail", "title": "The unfolding, by hand, and where it stops working", "tag": "Lean", "open": false,
      "blocks": [
        { "t": "txt",
          "src": "  Hoare P c Q\n= ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap      -- unfold Hoare\n\n  P ⊢ wp c Q\n= Entails P (wp c Q)\n= ∀ σ h, P σ h → wp c Q σ h                                        -- unfold Entails\n= ∀ σ h, P σ h → (fun σ h => ∃ s', …) σ h                          -- unfold wp\n= ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap       -- beta" },

        { "t": "p",
          "h": "Three <code>def</code> unfoldings and one beta step, all of which Lean performs silently when checking a term against a type. The two <i>types</i> coincide, not just their inhabitants, so you can drop the <code>↔</code> and state an equation at <code>Prop</code>:" },

        { "t": "code", "tag": "illustration",
          "src": "example (P Q : Assertion) (c : Cmd) : Hoare P c Q = (P ⊢ wp c Q) := rfl" },

        { "t": "p",
          "h": "Swap <code>Hoare</code> for <code>PartialHoare</code> and the same proof fails, because <code>PartialHoare</code> quantifies over <code>s'</code> universally and outside the implication. That is a different proposition, not a different spelling." },

        { "t": "code", "tag": "sketch",
          "src": "example (P Q : Assertion) (c : Cmd) : PartialHoare P c Q ↔ P ⊢ wp c Q := Iff.rfl" },

        { "t": "state", "cap": "what Lean actually says",
          "src": "error: Type mismatch\n  Iff.rfl\nhas type\n  ?m.1 ↔ ?m.1\nbut is expected to have type\n  PartialHoare P c Q ↔ P ⊢ wp c Q" },

        { "t": "p",
          "h": "<code>?m.1 ↔ ?m.1</code> is Lean stating what it wanted: one proposition, used twice. It could not find one that fits both slots." }
      ] },

    { "t": "p",
      "h": "The difference between the two readings is which end you start from, and only one end lets you avoid knowing the answer in advance." },

    { "t": "cmp",
      "left": {
        "t": "Forwards (M6–M9)",
        "h": "Split the program with <code>hoare_seq (Q := …)</code>. <b>You</b> supply the intermediate assertion at every join. Guess wrong and the second half does not close, and you go back and guess again.",
        "tag": "sketch",
        "src": "hoare_seq (Q := ???)\n  step₁_spec\n  step₂_spec"
      },
      "right": {
        "t": "Backwards (this chapter)",
        "h": "Start at the postcondition and apply <code>wp_seq</code> repeatedly. The intermediate assertion is <i>produced</i>. What is left at the front is one entailment between the given precondition and the computed one, with no program in it.",
        "kind": "good",
        "tag": "sketch",
        "src": "wp (c₁ ;; c₂) Q\n  ⊣⊢ wp c₁ (wp c₂ Q)\n         └── computed, not guessed"
      } },

    { "t": "h3", "s": "A definition is not a calculus" },

    { "t": "p",
      "h": "Existence is settled. Computation is not. <code>wp (.free l) emp</code> is, by definition, a sentence about the existence of runs, and no amount of looking at it turns into <code>∃ v, l ↦ v</code>. What makes the definition calculable is one equation per command shape, each replacing a <code>wp</code> by something with less program inside it." },

    { "t": "p",
      "h": "Every one of those equations is proved the same way. Left to right you are handed a run and must say what it did: invert the derivation. Right to left you must produce a run: build one from the constructor. There is no third move anywhere in this chapter." },

    { "t": "sec", "s": "Exercises · the equations of wp" },

    { "t": "ex",
      "id": "m12-1",
      "name": "wp_skip / wp_assign",
      "hard": false,

      "why": "The two base cases, and the place to learn the rhythm. <code>wp_assign</code> is the assignment axiom in its natural direction, and it makes the semantic <code>subst</code> look obvious rather than clever: <code>subst x e Q</code> was defined to describe the post-assignment store, and that is exactly the state the derivation forces.",
      "setup": "In scope: <code>wp</code>, <code>subst</code>, and the <code>Exec</code> constructors. <code>⊣⊢</code> is a bare <code>And</code>, so <code>constructor</code> splits it. You need <code>Exec.skip</code> and <code>Exec.assign</code>.",
      "goal": "theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q\ntheorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :\n    wp (.assign x e) Q ⊣⊢ subst x e Q",

      "hints": [
        "Treat the two directions as separate proofs, because they are. <code>constructor</code> first.",
        "Forwards you are <i>given</i> a run and must say where it ended. The only way to find out is <code>cases hex</code>. Exactly one constructor can have produced it, so you get exactly one subgoal.",
        "Backwards you must <i>supply</i> the final state, a derivation reaching it, and a proof of <code>Q</code> there. For <code>skip</code> the final state is <code>⟨σ, h⟩</code>; for <code>assign</code> it is <code>⟨Store.set σ x (e.eval σ), h⟩</code>.",
        "Each direction: forwards, <code>cases hex</code> to see what the final state was; backwards, supply the state and the derivation."
      ],

      "sol": "theorem wp_skip (Q : Assertion) : wp .skip Q ⊣⊢ Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex; exact hq\n  · intro σ h hq\n    exact ⟨⟨σ, h⟩, Exec.skip, hq⟩\n\ntheorem wp_assign (x : Var) (e : Atom) (Q : Assertion) :\n    wp (.assign x e) Q ⊣⊢ subst x e Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex; exact hq\n  · intro σ h hq\n    exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",

      "expl": "Both theorems have the same five-line skeleton, and the move that matters is <code>cases hex</code>. There is only one case, so it is not case analysis — it is there to learn an equation. Inverting <code>Exec .skip ⟨σ,h⟩ s'</code> forces <code>s'</code> to be <code>⟨σ,h⟩</code>; inverting the assignment forces the updated state. After that <code>hq</code> already has the type the goal wants, up to reductions Lean performs and never displays.",

      "walk": [
        { "tac": "constructor",
          "h": "<code>AssertionEquiv</code> is <code>And</code>, so this leaves <code>case left</code> (<code>wp .skip Q ⊢ Q</code>) and <code>case right</code> (<code>Q ⊢ wp .skip Q</code>)." },
        { "tac": "· intro σ h ⟨s', hex, hq⟩",
          "h": "Three introductions, the third destructured on arrival: <code>wp .skip Q σ h</code> is an <code>∃</code> over an <code>∧</code>, so the pattern names the witness, the derivation and the postcondition proof at once." },
        { "tac": "cases hex; exact hq",
          "h": "Which constructor could have concluded <code>Exec .skip ⟨σ,h⟩ s'</code>? Only <code>Exec.skip</code>, and it forces <code>s' := ⟨σ,h⟩</code>. So <code>hq</code>, whose type mentioned an unknown <code>s'</code>, now mentions a literal state whose projections reduce to <code>σ</code> and <code>h</code>." },
        { "tac": "· intro σ h hq",
          "h": "The other direction. <code>hq : Q σ h</code> needs no destructuring; all the work is in the goal, which is an existential to be built." },
        { "tac": "exact ⟨⟨σ, h⟩, Exec.skip, hq⟩",
          "h": "The witness <code>⟨σ, h⟩</code> — itself an anonymous constructor, this time for <code>State</code> — then the derivation, then <code>hq</code>." },
        { "tac": "theorem wp_assign (x : Var) (e : Atom) (Q : Assertion) : wp (.assign x e) Q ⊣⊢ subst x e Q := by",
          "h": "Second theorem, same skeleton. The new ingredient is <code>subst x e Q</code>, which is <code>fun σ h => Q (Store.set σ x (e.eval σ)) h</code> — an assertion about the <i>post</i>-assignment store." },
        { "tac": "constructor",
          "h": "Two entailments again." },
        { "tac": "· intro σ h ⟨s', hex, hq⟩",
          "h": "Same destructuring intro; the goal is now <code>subst x e Q σ h</code>." },
        { "tac": "cases hex; exact hq",
          "h": "Inverting forces <code>s'</code> to be <code>⟨Store.set σ x (e.eval σ), h⟩</code>. So <code>hq</code> is <code>Q</code> at that state, and <code>subst x e Q σ h</code> unfolds to exactly that. The assignment axiom is a tautology once <code>subst</code> is semantic." },
        { "tac": "· intro σ h hq",
          "h": "Backwards. <code>hq</code> is <i>already</i> a proof of <code>Q</code> at the post-state; nothing needs converting." },
        { "tac": "exact ⟨⟨Store.set σ x (e.eval σ), h⟩, Exec.assign, hq⟩",
          "h": "You must write the post-state out. <code>Exec.assign</code> takes no explicit arguments, so Lean has nothing to read it off until the existential has been given a witness." }
      ],

      "deep": [
        { "t": "trace",
          "title": "wp_skip, tactic by tactic",
          "start": "Q : Assertion\n⊢ wp Cmd.skip Q ⊣⊢ Q",
          "steps": [
            { "tac": "constructor",
              "state": "case left\nQ : Assertion\n⊢ wp Cmd.skip Q ⊢ Q\n\ncase right\nQ : Assertion\n⊢ Q ⊢ wp Cmd.skip Q",
              "h": "Two goals, named after <code>And.intro</code>’s arguments. Note <code>Cmd.skip</code> where the source wrote <code>.skip</code>: the dot is elaboration sugar and does not survive into the display." },
            { "tac": "intro σ h ⟨s', hex, hq⟩",
              "state": "case left\nQ : Assertion\nσ : Store\nh : Heap\ns' : State\nhex : Exec Cmd.skip { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ Q σ h",
              "h": "The goal is <code>Q σ h</code>; the hypothesis is <code>Q s'.store s'.heap</code>. Nothing connects them while <code>s'</code> is an opaque variable." },
            { "tac": "cases hex",
              "state": "case left.skip\nQ : Assertion\nσ : Store\nh : Heap\nhq : Q { store := σ, heap := h }.store { store := σ, heap := h }.heap\n⊢ Q σ h",
              "h": "<code>s'</code> and <code>hex</code> are gone, and every occurrence of <code>s'</code> has become the literal state. Lean does <i>not</i> simplify <code>{ store := σ, heap := h }.store</code> to <code>σ</code> in the display, though it will happily do so when checking." },
            { "tac": "exact hq",
              "state": "No goals.",
              "h": "Projection of a literal structure is an iota reduction, and <code>exact</code> checks up to definitional equality. This is the commonest source of “but those look different!” in this chapter: the displayed type and the accepted type differ by reductions Lean does not bother to print." }
          ],
          "done": "No goals." },

        { "t": "trace",
          "title": "wp_assign, forwards — and a spectacular goal display",
          "start": "case left\nx : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.assign x e) { store := σ, heap := h } s'\nhq : Q s'.store s'.heap\n⊢ subst x e Q σ h",
          "steps": [
            { "tac": "cases hex",
              "state": "case left.assign\nx : Var\ne : Atom\nQ : Assertion\nσ : Store\nh : Heap\nhq :\n  Q\n    { store := { store := σ, heap := h }.store.set x (Atom.eval { store := σ, heap := h }.store e),\n        heap := { store := σ, heap := h }.heap }.store\n    { store := { store := σ, heap := h }.store.set x (Atom.eval { store := σ, heap := h }.store e),\n        heap := { store := σ, heap := h }.heap }.heap\n⊢ subst x e Q σ h",
              "h": "<code>Exec.assign</code>’s conclusion with its implicit state instantiated and nothing reduced. Two spellings collide here. <code>Store.set σ x v</code> prints as <code>σ.set x v</code>, because the printer folds <code>Foo.bar a …</code> back into <code>a.bar …</code> when <code>a</code> has type <code>Foo</code>. But the source’s <code>e.eval σ</code> prints as <code>Atom.eval σ e</code>, since <code>Atom.eval</code> declares the store first and the <code>Atom</code> is not the first explicit argument. You cannot predict which form you will be shown; read them as the same term." },
            { "tac": "exact hq",
              "state": "No goals.",
              "h": "Reduce the projections and this hypothesis is <code>Q (Store.set σ x (e.eval σ)) h</code>. Unfold <code>subst</code> in the goal and it is <code>Q (Store.set σ x (e.eval σ)) h</code>. Lean does both reductions during the check and shows you neither." }
          ],
          "done": "No goals." },

        { "t": "cmp",
          "left": {
            "t": "Skipping the inversion",
            "kind": "bad",
            "h": "Surely <code>hq</code> is already what we want? It is not. <code>s'</code> is a bound variable about which nothing is known.",
            "tag": "sketch",
            "src": "intro σ h ⟨s', hex, hq⟩\nexact hq\n\n-- error: Type mismatch\n--   hq\n-- has type\n--   Q s'.store s'.heap\n-- but is expected to have type\n--   Q σ h"
          },
          "right": {
            "t": "Why simp does not rescue you",
            "h": "<code>simp [wp]</code> unfolds the definition and stops. It cannot invert an inductive predicate — that is <code>cases</code>’s job, not a rewrite. Reaching for <code>simp</code> when the obstacle is an inductive hypothesis is the classic wrong reflex.",
            "tag": "sketch",
            "src": "intro σ h hw\nsimp [wp] at hw\n\n-- hw : ∃ s', Exec Cmd.skip { store := σ, heap := h } s' ∧ Q s'.store s'.heap\n-- ⊢ Q σ h        (unchanged)"
          } }
      ],

      "pitfall": "Writing <code>exact hq</code> before <code>cases hex</code>: the types look close, but <code>s'</code> is opaque until you invert. The reverse trap is the one that makes people distrust Lean — <i>after</i> <code>cases</code>, the displayed type of <code>hq</code> is a nest of projections resembling nothing in the goal, and <code>exact hq</code> works anyway. Never conclude from a goal display that a term will not typecheck.",

      "variants": "Weaken <code>wp .skip Q ⊣⊢ Q</code> to <code>wp .skip Q ⊢ Q</code> and you drop the half that has to produce a derivation — the half that would fail for a command that can get stuck. Now try the same statement for <code>.load x l</code>. <code>wp (.load x l) Q ⊢ Q</code> is false because the run changes the store; <code>Q ⊢ wp (.load x l) Q</code> is false for an unrelated reason, since <code>Exec.load</code> demands <code>h l = some v</code> and no assumption supplies it. Those two failures are the two jobs <code>wp</code> does: transport the postcondition, and assert safety."
    },

    { "t": "p",
      "h": "Both of those commands have a single run whose final state you can write down. Sequencing is where the transformer shape starts to earn its keep: <code>wp (c₁ ;; c₂) Q</code> must be expressed through <code>wp c₁</code> and <code>wp c₂</code>, and the state between them occurs nowhere in the statement." },

    { "t": "ex",
      "id": "m12-2",
      "name": "wp_seq",
      "hard": false,

      "why": "<b>The rule that makes backwards reasoning work.</b> <code>wp</code> of a sequence is the composition of the two transformers, so a straight-line program becomes a fold from the end. Without it <code>wp</code> would be a definition with no calculus attached, and the intermediate assertion at every <code>;;</code> would still be yours to invent.",
      "setup": "You need <code>Exec.seq</code>, which takes two derivations and an intermediate state. The intermediate state is an <i>implicit</i> argument of the constructor, which has a visible consequence in the proof.",
      "goal": "theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q)",

      "hints": [
        "Both directions are about the intermediate state. Forwards it is buried in the derivation you are given; backwards it is buried in the nested <code>wp</code> you are given. Dig it out and hand it over.",
        "Forwards: <code>cases hex with | seq h₁ h₂ =&gt;</code> names the two sub-derivations and nothing else, because the state between them is implicit. Write <code>_</code> and let unification find it.",
        "Backwards: the hypothesis unfolds to <code>∃ s₁, Exec c₁ … s₁ ∧ ∃ s₂, Exec c₂ … s₂ ∧ Q …</code>, so one flat pattern <code>⟨s₁, hex₁, s₂, hex₂, hq⟩</code> takes all five components.",
        "Forwards, invert the <code>seq</code> derivation. Backwards, glue with <code>Exec.seq</code>. No determinism is needed in either direction."
      ],

      "sol": "theorem wp_seq (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (c₁ ;; c₂) Q ⊣⊢ wp c₁ (wp c₂ Q) := by\n  constructor\n  · intro σ h ⟨s'', hex, hq⟩\n    cases hex with\n    | seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩\n  · intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩\n    exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",

      "expl": "Determinism is <i>not</i> used. The equation holds for nondeterministic languages too, provided <code>wp</code> is read as “there exists a terminating run landing in <code>Q</code>” (angelic) rather than “all runs do” (demonic). Ours is the angelic one; a demonic <code>wp</code> would use <code>∀</code> and would need a separate safety conjunct.",

      "walk": [
        { "tac": "constructor",
          "h": "Split the <code>⊣⊢</code>." },
        { "tac": "· intro σ h ⟨s'', hex, hq⟩",
          "h": "<code>s''</code> is the <i>final</i> state of the whole sequence — two primes because it is the state after two commands." },
        { "tac": "cases hex with",
          "h": "Only <code>Exec.seq</code> can conclude a <code>;;</code>, so one branch; the <code>with</code> form lets you name that branch’s arguments." },
        { "tac": "| seq h₁ h₂ => exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩",
          "h": "<code>h₁ : Exec c₁ ⟨σ,h⟩ s'✝</code> and <code>h₂ : Exec c₂ s'✝ s''</code>, with <code>s'✝</code> inaccessible. Supply the intermediate state as <code>_</code>, then <code>h₁</code>, then a proof of <code>wp c₂ Q</code> there — which is <code>⟨s'', h₂, hq⟩</code>." },
        { "tac": "· intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩",
          "h": "Five components in one flat pattern: the state after <code>c₁</code>, the first run, then the nested <code>wp c₂ Q</code> opened into its three." },
        { "tac": "exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",
          "h": "<code>Exec.seq</code> unifies its implicit middle state with <code>s₁</code>. One subtlety, invisible here and shown in the trace: <code>hex₂</code>’s start state displays as <code>{ store := s₁.store, heap := s₁.heap }</code>, and structure eta makes that the same term as <code>s₁</code>." }
      ],

      "deep": [
        { "t": "trace",
          "title": "wp_seq, both directions",
          "start": "case left\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns'' : State\nhex : Exec (c₁ ;; c₂) { store := σ, heap := h } s''\nhq : Q s''.store s''.heap\n⊢ wp c₁ (wp c₂ Q) σ h",
          "steps": [
            { "tac": "cases hex with | seq h₁ h₂ =>",
              "state": "case left.seq\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns'' : State\nhq : Q s''.store s''.heap\ns'✝ : State\nh₁ : Exec c₁ { store := σ, heap := h } s'✝\nh₂ : Exec c₂ s'✝ s''\n⊢ wp c₁ (wp c₂ Q) σ h",
              "h": "There it is: <code>s'✝ : State</code>. The constructor’s binder <code>{s'}</code> is implicit, and <code>cases … with | seq h₁ h₂</code> named only the two explicit arguments, so Lean invented an unwritable name. That is why the solution says <code>⟨_, h₁, …⟩</code> — the underscore hands the job to unification, which reads the state off <code>h₁</code>. <code>rename_i sMid</code> after the arrow works too." },
            { "tac": "exact ⟨_, h₁, ⟨s'', h₂, hq⟩⟩",
              "state": "No goals.",
              "h": "The nesting mirrors the statement: the outer triple for <code>wp c₁ (…)</code>, the inner one for <code>wp c₂ Q</code> at the intermediate state. Fully flat, <code>⟨_, h₁, s'', h₂, hq⟩</code>, also works." },
            { "tac": "intro σ h ⟨s₁, hex₁, s₂, hex₂, hq⟩",
              "state": "case right\nc₁ c₂ : Cmd\nQ : Assertion\nσ : Store\nh : Heap\ns₁ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s₁\ns₂ : State\nhex₂ : Exec c₂ { store := s₁.store, heap := s₁.heap } s₂\nhq : Q s₂.store s₂.heap\n⊢ wp (c₁ ;; c₂) Q σ h",
              "h": "<code>hex₂</code> starts at <code>{ store := s₁.store, heap := s₁.heap }</code> rather than <code>s₁</code>, because <code>wp c₂ Q</code> was applied to the two projections and <code>wp</code> repackages them. Eta for structures makes any <code>s : State</code> the same term as <code>{ store := s.store, heap := s.heap }</code>, so nothing needs repairing." },
            { "tac": "exact ⟨s₂, Exec.seq hex₁ hex₂, hq⟩",
              "state": "No goals.",
              "h": "Unification takes the middle state to be <code>s₁</code> from <code>hex₁</code>, then checks <code>hex₂</code> against <code>Exec c₂ s₁ s₂</code>, which holds up to eta." }
          ],
          "done": "No goals." },

        { "t": "steps",
          "title": "What the two directions are, mathematically",
          "items": [
            { "k": "Re-bracketing an existential",
              "h": "A run of <code>c₁ ;; c₂</code> from <code>s</code> to <code>s''</code> <i>is</i> a pair of runs through some middle state, so the content is <code>∃ s'', (∃ s', R₁ s s' ∧ R₂ s' s'') ∧ Q s''</code> against <code>∃ s', R₁ s s' ∧ (∃ s'', R₂ s' s'' ∧ Q s'')</code>. Backwards is the same move read right to left, which is why neither branch needs a lemma." },
            { "k": "So <code>wp</code> is a homomorphism",
              "h": "<code>wp (c₁ ;; c₂) = wp c₁ ∘ wp c₂</code> as transformers, and <code>wp .skip = id</code> by m12-1. Sequencing is a monoid with <code>skip</code> as unit, transformers are a monoid under composition, and <code>wp</code> maps one to the other. That is “verification is compositional”, stated so it can be checked." },
            { "k": "And <code>Exec</code> is barely used",
              "h": "Only <code>Exec.seq</code> appears, in both directions, and only as a two-field constructor. Any relation with an inference rule of that shape gets the same equation." }
          ] },

        { "t": "detail", "title": "Angelic and demonic <code>wp</code>, and why they coincide here", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p",
              "h": "The demonic reading is safety plus <i>all</i> runs landing in <code>Q</code>. In our deterministic language it agrees with ours." },
            { "t": "code", "tag": "illustration",
              "src": "def wpDemonic (c : Cmd) (Q : Assertion) : Assertion :=\n  fun σ h => (∃ s', Exec c ⟨σ, h⟩ s') ∧ ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap\n\ntheorem wp_eq_wpDemonic (c : Cmd) (Q : Assertion) : wp c Q ⊣⊢ wpDemonic c Q := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    refine ⟨⟨s', hex⟩, ?_⟩\n    intro s'' hex''\n    rw [exec_deterministic hex'' hex]\n    exact hq\n  · intro σ h ⟨⟨s', hex⟩, hall⟩\n    exact ⟨s', hex, hall s' hex⟩" },
            { "t": "p",
              "h": "Only the forward direction uses anything — <code>exec_deterministic</code>, to say the run you were handed is the run you were promised. That is the checked part, and it is the whole of it. What follows is about a language we do not have." },
            { "t": "p",
              "h": "Drop determinism and the forward direction is what breaks: “some run lands in <code>Q</code>” stops implying “every run does”, so the angelic reading admits states the demonic one rejects. Which you want depends on who chooses the run. If it is you — a scheduler you control, an oracle, a proof search — angelic is right. If it is an adversary, the guarantee must hold for every run, which is why real tools are demonic. We can afford the angelic one because <code>Exec</code> leaves nothing to choose." },
            { "t": "p",
              "h": "Note the separate safety conjunct in <code>wpDemonic</code>. Without <code>∃ s', Exec c ⟨σ,h⟩ s'</code>, a state from which <code>c</code> faults satisfies <code>∀ s', … → Q</code> vacuously, and the transformer certifies a program that dereferences a dangling pointer. Splitting that conjunct out is how the literature separates partial from total correctness at the <code>wp</code> level." }
          ] }
      ],

      "pitfall": "Trying to name the intermediate state. <code>cases hex with | seq h₁ h₂ =&gt;</code> names two things and the state is not one of them; the fix is <code>_</code> in the term you build, or <code>rename_i</code>. The subtler trap is in the backward direction: you may want to “fix up” <code>hex₂</code> because it prints as starting at <code>{ store := s₁.store, heap := s₁.heap }</code>. Do not. Structure eta already makes them one term, and any <code>show</code> or <code>rw</code> you add will be rejected for having nothing to rewrite.",

      "variants": "Reverse the composition — <code>wp (c₁ ;; c₂) Q ⊣⊢ wp c₂ (wp c₁ Q)</code> — and both directions fail, because <code>Exec c₂</code> would have to start where the whole program starts. The order is forced by the definition, which is why backwards reasoning is a <i>right</i> fold. Separately, keep only <code>wp c₁ (wp c₂ Q) ⊢ wp (c₁ ;; c₂) Q</code>: that is the gluing half, the one a tool needs to turn a computed precondition back into a claim about the whole program. The other half is what lets you compute at all."
    },

    { "t": "p",
      "h": "Folding those equations over a program means replacing an <i>inner</i> <code>wp</code> while the outer one stays put, and <code>wp_seq</code> cannot do that on its own. It is an <code>⊣⊢</code>, which is a conjunction of entailments, not an equation — there is no <code>rw</code> that takes one. What you need instead is that improving <code>Q</code> improves <code>wp c Q</code>." },

    { "t": "ex",
      "id": "m12-3",
      "name": "wp_mono",
      "hard": false,

      "why": "Monotonicity is what lets a calculation happen inside a bigger one: improve the postcondition of an inner command and everything around it is untouched. It is the step that takes <code>wp c₁ (wp c₂ Q)</code> to <code>wp c₁ (subst y (.var x) Q)</code>. Without it the equations could only ever be applied at the outermost position, and the calculus would not compose.",
      "setup": "Two lines. Note that <code>h : Q ⊢ Q'</code> is a function of three arguments, so it is applied, not rewritten with.",
      "goal": "theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q'",

      "hints": [
        "The run is irrelevant: the same derivation witnesses both sides. Only the last component of the triple changes.",
        "Destructure with <code>intro σ hh ⟨s', hex, hq⟩</code>, then rebuild <code>⟨s', hex, ?_⟩</code> and fill the hole by applying <code>h</code>.",
        "<code>h s'.store s'.heap hq : Q' s'.store s'.heap</code>. The heap argument is <code>s'.heap</code>, the heap <i>after</i> the run — not the <code>hh</code> you introduced."
      ],

      "sol": "theorem wp_mono {Q Q' : Assertion} (c : Cmd) (h : Q ⊢ Q') : wp c Q ⊢ wp c Q' := by\n  intro σ hh ⟨s', hex, hq⟩\n  exact ⟨s', hex, h s'.store s'.heap hq⟩",

      "expl": "<code>wp c</code> is a monotone assertion transformer, and monotonicity is the only property of it that a fold uses beyond the equations themselves. Every step in this chapter that reaches inside a <code>wp</code> is these two lines.",

      "walk": [
        { "tac": "intro σ hh ⟨s', hex, hq⟩",
          "h": "The heap is called <code>hh</code> because <code>h</code> is taken by the entailment hypothesis. The third argument opens into witness, derivation and postcondition proof." },
        { "tac": "exact ⟨s', hex, h s'.store s'.heap hq⟩",
          "h": "Reuse the same final state and the same derivation; the command has not changed, so nothing about the run has to. Only the third slot needs work, and <code>h</code> applied at the final store and heap supplies it." }
      ],

      "deep": [
        { "t": "trace",
          "title": "wp_mono in two steps",
          "start": "Q Q' : Assertion\nc : Cmd\nh : Q ⊢ Q'\n⊢ wp c Q ⊢ wp c Q'",
          "steps": [
            { "tac": "intro σ hh ⟨s', hex, hq⟩",
              "state": "Q Q' : Assertion\nc : Cmd\nh : Q ⊢ Q'\nσ : Store\nhh : Heap\ns' : State\nhex : Exec c { store := σ, heap := hh } s'\nhq : Q s'.store s'.heap\n⊢ wp c Q' σ hh",
              "h": "The goal is still folded — <code>intro</code> unfolded only far enough to consume its arguments, and <code>exact</code> will unfold the rest when it checks the bracket." },
            { "tac": "exact ⟨s', hex, h s'.store s'.heap hq⟩",
              "state": "No goals.",
              "h": "Note where the entailment is applied: at the state <i>after</i> the run. Applying it at <code>σ, hh</code> is the mistake to make once — it is a well-typed application that then fails to match." }
          ],
          "done": "No goals." },

        { "t": "p",
          "h": "Those two lines prove more than they look like. Compose <code>wp_mono c hpost : wp c Q ⊢ wp c Q'</code> with <code>Hoare P c Q</code>, which <i>is</i> <code>P ⊢ wp c Q</code>, and <code>entails_trans</code> gives <code>Hoare P c Q'</code>. Weakening the postcondition of a triple is monotonicity of <code>wp</code>, with no separate proof." },

        { "t": "detail", "title": "The frame rule, stated for <code>wp</code>", "tag": "payoff", "open": false,
          "blocks": [
            { "t": "p",
              "h": "Instantiate <code>hoare_frame</code> at <code>P := wp c Q</code> and its first hypothesis <code>Hoare (wp c Q) c Q</code> becomes <code>wp c Q ⊢ wp c Q</code>." },
            { "t": "code", "tag": "illustration",
              "src": "theorem wp_frame {Q R : Assertion} {c : Cmd}\n    (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    wp c Q ∗ R ⊢ wp c (Q ∗ R) :=\n  hoare_frame (entails_refl (wp c Q)) hlocal hpres" },
            { "t": "p",
              "h": "One line, and it is the rule letting a <code>wp</code>-based tool reason about a small footprint inside a large heap. It is this short because <code>wp c Q</code> is by construction the greatest precondition, so “apply the frame rule to the best possible triple” needs no triple to be supplied." },
            { "t": "p",
              "h": "The side conditions are not free. <code>hlocal</code> and <code>hpres</code> survive unchanged into the statement and carry all the content. <code>Iff.rfl</code> removes the triple from the frame rule’s hypotheses and removes nothing about locality — if it did, M8’s counterexamples would still be counterexamples and the rule would be unsound." }
          ] }
      ],

      "pitfall": "Applying <code>h</code> at the wrong state: <code>h σ hh hq</code> rather than <code>h s'.store s'.heap hq</code>. Both are well-typed applications of a three-argument function, so the error surfaces late, as a mismatch on the third argument. An entailment used inside a <code>wp</code> is always applied at the post-state, because that is where the postcondition lives.",

      "variants": "Try the contravariant version — <code>wp c Q ⊢ wp c Q'</code> from <code>Q' ⊢ Q</code> — and it fails immediately: you would need to turn a proof of <code>Q</code> into a proof of <code>Q'</code> with the arrow pointing the other way. <code>wp c</code> is covariant because <code>Q</code> occurs positively in <code>∃ s', … ∧ Q …</code>. In <code>Hoare P c Q</code>, by contrast, <code>P</code> sits to the left of an implication, so triples are contravariant there. Same rule as function types, and it is worth checking that the variances of <code>hoare_consequence</code> agree."
    },

    { "t": "h3", "s": "The fold, run once" },

    { "t": "p",
      "h": "Take <code>x := 3 ;; y := x</code> and an arbitrary <code>Q</code>. Peel the <i>last</i> command first: <code>wp_seq</code> turns <code>wp (c₁ ;; c₂) Q</code> into <code>wp c₁ (wp c₂ Q)</code>, so the inner application is the later command. Then replace each <code>wp</code> of an assignment by its <code>subst</code>." },

    { "t": "txt",
      "src": "  wp (x := 3 ;; y := x) Q\n⊣⊢ wp (x := 3) (wp (y := x) Q)           -- wp_seq\n⊣⊢ wp (x := 3) (subst y (var x) Q)       -- wp_assign, inner, under wp_mono\n⊣⊢ subst x (const 3) (subst y (var x) Q) -- wp_assign, outer" },

    { "t": "p",
      "h": "The last line is the weakest precondition. It depends on <code>Q</code>, which is sitting inside it; the <i>calculation</i> does not. At each step the equation to apply was fixed by the outermost command and by nothing else, so the same fold serves every postcondition you might substitute. That is what the word calculus is doing here." },

    { "t": "code",
      "tag": "illustration",
      "cap": "the same chain in Lean, once in each direction; compiles against the M12 prelude",
      "src": "example (x y : Var) (Q : Assertion) :\n    wp (.assign x (.const 3) ;; .assign y (.var x)) Q\n      ⊣⊢ subst x (.const 3) (subst y (.var x) Q) := by\n  constructor\n  · refine entails_trans (wp_seq _ _ Q).1 ?_\n    refine entails_trans (wp_mono _ (wp_assign y (.var x) Q).1) ?_\n    exact (wp_assign x (.const 3) _).1\n  · refine entails_trans (wp_assign x (.const 3) _).2 ?_\n    refine entails_trans (wp_mono _ (wp_assign y (.var x) Q).2) ?_\n    exact (wp_seq _ _ Q).2" },

    { "t": "p",
      "h": "<code>refine entails_trans e ?_</code> supplies the first factor of a composition and leaves the rest as the next goal, which is what makes the chain read top to bottom. The middle line of each branch is <code>wp_mono</code> reaching under the outer <code>wp</code>." },

    { "t": "h4", "s": "Which equations exist, and which are work" },

    { "t": "tbl",
      "cap": "the wp calculus for our language; the rows carrying an exercise id are proved here, and they are the ones that make the rest routine",
      "head": ["command", "<code>wp c Q</code>", "status"],
      "rows": [
        ["<code>skip</code>", "<code>Q</code>", "m12-1"],
        ["<code>x := e</code>", "<code>subst x e Q</code>", "m12-1"],
        ["<code>c₁ ;; c₂</code>", "<code>wp c₁ (wp c₂ Q)</code>", "m12-2"],
        ["<code>free l</code>, with <code>Q = emp</code>", "<code>∃ v, l ↦ v</code>", "m12-4"],
        ["<code>[l] := new</code>, with <code>Q = l ↦ new</code>", "<code>∃ old, l ↦ old</code>", "m12-5"],
        ["<code>x := [l]</code>, general <code>Q</code>", "<code>∃ v</code>, the cell holds <code>v</code>, and <code>Q</code> at the updated store", "six lines; in the aside below"],
        ["<code>if b then c₁ else c₂</code>", "<code>(b ∧ wp c₁ Q) ∨ (¬b ∧ wp c₂ Q)</code>", "same shape, two constructors; in the aside below"],
        ["<code>while b do c</code>", "<b>least</b> fixed point of <code>X ↦ (b ∧ wp c X) ∨ (¬b ∧ Q)</code>", "not an equation at all"]
      ] },

    { "t": "detail", "title": "The two equations the corpus does not prove: load, and <code>if</code>", "tag": "aside", "open": false,
      "blocks": [
        { "t": "p",
          "h": "The load equation is worth seeing once, because its shape is the shape of every heap command: an existential over the value the command reads, a footprint condition saying the value is really there, and the postcondition evaluated after the effect." },
        { "t": "code", "tag": "illustration",
          "src": "theorem wp_load (x : Var) (l : Loc) (Q : Assertion) :\n    wp (.load x l) Q ⊣⊢\n      aExists (fun v => aAnd (fun _ h => h l = some v)\n                             (fun σ h => Q (Store.set σ x v) h)) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | load hl => rename_i v; exact ⟨v, hl, hq⟩\n  · intro σ h ⟨v, hl, hq⟩\n    exact ⟨⟨Store.set σ x v, h⟩, Exec.load hl, hq⟩" },
        { "t": "p",
          "h": "Two lines of content: forwards, invert and read the value off; backwards, build the derivation from the value. Exercises m12-4 and m12-5 are this same proof specialised to a concrete <code>Q</code>, plus the work of showing the resulting heap condition <i>is</i> a points-to." },
        { "t": "p",
          "h": "The conditional is the same move with two constructors instead of one, so “same shape” in the table is a checked statement rather than a promise." },
        { "t": "code", "tag": "illustration",
          "src": "theorem wp_ite (b : BExpr) (c₁ c₂ : Cmd) (Q : Assertion) :\n    wp (.ite b c₁ c₂) Q ⊣⊢\n      aOr (aAnd (fact (fun σ => b.eval σ = true))  (wp c₁ Q))\n          (aAnd (fact (fun σ => b.eval σ = false)) (wp c₂ Q)) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | iteTrue  hb hc => exact Or.inl ⟨hb, s', hc, hq⟩\n    | iteFalse hb hc => exact Or.inr ⟨hb, s', hc, hq⟩\n  · intro σ h hor\n    cases hor with\n    | inl hl => obtain ⟨hb, s', hc, hq⟩ := hl; exact ⟨s', Exec.iteTrue  hb hc, hq⟩\n    | inr hr => obtain ⟨hb, s', hc, hq⟩ := hr; exact ⟨s', Exec.iteFalse hb hc, hq⟩" },
        { "t": "p",
          "h": "In the backward direction <code>cases hor</code> is inverting an <code>Or</code>, not an <code>Exec</code>. A command whose semantics has <i>k</i> constructors gets a <code>wp</code> equation with <i>k</i> disjuncts; <code>loop</code> is the exception only because one of its two constructors is recursive." }
      ] },

    { "t": "sec", "s": "Exercises · calculating weakest preconditions" },

    { "t": "p",
      "h": "For <code>skip</code>, assignment and <code>;;</code>, the answer was an assertion you could already name. For the heap commands nothing names it, and what the calculation produces is not what you would have written." },

    { "t": "p",
      "h": "When you write a specification you must name every value you mention. The program need not. <code>free l</code> discards the contents of the cell without looking; <code>[l] := new</code> overwrites them without looking. So the honest precondition <i>cannot</i> mention those values, and the only way to own a cell while declining to say what is in it is an existential." },

    { "t": "dl",
      "items": [
        { "k": "<code>aExists (fun v => l ↦ v)</code>",
          "h": "“I own the cell at <code>l</code>, and I decline to say what is in it.”" },
        { "k": "<code>l ↦ v</code> for a fixed <code>v</code>",
          "h": "Strictly stronger. A perfectly good precondition for both commands, the one M7 used, and not the weakest one. The gap between the two is the subject of m12-5." }
      ] },

    { "t": "note", "kind": "info", "title": "Why these two proofs are longer",
      "h": "In m12-1 to m12-3 the postcondition was an opaque <code>Q</code> and there was nothing to compute. Here <code>Q</code> is concrete — <code>emp</code>, or <code>l ↦ new</code> — so inverting the derivation leaves a <i>heap equation</i> to solve, pointwise. The separation-logic content is two lines; the rest is the extensionality argument you have run since M1." },

    { "t": "ex",
      "id": "m12-4",
      "name": "wp_free_emp",
      "hard": true,

      "why": "“What must hold before <code>free l</code> so that afterwards I own nothing?” Answer: I own exactly that cell, and <i>the value does not matter</i>. This is the small-footprint free rule derived rather than postulated — and the precondition M7 guessed turns out to have been slightly too strong.",
      "setup": "You will need <code>erase_other</code> and <code>erase_singleton</code>, plus <code>singleton_same</code> and <code>singleton_other</code>. The helper <code>heap_eq_singleton</code> is part of the exercise: prove it first, as a standalone theorem.",
      "goal": "theorem wp_free_emp (l : Loc) :\n    wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v)",

      "hints": [
        "Ask what the forward direction actually hands you. Inverting <code>Exec.free</code> gives <code>h l = some v</code> for some <code>v</code>, and <code>emp</code> at the final state says <code>Heap.erase h l = Heap.empty</code>. Between them, <code>h</code> is pinned down completely. Say so as a lemma.",
        "The lemma: if <code>h l = some v</code> and <code>Heap.erase h l = Heap.empty</code> then <code>h = Heap.singleton l v</code>. Prove it by <code>funext x</code> and <code>by_cases hx : x = l</code>. At <code>x = l</code> the first hypothesis does it; away from <code>l</code> you need the <i>pointwise</i> consequence of the second.",
        "<code>congrFun hrest x : Heap.erase h l x = Heap.empty x</code>. Then <code>erase_other</code> rewrites the left side to <code>h x</code>, and the right side is <code>none</code> definitionally.",
        "With the lemma: forwards, <code>refine ⟨_, heap_eq_singleton hl ?_⟩</code> — the underscore is the value, inaccessible after <code>cases</code>, and the remaining hole is exactly the <code>emp</code> hypothesis. Backwards, <code>subst</code> the points-to and hand Lean the erased singleton.",
        "You need one heap lemma first: a heap where <code>l</code> is allocated and erasing <code>l</code> leaves nothing is a singleton. Prove <code>heap_eq_singleton</code>, then the forward direction is immediate."
      ],

      "sol": "theorem heap_eq_singleton {h : Heap} {l : Loc} {v : Val}\n    (hl : h l = some v) (hrest : Heap.erase h l = Heap.empty) :\n    h = Heap.singleton l v := by\n  funext x\n  by_cases hx : x = l\n  · subst hx; rw [hl, singleton_same]\n  · rw [singleton_other l x v hx]\n    have := congrFun hrest x\n    rw [erase_other h l x hx] at this\n    exact this\n\ntheorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by\n  constructor\n  · intro σ h ⟨s', hex, he⟩\n    cases hex with\n    | free hl =>\n        refine ⟨_, heap_eq_singleton hl ?_⟩\n        exact he\n  · intro σ h ⟨v, hp⟩\n    subst hp\n    exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v),\n           erase_singleton l v⟩",

      "expl": "<code>heap_eq_singleton</code> carries the mathematics: “allocated at <code>l</code>, and empty after erasing <code>l</code>” characterises singletons. Once it exists, the theorem is bookkeeping — forwards the lemma consumes both facts the inversion produced, backwards there is a single state to write down.",

      "walk": [
        { "tac": "funext x",
          "h": "The goal is an equation between two functions; go pointwise at an arbitrary <code>x</code>." },
        { "tac": "by_cases hx : x = l",
          "h": "<code>case pos</code> with <code>hx : x = l</code>, <code>case neg</code> with <code>hx : ¬x = l</code>. That orientation matters when you feed <code>hx</code> to a lemma." },
        { "tac": "· subst hx; rw [hl, singleton_same]",
          "h": "<code>subst</code> eliminates <code>l</code>, replacing it by <code>x</code> everywhere — not the other way round; see the trace. Then <code>rw [hl]</code> makes the left side <code>some v</code> and <code>singleton_same</code> makes the right side <code>some v</code>." },
        { "tac": "· rw [singleton_other l x v hx]",
          "h": "Deal with the right side first: away from <code>l</code>, a singleton is <code>none</code>, so the goal becomes <code>h x = none</code>. <code>singleton_other</code> wants exactly <code>x ≠ l</code> in that order, and <code>hx</code> has it." },
        { "tac": "have := congrFun hrest x",
          "h": "<code>hrest</code> is an equation between functions; apply both sides at <code>x</code>. This is the only line that uses it, and it spends it." },
        { "tac": "rw [erase_other h l x hx] at this",
          "h": "Away from <code>l</code>, erasing changes nothing, so <code>this</code> becomes <code>h x = Heap.empty x</code>." },
        { "tac": "exact this",
          "h": "The goal is <code>h x = none</code>, and <code>Heap.empty x</code> beta-reduces to <code>none</code>. Nothing to rewrite; only to reduce." },
        { "tac": "theorem wp_free_emp (l : Loc) : wp (.free l) emp ⊣⊢ aExists (fun v => l ↦ v) := by",
          "h": "The theorem itself. Everything hard is already done." },
        { "tac": "· intro σ h ⟨s', hex, he⟩",
          "h": "<code>he</code> is <code>emp</code> at the final state; <code>hex</code> is the run of <code>free l</code>." },
        { "tac": "cases hex with | free hl =>",
          "h": "One branch. <code>hl</code> is the constructor’s side condition, at a value Lean names <code>v✝</code> because <code>Exec.free</code>’s <code>{v}</code> binder is implicit." },
        { "tac": "refine ⟨_, heap_eq_singleton hl ?_⟩",
          "h": "The goal is <code>∃ v, h = Heap.singleton l v</code>. You cannot type <code>v✝</code>, so write <code>_</code>; unification reads the witness off <code>hl</code>. The second argument of <code>heap_eq_singleton</code> is deferred as a hole." },
        { "tac": "exact he",
          "h": "The hole has type <code>Heap.erase h l = Heap.empty</code>, and <code>he</code> is that once <code>emp</code> is unfolded and the state projections reduced." },
        { "tac": "· intro σ h ⟨v, hp⟩",
          "h": "Backwards. <code>hp</code> is <code>(fun v => l ↦ v) v σ h</code>, which under the beta-redex is <code>h = Heap.singleton l v</code>." },
        { "tac": "subst hp",
          "h": "Eliminate <code>h</code> in favour of <code>Heap.singleton l v</code>. <code>subst</code> reaches the equation through the beta-redex and the folded <code>pointsTo</code> without help." },
        { "tac": "exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v), erase_singleton l v⟩",
          "h": "The state after freeing, the constructor with its side condition discharged by <code>singleton_same</code>, and the <code>emp</code> discharged by <code>erase_singleton</code>. Nothing here is a choice." }
      ],

      "deep": [
        { "t": "trace",
          "title": "heap_eq_singleton, tactic by tactic",
          "start": "h : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\n⊢ h = Heap.singleton l v",
          "steps": [
            { "tac": "funext x",
              "state": "h : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\n⊢ h x = Heap.singleton l v x",
              "h": "Both sides applied to <code>x</code>. <code>hrest</code> prints as <code>h.erase l</code>: the printer prefers generalised field notation on output regardless of what you wrote." },
            { "tac": "by_cases hx : x = l",
              "state": "case pos\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : x = l\n⊢ h x = Heap.singleton l v x",
              "h": "The first of two goals." },
            { "tac": "subst hx",
              "state": "case pos\nh : Heap\nv : Val\nx : Loc\nhl : h x = some v\nhrest : h.erase x = Heap.empty\n⊢ h x = Heap.singleton x v x",
              "h": "Read this carefully: <code>l</code> has <b>disappeared</b> and <code>x</code> is everywhere. With <code>hx : x = l</code> between two local variables, <code>subst</code> may eliminate either, and here it took <code>l</code>. The following <code>rw [hl, singleton_same]</code> works precisely because <code>hl</code> is now stated at <code>x</code>." },
            { "tac": "rw [hl, singleton_same]",
              "state": "No goals.",
              "h": "Two rewrites in one bracket, applied left to right; <code>rw</code>’s trailing <code>rfl</code> closes what is left." },
            { "tac": "(second branch) rw [singleton_other l x v hx]",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : ¬x = l\n⊢ h x = none",
              "h": "The right-hand side is gone. What remains is: show <code>h</code> is empty away from <code>l</code>. That is what <code>hrest</code> says, but <code>hrest</code> is about <i>functions</i> and the goal is about a value." },
            { "tac": "have := congrFun hrest x",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : ¬x = l\nthis : h.erase l x = Heap.empty x\n⊢ h x = none",
              "h": "The pointwise version of <code>hrest</code>, and the last thing this proof learns; both remaining lines only reshape it." },
            { "tac": "rw [erase_other h l x hx] at this",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nhl : h l = some v\nhrest : h.erase l = Heap.empty\nx : Loc\nhx : ¬x = l\nthis : h x = Heap.empty x\n⊢ h x = none",
              "h": "All four explicit arguments of <code>erase_other</code> are supplied so there is no ambiguity about which <code>erase</code> is being rewritten." },
            { "tac": "exact this",
              "state": "No goals." }
          ],
          "done": "No goals." },

        { "t": "trace",
          "title": "wp_free_emp, forwards and backwards",
          "start": "case left\nl : Loc\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.free l) { store := σ, heap := h } s'\nhe : emp s'.store s'.heap\n⊢ aExists (fun v => l ↦ v) σ h",
          "steps": [
            { "tac": "cases hex with | free hl =>",
              "state": "case left.free\nl : Loc\nσ : Store\nh : Heap\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhe :\n  emp { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap\n⊢ aExists (fun v => l ↦ v) σ h",
              "h": "Two inaccessible things at once. <code>v✝</code> is the stored value, implicit in <code>Exec.free</code>, hence the <code>_</code> on the next line. And <code>hl</code>’s type is printed unreduced even though <code>heap_eq_singleton</code> wants <code>h l = some v✝</code> — it is accepted anyway, because the projection reduces." },
            { "tac": "refine ⟨_, heap_eq_singleton hl ?_⟩",
              "state": "case left.free\nl : Loc\nσ : Store\nh : Heap\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhe :\n  emp { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap\n⊢ h.erase l = Heap.empty",
              "h": "The goal left behind is <code>heap_eq_singleton</code>’s <code>hrest</code> argument, and Lean has <b>reduced it for us</b>. Meanwhile <code>he</code> is still displayed in full. Same proposition: unfolding <code>emp</code> gives <code>(state).heap = Heap.empty</code>, and that state’s heap is <code>h.erase l</code>." },
            { "tac": "exact he",
              "state": "No goals.",
              "h": "A hypothesis sharing no visible structure with the goal closes it exactly." },
            { "tac": "intro σ h ⟨v, hp⟩",
              "state": "case right\nl : Loc\nσ : Store\nh : Heap\nv : Val\nhp : (fun v => l ↦ v) v σ h\n⊢ wp (Cmd.free l) emp σ h",
              "h": "<code>hp</code> displays as an unreduced beta-redex; Lean does not beta-reduce hypothesis types for display." },
            { "tac": "subst hp",
              "state": "case right\nl : Loc\nσ : Store\nv : Val\n⊢ wp (Cmd.free l) emp σ (Heap.singleton l v)",
              "h": "<code>h</code> is gone. The goal is now completely concrete and can be discharged by supplying a run." },
            { "tac": "exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, Exec.free (singleton_same l v), erase_singleton l v⟩",
              "state": "No goals.",
              "h": "Every component is forced, which is the sign that you have the right lemmas." }
          ],
          "done": "No goals." },

        { "t": "steps",
          "title": "Where the existential came from",
          "items": [
            { "k": "The run requires a value",
              "h": "<code>Exec.free</code> requires <code>h l = some v</code> for <i>some</i> <code>v</code>, quantified implicitly by the constructor. Nothing constrains which." },
            { "k": "The postcondition requires a heap",
              "h": "<code>Heap.erase h l = Heap.empty</code>. Combined with the previous point, <code>heap_eq_singleton</code> gives <code>h = Heap.singleton l v</code>." },
            { "k": "Collect",
              "h": "So the precondition is <code>∃ v, h = Heap.singleton l v</code>. The existential is inherited from the constructor’s implicit argument. It is not a stylistic choice; it is where the value went." }
          ] },

        { "t": "detail", "title": "The general <code>wp</code> of <code>free</code>, and why it is shorter", "tag": "aside", "open": false,
          "blocks": [
            { "t": "p",
              "h": "<code>wp_free_emp</code> is the case <code>Q := emp</code> of a general equation, and the general one takes six tactic lines against seventeen." },
            { "t": "code", "tag": "illustration",
              "src": "theorem wp_free (l : Loc) (Q : Assertion) :\n    wp (.free l) Q ⊣⊢\n      aExists (fun v => aAnd (fun _ h => h l = some v)\n                             (fun σ h => Q σ (Heap.erase h l))) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | free hl => rename_i v; exact ⟨v, hl, hq⟩\n  · intro σ h ⟨v, hl, hq⟩\n    exact ⟨⟨σ, Heap.erase h l⟩, Exec.free hl, hq⟩" },
            { "t": "p",
              "h": "All of <code>heap_eq_singleton</code> exists to convert that answer into the points-to language. <i>Stating</i> a weakest precondition in separation-logic vocabulary is real work over and above computing it, and that translation step is where a tool like Iris spends most of its effort." }
          ] }
      ],

      "pitfall": "Reaching for <code>rw [hrest]</code> instead of <code>congrFun hrest x</code>. After <code>funext x</code> the goal contains <code>h x</code>, not <code>Heap.erase h l</code>, so there is nothing to match and <code>rw</code> fails with “did not find an occurrence of the pattern”. Once you have gone pointwise, function-level equations must come pointwise too. The second trap is in the positive branch: after <code>subst hx</code> the surviving variable is <code>x</code>, so a proof written as <code>rw [singleton_same l v]</code> fails with an unknown identifier.",

      "variants": "Drop <code>hrest</code> from <code>heap_eq_singleton</code> and it is plainly false: <code>h</code> could hold a cell elsewhere, and singletons are exact ownership. Drop <code>hl</code> instead and it is false at exactly one point — the empty heap satisfies <code>Heap.erase h l = Heap.empty</code> and is no singleton. That single point is the safety content of the free rule: without <code>hl</code> the cell was never shown to be allocated, and <code>free</code> on an unallocated cell has no derivation at all. Now replace the postcondition <code>emp</code> by <code>aTrue</code>: the forward direction collapses, because all you can conclude is <code>∃ v, h l = some v</code> — ownership of a cell inside a possibly larger heap, which <code>↦</code> alone cannot express. That is why the exercise fixes <code>Q := emp</code>."
    },

    { "t": "ex",
      "id": "m12-5",
      "name": "wp_write",
      "hard": true,

      "why": "Same shape, and now the gap is visible. You must own the cell; its previous contents are irrelevant. The hand-written precondition <code>l ↦ old</code> for a fixed <code>old</code> is <i>sufficient</i> and not <i>weakest</i>, because it pins down a value nothing reads. This is where the difference between a specification that works and the specification stops being a slogan.",
      "setup": "Same toolkit as m12-4 with <code>Heap.write</code> in place of <code>Heap.erase</code>: <code>write_other</code>, <code>write_singleton</code>, <code>singleton_same</code>, <code>singleton_other</code>. The command is <code>.write l (.const new)</code>, a literal, so <code>e.eval σ</code> is <code>new</code> whatever the store and the exercise is about the heap only.",
      "goal": "theorem wp_write (l : Loc) (new : Val) :\n    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old)",

      "hints": [
        "Forwards is m12-4’s argument with a different final heap: you learn <code>h l = some old</code> from the derivation and <code>Heap.write h l new = Heap.singleton l new</code> from the postcondition, and must conclude <code>h = Heap.singleton l old</code>.",
        "You cannot reuse <code>heap_eq_singleton</code> — its second hypothesis is about <code>erase</code>. Run the <code>funext</code> / <code>by_cases</code> argument inline. Away from <code>l</code>, <code>write_other</code> and <code>singleton_other</code> both deliver <code>none</code>.",
        "Restate the hypotheses before rewriting with them. <code>hl</code> displays as <code>{ store := σ, heap := h }.heap l = some old</code>, and <code>rw</code> matches syntax, so it will not fire. <code>have hl' : h l = some old := hl</code> costs nothing.",
        "The value is an inaccessible <code>old✝</code> after <code>cases hex with | write hl =&gt;</code>, and you need to <i>name</i> it, because it is the witness of the existential you are building. <code>rename_i old</code>.",
        "Forwards: from <code>Heap.write h l new = Heap.singleton l new</code> and <code>h l = some old</code>, show <code>h = Heap.singleton l old</code> by <code>funext</code>; away from <code>l</code>, <code>write_other</code> and <code>singleton_other</code> both give <code>none</code>."
      ],

      "sol": "theorem wp_write (l : Loc) (new : Val) :\n    wp (.write l (.const new)) (l ↦ new) ⊣⊢ aExists (fun old => l ↦ old) := by\n  constructor\n  · intro σ h ⟨s', hex, hq⟩\n    cases hex with\n    | write hl =>\n        rename_i old\n        refine ⟨old, ?_⟩\n        have hl' : h l = some old := hl\n        have hq' : Heap.write h l new = Heap.singleton l new := hq\n        funext x\n        by_cases hx : x = l\n        · subst hx; rw [hl', singleton_same]\n        · rw [singleton_other l x old hx]\n          have := congrFun hq' x\n          rw [write_other h l x new hx, singleton_other l x new hx] at this\n          exact this\n  · intro σ h ⟨old, hp⟩\n    subst hp\n    exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩,\n           Exec.write (singleton_same l old), write_singleton l old new⟩",

      "expl": "The two <code>have</code> lines are the whole difficulty, and they are not mathematics. Everything else is m12-4 again. Once the theorem is proved, ask the same question of <code>copyCell</code>: is <code>src ↦ a ∗ dst ↦ b</code> weakest? It is not — <code>b</code> is never read. Naming values a program does not read is the commonest way a hand-written specification comes out stronger than it needs to be, and it is exactly what makes it fail to compose.",

      "walk": [
        { "tac": "constructor",
          "h": "Two entailments." },
        { "tac": "· intro σ h ⟨s', hex, hq⟩",
          "h": "<code>hq</code> is <code>l ↦ new</code> at the final state — an equation saying the post-heap is exactly <code>Heap.singleton l new</code>." },
        { "tac": "cases hex with | write hl =>",
          "h": "<code>Exec.write</code>’s side condition <code>hl : s.heap l = some old</code> for an implicit <code>old</code>." },
        { "tac": "rename_i old",
          "h": "That value arrived as <code>old✝</code>. Naming it is required here, unlike in m12-4 where <code>_</code> sufficed, because unification cannot recover it: it is the witness you are choosing, and the goal gives no clue what it should be until the equation is proved." },
        { "tac": "refine ⟨old, ?_⟩",
          "h": "Commit to the witness. The remaining goal is <code>h = Heap.singleton l old</code>." },
        { "tac": "have hl' : h l = some old := hl",
          "h": "A restatement of <code>hl</code> at the type you wish it had. What lands in the context is the same proof, at a type <code>rw</code> can match." },
        { "tac": "have hq' : Heap.write h l new = Heap.singleton l new := hq",
          "h": "The same move on the postcondition, doing far more: unfolding <code>pointsTo</code>, reducing the state projections, and evaluating <code>Atom.eval σ (Atom.const new)</code> to <code>new</code>. Compare the displayed type of <code>hq</code> in the trace — it is six lines." },
        { "tac": "funext x",
          "h": "A heap equation, so go pointwise." },
        { "tac": "by_cases hx : x = l",
          "h": "Split at the written location." },
        { "tac": "· subst hx; rw [hl', singleton_same]",
          "h": "At <code>x = l</code>, <code>hl'</code> says <code>h x = some old</code> and the singleton agrees. This branch never mentions <code>new</code>: what was written is irrelevant to what was there." },
        { "tac": "· rw [singleton_other l x old hx]",
          "h": "Away from <code>l</code>, the right side is <code>none</code>, so the goal is <code>h x = none</code>." },
        { "tac": "have := congrFun hq' x",
          "h": "Bring the post-heap equation pointwise. This is where <code>hq'</code> rather than <code>hq</code> matters: <code>congrFun hq x</code> also elaborates, but produces the unreduced form, which the next rewrite cannot match." },
        { "tac": "rw [write_other h l x new hx, singleton_other l x new hx] at this",
          "h": "Left side: away from <code>l</code>, writing changed nothing, so it is <code>h x</code>. Right side: the singleton is <code>none</code>." },
        { "tac": "exact this",
          "h": "This branch is the whole non-aliasing content of the proof: the only reason the untouched part of <code>h</code> is empty is that the post-heap was a singleton and writing created nothing elsewhere." },
        { "tac": "· intro σ h ⟨old, hp⟩",
          "h": "Backwards. <code>old</code> is an ordinary named variable now, because it came from an existential in a hypothesis rather than from a constructor." },
        { "tac": "subst hp",
          "h": "Replace <code>h</code> by <code>Heap.singleton l old</code>; the goal becomes fully concrete." },
        { "tac": "exact ⟨⟨σ, Heap.write (Heap.singleton l old) l new⟩, Exec.write (singleton_same l old), write_singleton l old new⟩",
          "h": "<code>write_singleton l old new : Heap.write (Heap.singleton l old) l new = Heap.singleton l new</code> is exactly <code>l ↦ new</code> at that heap. An M1 lemma is doing the separation-logic work." }
      ],

      "deep": [
        { "t": "note", "kind": "info", "title": "How to read the trace below",
          "h": "<code>hl</code> and <code>hq</code> arrive unreduced from <code>cases</code> and then sit untouched for the rest of the proof — twelve lines of context that never change. They are printed in full once, because that display <i>is</i> the point of the exercise; after that they are abbreviated <code>hl : ⋯</code> and <code>hq : ⋯</code>. Everything else below is Lean’s own output, unedited." },

        { "t": "trace",
          "title": "wp_write, forwards — and why the two haves exist",
          "start": "case left\nl : Loc\nnew : Val\nσ : Store\nh : Heap\ns' : State\nhex : Exec (Cmd.write l (Atom.const new)) { store := σ, heap := h } s'\nhq : (l ↦ new) s'.store s'.heap\n⊢ aExists (fun old => l ↦ old) σ h",
          "steps": [
            { "tac": "cases hex with | write hl =>",
              "state": "case left.write\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhq :\n  (l ↦ new)\n    { store := { store := σ, heap := h }.store,\n        heap :=\n          { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store (Atom.const new)) }.store\n    { store := { store := σ, heap := h }.store,\n        heap :=\n          { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store (Atom.const new)) }.heap\n⊢ aExists (fun old => l ↦ old) σ h",
              "h": "The state that justifies the rest of the proof. <code>hq</code> is six lines in which nothing has been reduced: the state is a literal, its projections are unevaluated, and <code>Atom.eval … (Atom.const new)</code> has not become <code>new</code>. Lean is happy to <i>use</i> this hypothesis. It is <code>rw</code> that will not." },
            { "tac": "rename_i old",
              "h": "Renames <code>old✝</code>. Without it you cannot write the witness on the next line, and unification cannot supply it either." },
            { "tac": "refine ⟨old, ?_⟩",
              "h": "The goal becomes <code>(fun old => l ↦ old) old σ h</code>, the beta-redex left unreduced in the display as always. Underneath it is <code>h = Heap.singleton l old</code>." },
            { "tac": "have hl' : h l = some old := hl",
              "h": "The smaller of the two restatements: only one state projection has to disappear." },
            { "tac": "have hq' : Heap.write h l new = Heap.singleton l new := hq",
              "state": "case left.write\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\n⊢ (fun old => l ↦ old) old σ h",
              "h": "Three reductions happen inside the definitional-equality check and none is reported: <code>pointsTo</code> unfolds, the state projections evaluate, and <code>Atom.eval σ (Atom.const new)</code> becomes <code>new</code>." },
            { "tac": "funext x  ·  by_cases hx : x = l  ·  (negative branch)",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\n⊢ h x = Heap.singleton l old x",
              "h": "The positive branch is two rewrites and closes at once; the negative branch is where the content is." },
            { "tac": "rw [singleton_other l x old hx]",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\n⊢ h x = none",
              "h": "Right-hand side dispatched." },
            { "tac": "have := congrFun hq' x",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\nthis : h.write l new x = Heap.singleton l new x\n⊢ h x = none",
              "h": "Compare what <code>congrFun hq x</code> would give: the whole unreduced state, still in the way." },
            { "tac": "rw [write_other h l x new hx, singleton_other l x new hx] at this",
              "state": "case neg\nl : Loc\nnew : Val\nσ : Store\nh : Heap\nold : Val\nhl : ⋯\nhq : ⋯\nhl' : h l = some old\nhq' : h.write l new = Heap.singleton l new\nx : Loc\nhx : ¬x = l\nthis : h x = none\n⊢ h x = none",
              "h": "Both sides simplified away from <code>l</code>. <code>exact this</code> finishes." }
          ],
          "done": "No goals." },

        { "t": "cmp",
          "left": {
            "t": "Without the restatements",
            "kind": "bad",
            "h": "Both rewrites fail, naming patterns you never wrote. This is the single commonest way to get stuck in this exercise, and it is not a mathematical difficulty at all.",
            "tag": "sketch",
            "src": "· subst hx; rw [hl, singleton_same]\n-- error: Tactic `rewrite` failed: Did not find an\n--   occurrence of the pattern\n--     { store := σ, heap := h }.heap x\n--   in the target expression\n--     h x = Heap.singleton x old x\n\n  have := congrFun hq x\n  rw [write_other h l x new hx, …] at this\n-- error: Tactic `rewrite` failed: Did not find an\n--   occurrence of the pattern\n--     h.write l new x"
          },
          "right": {
            "t": "With them",
            "kind": "good",
            "h": "Two lines that prove nothing and enable everything. Read them as “re-elaborate this hypothesis at the type I want”: the definitional-equality check does the reducing, and what lands in the context is syntactically usable.",
            "tag": "sketch",
            "src": "have hl' : h l = some old := hl\nhave hq' : Heap.write h l new\n             = Heap.singleton l new := hq"
          } },

        { "t": "steps",
          "title": "Is <code>l ↦ old</code> weakest? No, and one heap says so",
          "items": [
            { "k": "It is sufficient",
              "h": "For any fixed <code>old</code>, <code>l ↦ old</code> entails the computed precondition by supplying <code>old</code> as the witness. The M7 rule is sound; nothing is wrong with it." },
            { "k": "It is not necessary",
              "h": "Take <code>old := 0</code>. The heap <code>Heap.singleton l 1</code> satisfies the weakest precondition — the write succeeds and lands in <code>l ↦ new</code> — and does not satisfy <code>l ↦ 0</code>." },
            { "k": "In Lean",
              "h": [
                { "t": "code", "tag": "illustration",
                  "src": "-- sufficient: any fixed `old` entails the weakest precondition\nexample (l : Loc) (old new : Val) :\n    (l ↦ old) ⊢ wp (.write l (.const new)) (l ↦ new) :=\n  fun σ h hp => (wp_write l new).2 σ h ⟨old, hp⟩\n\n-- but not necessary: `l ↦ 0` is strictly stronger\nexample (l : Loc) (new : Val) :\n    ¬ (wp (.write l (.const new)) (l ↦ new) ⊢ (l ↦ 0)) := by\n  intro hcontra\n  have h1 : (l ↦ 1) ⊢ wp (.write l (.const new)) (l ↦ new) :=\n    fun σ hh hp => (wp_write l new).2 σ hh ⟨1, hp⟩\n  have h2 := hcontra (fun _ => 0) (Heap.singleton l 1)\n    (h1 (fun _ => 0) (Heap.singleton l 1) rfl)\n  have heq : Heap.singleton l 1 l = Heap.singleton l 0 l := by rw [h2]\n  rw [singleton_same, singleton_same] at heq\n  exact absurd (Option.some.inj heq) (by simp)" }
              ] },
            { "k": "Why it matters downstream",
              "h": "A precondition naming a value it never uses does not compose. If a caller owns <code>l ↦ 7</code> and your specification says <code>l ↦ 0</code>, the caller must first rewrite the specification or prove <code>7 = 0</code>. Quantifying the unread value is what makes the rule apply on the first attempt every time." }
          ] },

        { "t": "note", "kind": "tip", "title": "A test you can run on any specification you write",
          "h": "For each value named in the precondition, ask whether the program <i>reads</i> it. If not, it should be existentially quantified. Run this on <code>copyCell_spec</code> from M9 — precondition <code>src ↦ a ∗ dst ↦ b</code> — and <code>b</code> fails at once: <code>copyCell</code> writes to <code>dst</code> and never loads from it. The weakest precondition is <code>src ↦ a ∗ (∃ b, dst ↦ b)</code>." }
      ],

      "pitfall": "Skipping <code>have hq' : … := hq</code> and calling <code>congrFun hq x</code> directly. It elaborates, but the hypothesis it produces still carries the unreduced state, so the next line fails with <code>Did not find an occurrence of the pattern h.write l new x</code> — an error naming a pattern that <i>is</i>, semantically, the term you are looking at. When a hypothesis comes out of <code>cases</code> and you intend to rewrite with it, restate it first. The mirror-image mistake is in the positive branch: <code>subst hx</code> eliminates <code>l</code> and keeps <code>x</code>, so afterwards the identifier <code>l</code> does not exist and <code>rw [singleton_same l old]</code> fails with <code>Unknown identifier `l`</code>. That is why the solution’s positive branch supplies no explicit arguments at all.",

      "variants": "Replace the postcondition <code>l ↦ new</code> by <code>aTrue</code> and the forward direction becomes false: a successful write yields only <code>∃ old, h l = some old</code>, which does not pin <code>h</code> to a singleton. Replace it by <code>(l ↦ new) ∗ R</code> for a fixed <code>R</code> and you get the framed version, which is <code>wp_frame</code> plus this exercise rather than a new proof. Strengthen the right-hand side to <code>l ↦ old</code> for a fixed <code>old</code> and ⟸ still holds while ⟹ fails, at the single heap <code>Heap.singleton l v</code> for any <code>v ≠ old</code>. Finally, change the command’s argument from <code>.const new</code> to <code>.var y</code>: the forward direction now carries <code>Atom.eval σ (.var y)</code> where it had <code>new</code>, <code>have hq'</code> no longer reduces to a constant, and you need a pure side condition <code>σ y = new</code> — which is exactly why M9 introduced <code>hoare_write_val</code>."
    },

    { "t": "sec", "s": "What the calculus buys, and where it stops" },

    { "t": "ul",
      "items": [
        "<b>The program vanishes halfway through.</b> Once the fold has run, nothing is left but two assertions and an entailment between them, and no rule of the program logic is involved in discharging it. Phase 1 was the preparation for that second half.",
        "<b>The frame rule needs no triple.</b> <code>wp c Q ∗ R ⊢ wp c (Q ∗ R)</code> is <code>hoare_frame</code> at the best possible triple, whose proof is <code>entails_refl</code>. The M8 side conditions still carry all the content.",
        "<b>“Is my specification honest?” is checkable.</b> If <code>Hoare P c Q</code> is provable at all then <code>P ⊢ wp c Q</code>, with no proof required, so whether <code>P</code> was stronger than it needed to be is a question about a single entailment rather than a matter of taste."
      ] },

    { "t": "note", "kind": "warn", "title": "Where the equations run out",
      "h": "There is no equation for <code>loop</code>. <code>wp (.loop b c) Q</code> is the <b>least</b> <code>X</code> satisfying <code>X ⊣⊢ (b ∧ wp c X) ∨ (¬b ∧ Q)</code>, and a fixed point is not something a fold over syntax produces. Everything else in this chapter was mechanical. This is the one place where mathematics is required." },

    { "t": "detail", "title": "Least, not greatest — and the loop that shows the difference", "tag": "aside", "open": false,
      "blocks": [
        { "t": "p",
          "h": "Which fixed point is not a matter of taste, and it is easy to get backwards. <code>Exec</code> is an <code>inductive</code> relation, so a run is a <i>finite</i> derivation tree and <code>wp</code>’s <code>∃ s'</code> therefore asserts termination. That forces the <b>least</b> fixed point. The greatest one is what partial correctness gets, where a non-terminating run satisfies everything vacuously; the literature writes it <code>wlp</code>." },
        { "t": "p",
          "h": "The smallest witness that they differ is M6’s <code>forever</code>. Its loop equation degenerates to <code>X ⊣⊢ X</code>, which <i>every</i> assertion solves. The least solution is <code>aFalse</code> — no state at all, because no run terminates. The greatest is <code>aTrue</code>, which would certify a program that never returns." },
        { "t": "code", "tag": "illustration",
          "cap": "compiles against the M12 prelude; forever and no_exec_forever are M6’s, repeated so the snippet stands alone",
          "src": "def forever : Cmd := .loop (.equals (.const 0) (.const 0)) .skip\n\ntheorem no_exec_forever : ∀ {c : Cmd} {s s' : State}, c = forever → Exec c s s' → False := by\n  intro c s s' hc hex\n  induction hex with\n  | loopFalse hb => cases hc; simp [BExpr.eval, Atom.eval] at hb\n  | loopTrue hb hbody hrest ihb ihr => exact ihr hc\n  | _ => cases hc\n\n-- the loop equation for `forever`, with X the unknown assertion\ndef loopEqn (Q X : Assertion) : Assertion :=\n  aOr (aAnd (fact (fun σ => BExpr.eval σ (.equals (.const 0) (.const 0)) = true))  (wp .skip X))\n      (aAnd (fact (fun σ => BExpr.eval σ (.equals (.const 0) (.const 0)) = false)) Q)\n\n-- `wp forever Q` is `aFalse`: no run terminates, so nothing satisfies it.\ntheorem wp_forever (Q : Assertion) : wp forever Q ⊣⊢ aFalse := by\n  constructor\n  · intro σ h ⟨s', hex, _⟩\n    exact (no_exec_forever rfl hex).elim\n  · intro σ h hf\n    exact hf.elim\n\n-- `aFalse` does solve the equation …\ntheorem aFalse_solves (Q : Assertion) : aFalse ⊣⊢ loopEqn Q aFalse := by\n  constructor\n  · intro σ h hf; exact hf.elim\n  · intro σ h hx\n    cases hx with\n    | inl hl => obtain ⟨_, _, _, hf⟩ := hl; exact hf\n    | inr hr =>\n        have hb : BExpr.eval σ (.equals (.const 0) (.const 0)) = false := hr.1\n        simp [BExpr.eval, Atom.eval] at hb\n\n-- … but so does `aTrue`, and `aTrue` is not `wp forever Q`.\ntheorem aTrue_solves (Q : Assertion) : aTrue ⊣⊢ loopEqn Q aTrue := by\n  constructor\n  · intro σ h _\n    exact Or.inl ⟨rfl, ⟨σ, h⟩, Exec.skip, trivial⟩\n  · intro σ h _\n    trivial" },
        { "t": "p",
          "h": "Two assertions, both solving the equation, and only one of them is <code>wp forever Q</code>. So the equation alone does not determine the transformer; you have to say which solution, and total correctness says the least." }
      ] },

    { "t": "p",
      "h": "What a loop verification starts from, then, is an assertion you hand over. Nothing so far says what makes one adequate — still less what makes one adequate for a loop that is obliged to stop. M13 starts there." },

    { "t": "dod",
      "h": "You can move freely between forward Hoare reasoning and backward weakest-precondition calculation, and you can tell whether a precondition you wrote is genuinely the weakest one." }
  ]
});
