/* M13 — Loops, invariants, and termination
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m13",
  "num": "M13",
  "phase": "Phase 3 · Advanced separation logic",
  "title": "Loops, invariants, and termination",
  "blurb": "Partial versus total correctness, the invariant rule, and a decreasing variant.",

  "orient": {
    "youWill": [
      `Read the invariant rule off the semantics and see which of the two triples it is able to conclude — with the loop that makes the difference load-bearing.`,
      `Prove the structural rules again in the partial reading, where a derivation is an argument you take apart rather than a result you build.`,
      `Prove the while rule by induction on an <code>Exec</code> derivation, generalising the command and pinning it with an equation.`,
      `Add a <b>variant</b> — a <code>Nat</code> that falls by one on every iteration — and turn the partial argument into a total triple.`,
      `Verify <code>while x ≠ 0 do x := x - 1</code> end to end, and read the goal Lean leaves behind when a program's variant does not fall by exactly one.`
    ],
    "needs": [
      `<code>Exec</code>'s two loop constructors, <code>loopFalse</code> and <code>loopTrue</code>, and the habit of inverting a derivation with <code>cases … with</code> or inducting on one with <code>induction … with</code>.`,
      `<code>PartialHoare</code> from M6, and the two commands there that have no derivations at all — the faulting load and <code>forever</code>.`,
      `<code>aAnd</code> and <code>aExists</code>, and the anonymous constructor in both of its roles, since every proof here either builds one or destructures one.`
    ],
    "payoff": `Two moves verify every loop anybody has ever verified: an assertion that survives one iteration, and a quantity that shrinks. Here they are theorems rather than slogans, and the gap between them is a program for which the first is provable and the second is false.`
  },

  "blocks": [
    {
      "t": "h3",
      "s": "Adequate for one iteration"
    },
    {
      "t": "p",
      "h": `The assertion has a name — an <b>invariant</b> — and one condition makes it adequate. Run the body once from a state satisfying it, knowing the guard was true, and land back in it. Nothing about the loop as a whole is asked for.`
    },
    {
      "t": "txt",
      "src": `       { I ∧ b } body { I }
  ───────────────────────────────────
   { I } loop b body { I ∧ ¬b }`
    },
    {
      "t": "p",
      "h": `You may assume the guard above the line because the body only ever runs when it holds. Below the line you are given the invariant back <i>and</i> the negated guard, and the second conjunct is usually where the useful content is: <code>i ≤ n</code> together with <code>¬ (i ≠ n)</code> is <code>i = n</code>. Establishing <code>I</code> on entry is not part of the rule at all — it is an entailment you feed to <code>partialHoare_consequence</code>, and it is where most of the design work goes, because <code>I</code> has to be weak enough to hold before the first test and strong enough to be worth anything after the last.`
    },
    {
      "t": "p",
      "h": `Now put <code>Hoare</code> in the brackets and the rule is false. Take <code>I := aTrue</code>, the guard <code>0 == 0</code>, and <code>.skip</code> for the body. The premise holds — <code>skip</code> preserves <code>aTrue</code> — and the conclusion would assert that <code>forever</code> reaches a final state. <code>no_exec_forever</code> says it reaches none.`
    },
    {
      "t": "note",
      "kind": "key",
      "title": "What the premise cannot see",
      "h": `The premise is about <i>an</i> iteration. Nothing in it counts iterations, and nothing in it could: it mentions the body and the guard, and neither of those knows how many times it will be reached. So the rule concludes a <code>PartialHoare</code>, and the promotion to <code>Hoare</code> has to be bought separately.`
    },
    {
      "t": "p",
      "h": `Promotion is what costs. The demotion is free, and it is the only theorem in this workbook that spends <code>exec_deterministic</code>:`
    },
    {
      "t": "code",
      "src": `theorem partial_of_total {P Q : Assertion} {c : Cmd}
    (h : Hoare P c Q) : PartialHoare P c Q := by
  intro σ hh s' hp hex
  obtain ⟨s'', hex'', hq⟩ := h σ hh hp
  have : s' = s'' := exec_deterministic hex hex''
  rw [this]; exact hq`
    },
    {
      "t": "detail",
      "title": "Where that hypothesis is about to be taken away",
      "tag": "design",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": `Determinism is not decoration here. Without it <code>Hoare P c Q</code> promises only that <i>some</i> run lands in <code>Q</code>, while a partial triple constrains <i>every</i> run, and a command with one good run and one bad one satisfies the first and refutes the second.`
        },
        {
          "t": "p",
          "h": `M14 adds nondeterministic allocation, and <code>exec_deterministic</code> is the first casualty. <code>partial_of_total</code> goes with it. The repair there is to change what <code>Hoare</code> means — to quantify over runs rather than exhibit one — not to patch this proof.`
        }
      ]
    },
    {
      "t": "p",
      "h": `Before any of this is a Lean statement the guard has to become an assertion, since <code>b.eval σ</code> is a <code>Bool</code> and a precondition is an <code>Assertion</code>:`
    },
    {
      "t": "code",
      "src": `def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true

def bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false`
    },
    {
      "t": "p",
      "h": `Two things follow from writing the rule's precondition as <code>aAnd I (bTrue b)</code> rather than as an inline <code>fun σ h => I σ h ∧ b.eval σ = true</code>. Every entailment lemma from Phase 1 applies to it unchanged — <code>and_left</code>, <code>and_intro</code>, <code>star_pure_left</code> know nothing about <code>bTrue</code> and need to know nothing. And <code>bTrue b σ h</code> is definitionally <code>b.eval σ = true</code>, which is exactly the field an inverted <code>Exec</code> hands back, so the pair <code>⟨hp, hb⟩</code> typechecks with no coercion. The next two exercises use both facts.`
    },
    {
      "t": "detail",
      "title": "Guards read the store and never the heap",
      "tag": "design",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": `Both definitions ignore their heap argument, because <code>BExpr</code> cannot dereference: there is no <code>[l] == 0</code>. That is a real loss of expressiveness, bought deliberately.`
        },
        {
          "t": "p",
          "h": `Suppose a guard could read a cell. Then <code>bTrue b</code> would no longer be constant in its heap, and framing a loop would need the frame to leave that cell alone — the argument of M8's <code>Preserves</code>, now attached to every loop rather than to a command that writes. Keeping guards pure is what makes them invisible to the frame rule.`
        }
      ]
    },
    {
      "t": "sec",
      "s": "Everything else, in the partial reading"
    },
    {
      "t": "p",
      "h": `The invariant rule alone proves nothing about a program; the rest of the calculus has to hold in the same reading. Restating it turns on a single observation.`
    },
    {
      "t": "cmp",
      "left": {
        "t": "M6 · <code>Hoare</code>",
        "h": `The execution is <b>output</b>. Every proof ends by exhibiting a final state and a derivation reaching it, which is why every M6 proof bottoms out in <code>exact ⟨…, Exec.something, …⟩</code>.`,
        "src": `∀ σ h, P σ h →
  ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap`
      },
      "right": {
        "t": "M13 · <code>PartialHoare</code>",
        "h": `The execution is <b>input</b>. Every proof begins by destructing a derivation somebody else supplied. No <code>Exec</code> constructor appears anywhere in the next two exercises; if you type one, you have taken a wrong turn.`,
        "src": `∀ σ h s', P σ h →
  Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap`
      }
    },
    {
      "t": "ex",
      "id": "m13-1",
      "name": "partialHoare_skip / seq / consequence",
      "hard": false,
      "why": `Three at a sitting, because it is one change three times. What is used from <code>P</code> and how <code>Q</code> is discharged are untouched from M6; only <code>Exec</code> has changed sides.`,
      "setup": `<code>PartialHoare</code>, <code>Entails</code> and <code>Exec</code> are in scope. You will not need a single <code>Exec</code> constructor.`,
      "goal": "theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P\n\ntheorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R\n\ntheorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :\n    PartialHoare P' c Q'",
      "hints": [
        `All three open the same way. <code>intro σ h s' hp hex</code> takes all five binders; the final state comes <i>third</i>, before the two implications.`,
        `For <code>seq</code>, the middle state is inside the derivation rather than something you invent. <code>cases hex with | seq hex₁ hex₂ => …</code> splits it — then look carefully at what Lean called the state between the halves.`,
        `Lean called it <code>s'✝</code>: inaccessible, unusable. <code>rename_i sMid</code> fixes that. After it, <code>h₁ σ h sMid hp hex₁ : Q sMid.store sMid.heap</code>, and feeding that to <code>h₂</code> finishes.`,
        `For <code>consequence</code> nothing is destructed at all. <code>hpre</code> turns <code>P'</code> into <code>P</code>, <code>hc</code> turns that into <code>Q</code> at <code>s'</code>, <code>hpost</code> turns that into <code>Q'</code>. One <code>exact</code>, three nested applications.`
      ],
      "hint": `For <code>seq</code>, invert the derivation to find the middle state instead of constructing it.`,
      "sol": "theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P := by\n  intro σ h s' hp hex\n  cases hex; exact hp\n\ntheorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R := by\n  intro σ h s' hp hex\n  cases hex with\n  | seq hex₁ hex₂ =>\n      rename_i sMid\n      exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂\n\ntheorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :\n    PartialHoare P' c Q' := by\n  intro σ h s' hp hex\n  exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)",
      "expl": `In the total version you build the execution; here you are given one and take it apart. Every other move in these three proofs is the M6 move, unchanged.`,
      "walk": [
        {
          "tac": "intro σ h s' hp hex",
          "h": `(<code>skip</code>) Five binders at once. Goal <code>P s'.store s'.heap</code>, with <code>hex : Exec Cmd.skip { store := σ, heap := h } s'</code> in hand.`
        },
        {
          "tac": "cases hex; exact hp",
          "h": `<code>Exec .skip</code> has one constructor and it pins the end state to the start state, so <code>cases</code> substitutes <code>s'</code> away entirely rather than leaving an equation. The goal becomes <code>P { store := σ, heap := h }.store { store := σ, heap := h }.heap</code>, printed un-reduced but definitionally <code>P σ h</code>, so <code>exact hp</code> lands with nothing in between.`
        },
        {
          "tac": "intro σ h s' hp hex",
          "h": `(<code>seq</code>) Identical opening, with <code>hex : Exec (c₁ ;; c₂) { store := σ, heap := h } s'</code>. All the content of the proof is in that hypothesis.`
        },
        {
          "tac": "cases hex with",
          "h": `Only one constructor can conclude a <code>;;</code> command, so exactly one case survives unification.`
        },
        {
          "tac": "| seq hex₁ hex₂ =>",
          "h": `Names the two sub-derivations. <code>Exec.seq</code> also carries three implicit states and two implicit commands, and you are naming only the explicit fields — so the middle state arrives unnamed.`
        },
        {
          "tac": "rename_i sMid",
          "h": `The middle state came in as <code>s'✝</code>, a name you cannot type. Now <code>sMid : State</code>, <code>hex₁ : Exec c₁ { store := σ, heap := h } sMid</code> and <code>hex₂ : Exec c₂ sMid s'</code>.`
        },
        {
          "tac": "exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂",
          "h": `<code>h₁ σ h sMid hp hex₁ : Q sMid.store sMid.heap</code>. <code>h₂</code> wants a store, a heap, a final state, a <code>Q</code> at the first two, and a derivation, and all five are to hand. Pass the projections <code>sMid.store sMid.heap</code>, not <code>sMid</code>: <code>PartialHoare</code> takes a store and a heap.`
        },
        {
          "tac": "exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)",
          "h": `(<code>consequence</code>, after the same <code>intro</code>, where now <code>hp : P' σ h</code>.) Read it inside out: <code>hpre σ h hp : P σ h</code>, because an <code>Entails</code> is literally a function of three arguments; then <code>hc … hex : Q s'.store s'.heap</code>; then <code>hpost</code> on those projections. No tactic reasoning at all — it is a term.`
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "partialHoare_seq, and where the middle state goes",
          "start": `P Q R : Assertion
c₁ c₂ : Cmd
h₁ : PartialHoare P c₁ Q
h₂ : PartialHoare Q c₂ R
⊢ PartialHoare P (c₁ ;; c₂) R`,
          "steps": [
            {
              "tac": "intro σ h s' hp hex",
              "state": `P Q R : Assertion
c₁ c₂ : Cmd
h₁ : PartialHoare P c₁ Q
h₂ : PartialHoare Q c₂ R
σ : Store
h : Heap
s' : State
hp : P σ h
hex : Exec (c₁ ;; c₂) { store := σ, heap := h } s'
⊢ R s'.store s'.heap`,
              "h": `Nothing surprising yet. Watch what arrives between the two halves.`
            },
            {
              "tac": "cases hex with | seq hex₁ hex₂ =>",
              "state": `case seq
P Q R : Assertion
c₁ c₂ : Cmd
h₁ : PartialHoare P c₁ Q
h₂ : PartialHoare Q c₂ R
σ : Store
h : Heap
s' : State
hp : P σ h
s'✝ : State
hex₁ : Exec c₁ { store := σ, heap := h } s'✝
hex₂ : Exec c₂ s'✝ s'
⊢ R s'.store s'.heap`,
              "h": `There is <code>s'✝</code>, invented from the constructor's implicit binder <code>{s'}</code> — which already clashes with the <code>s'</code> in scope, so Lean marks it inaccessible rather than shadowing. It stands in the types of both sub-derivations and you cannot write it.`
            },
            {
              "tac": "rename_i sMid",
              "state": `case seq
P Q R : Assertion
c₁ c₂ : Cmd
h₁ : PartialHoare P c₁ Q
h₂ : PartialHoare Q c₂ R
σ : Store
h : Heap
s' : State
hp : P σ h
sMid : State
hex₁ : Exec c₁ { store := σ, heap := h } sMid
hex₂ : Exec c₂ sMid s'
⊢ R s'.store s'.heap`,
              "h": `One name for one trailing inaccessible hypothesis, and the rest of the proof is a single line.`
            }
          ]
        },
        {
          "t": "cmp",
          "left": {
            "t": "M6 · <code>hoare_seq</code>",
            "h": `Two <code>obtain</code>s pull final states out of the hypotheses, and the proof <i>glues</i> the derivations with <code>Exec.seq</code>. The middle state comes from <code>h₁</code>.`,
            "src": `intro σ h hp
obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp
obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq
exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩`
          },
          "right": {
            "t": "M13 · <code>partialHoare_seq</code>",
            "h": `One <code>cases</code> <i>splits</i> a given derivation, and the proof applies the two hypotheses. The middle state comes from <code>hex</code>. Same three objects, opposite direction of travel.`,
            "src": `intro σ h s' hp hex
cases hex with
| seq hex₁ hex₂ =>
    rename_i sMid
    exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂`
          }
        },
        {
          "t": "detail",
          "title": "Two other ways out of an inaccessible name",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "ul",
              "items": [
                `<code>cases hex with | @seq _ sMid _ _ _ hex₁ hex₂ => …</code> — prefixing the constructor with <code>@</code> makes its implicit binders nameable in the pattern. <code>Exec.seq</code> is declared <code>| seq {s s' s'' c₁ c₂} (h₁ …) (h₂ …)</code>, so <code>@seq</code> wants <b>seven</b> names and the middle state is the second. Precise, noisy, and unforgiving about arity.`,
                `Never name it: write <code>h₁ σ h _ hp hex₁</code> and let unification recover the state from <code>hex₁</code>'s type. Fine here, unreadable in general, and it stops working the moment you need the state twice.`
              ]
            },
            {
              "t": "p",
              "h": `The <code>@</code> form fails in the least helpful way available. Write five names instead of seven and Lean does <b>not</b> object to the pattern: it binds them to the first five fields in order, so <code>sMid</code> becomes the <i>start</i> state and <code>hex₁</code>, <code>hex₂</code> become the two <i>commands</i>. All of those are already fixed by the goal, so <code>cases</code> substitutes them away, every name you wrote disappears, and the complaint arrives at the line that uses them — as a row of <code>unknown identifier</code> errors naming variables that are visibly present in your source. Under-counted binder patterns always fail this way.`
            }
          ]
        }
      ],
      "pitfall": `Getting the <code>intro</code> order wrong. <code>intro σ h hp s' hex</code> looks right — precondition before final state — but <code>PartialHoare</code> binds <code>s'</code> third, so <code>hp</code> becomes the name of the <i>state</i> and <code>s'</code> the name of the proof:<br><br><code>hp : State</code><br><code>s' : P σ h</code><br><code>hex : Exec Cmd.skip { store := σ, heap := h } hp</code><br><code>⊢ P hp.store hp.heap</code><br><br>Then <code>cases hex</code> substitutes that state away — the state is called <code>hp</code> — and the last line fails with <code>Unknown identifier &#96;hp&#96;</code>, naming a hypothesis you can see in your own source. When a name disappears, check the binder order in the definition first.`,
      "variants": `<b>Drop determinism.</b> None of these three proofs touches <code>exec_deterministic</code>, so all three survive verbatim into a nondeterministic language. That is not luck: partial correctness quantifies over every run, which is the robust notion. It is <code>partial_of_total</code> that breaks.<br><br><b>Reverse <code>seq</code>'s hypotheses.</b> Prove <code>PartialHoare P (c₁ ;; c₂) R</code> from <code>h₁ : PartialHoare P c₂ Q</code> and the <code>cases</code> still succeeds, but <code>hex₁ : Exec c₁ …</code> no longer matches <code>h₁</code>'s command and there is nothing to be done. The middle state is a real object with a real store and heap; no lemma commutes the halves.<br><br><b>Weaken <code>consequence</code> to <code>hpost : Q' ⊢ Q</code>.</b> The last application breaks, and the statement is false: strengthening a postcondition after the fact would let you conclude <code>aFalse</code> from any triple.`
    },
    {
      "t": "ex",
      "id": "m13-2",
      "name": "partialHoare_ite",
      "hard": false,
      "why": `The smallest rule in which the guard does something, and the template for the loop rule. Both branches get the same <code>P</code> and the same target <code>Q</code>; one extra conjunct distinguishes them, and inversion supplies it free. Understand where <code>hb</code> comes from here and the <code>loopTrue</code> case of the next exercise will hold no surprises.`,
      "setup": `<code>bTrue</code> and <code>bFalse</code> are in scope, and <code>aAnd P Q σ h</code> unfolds to <code>P σ h ∧ Q σ h</code>, so <code>⟨_, _⟩</code> builds one directly.`,
      "goal": "theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q",
      "hints": [
        `<code>cases hex</code>: exactly two constructors can apply, and each hands you the guard evaluation you need.`,
        `The two cases are <code>iteTrue</code> and <code>iteFalse</code>. Each carries two explicit fields — the guard evaluation and the sub-derivation — so name them <code>hb</code> and <code>hex'</code>.`,
        `In <code>iteTrue</code> you hold <code>hp : P σ h</code> and <code>hb : b.eval σ = true</code>, and <code>h₁</code> wants <code>aAnd P (bTrue b) σ h</code>. That is a conjunction: write <code>⟨hp, hb⟩</code> and nothing needs unfolding.`
      ],
      "hint": `<code>cases hex</code>: exactly two constructors can apply, and each hands you the guard evaluation you need.`,
      "sol": "theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q := by\n  intro σ h s' hp hex\n  cases hex with\n  | iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'\n  | iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'",
      "expl": `Two lines. The inversion supplies <code>hb</code>, which is precisely the extra conjunct each branch hypothesis demands — and nothing else about the conditional exists to be recovered.`,
      "walk": [
        {
          "tac": "intro σ h s' hp hex",
          "h": `<code>hex : Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s'</code>, goal <code>Q s'.store s'.heap</code>.`
        },
        {
          "tac": "cases hex with",
          "h": `Of the ten <code>Exec</code> constructors, only two can have produced this derivation, so Lean generates two goals — and it will not let you write a case for one that cannot fire: adding <code>| skip => …</code> gets <code>error: Alternative 'skip' is not needed</code>. The <code>with</code> block is checked against the cases that survive unification, not against the constructor list.`
        },
        {
          "tac": "| iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'",
          "h": `<code>hb : BExpr.eval { store := σ, heap := h }.store b = true</code> and <code>hex' : Exec c₁ { store := σ, heap := h } s'</code>. The pair has type <code>P σ h ∧ b.eval σ = true</code>, which is <code>aAnd P (bTrue b) σ h</code> after two <code>def</code>s and a projection — all definitional, so <code>exact</code> takes it silently.`
        },
        {
          "tac": "| iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'",
          "h": `Mirror image. The two constructors differ in <code>= true</code> versus <code>= false</code> and in which branch they run, and so does the proof.`
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "partialHoare_ite, both branches",
          "start": `P Q : Assertion
b : BExpr
c₁ c₂ : Cmd
h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q
h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q
⊢ PartialHoare P (Cmd.ite b c₁ c₂) Q`,
          "steps": [
            {
              "tac": "intro σ h s' hp hex",
              "state": `P Q : Assertion
b : BExpr
c₁ c₂ : Cmd
h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q
h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q
σ : Store
h : Heap
s' : State
hp : P σ h
hex : Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s'
⊢ Q s'.store s'.heap`,
              "h": `<code>h₁</code> and <code>h₂</code> print with <code>aAnd</code> and <code>bTrue</code> intact. You have to carry the reading <code>P σ h ∧ b.eval σ = true</code> in your head; the display will never give it to you.`
            },
            {
              "tac": "cases hex with | iteTrue hb hex' =>",
              "state": `case iteTrue
P Q : Assertion
b : BExpr
c₁ c₂ : Cmd
h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q
h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q
σ : Store
h : Heap
s' : State
hp : P σ h
hb : BExpr.eval { store := σ, heap := h }.store b = true
hex' : Exec c₁ { store := σ, heap := h } s'
⊢ Q s'.store s'.heap`,
              "h": `Read <code>hb</code> carefully, because this printing recurs all chapter. The constructor's field is <code>b.eval s.store = true</code> with <code>s</code> instantiated to the start state, so out comes prefix form, structure literal, un-reduced projection. It is definitionally <code>b.eval σ</code> and <code>exact</code> treats it as such; no amount of staring will make Lean print it that way.`
            },
            {
              "tac": "exact h₁ σ h s' ⟨hp, hb⟩ hex'",
              "state": `case iteFalse
P Q : Assertion
b : BExpr
c₁ c₂ : Cmd
h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q
h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q
σ : Store
h : Heap
s' : State
hp : P σ h
hb : BExpr.eval { store := σ, heap := h }.store b = false
hex' : Exec c₂ { store := σ, heap := h } s'
⊢ Q s'.store s'.heap`,
              "h": `First goal closed; this is the second, identical but for <code>= false</code>, <code>c₂</code>, and which hypothesis applies.`
            }
          ]
        }
      ],
      "pitfall": `Attaching <code>hb</code> to the wrong branch. Swap <code>h₁</code> and <code>h₂</code> and the error is not about the branch, it is about the guard:<br><br><code>error: Application type mismatch: The argument</code><br><code>&nbsp;&nbsp;hb</code><br><code>has type</code><br><code>&nbsp;&nbsp;BExpr.eval { store := σ, heap := h }.store b = true</code><br><code>but is expected to have type</code><br><code>&nbsp;&nbsp;bFalse b σ h</code><br><code>in the application</code><br><code>&nbsp;&nbsp;⟨hp, hb⟩</code><br><br>Note that it compares an <i>unfolded</i> type against a <i>folded</i> one: the elaborator reports what it had, not what it tried. Read <code>bFalse b σ h</code> as <code>b.eval σ = false</code> and the mismatch is obvious.`,
      "variants": `<b>Drop <code>bTrue b</code> from <code>h₁</code>'s precondition.</b> Still sound — <code>PartialHoare P c₁ Q</code> is the stronger hypothesis, so <code>exact h₁ σ h s' hp hex'</code> finishes — but you have thrown away the only fact that distinguishes the branches, and no interesting conditional survives: “if <code>x = 0</code> then … else …” needs to know <code>x = 0</code> inside the first branch.<br><br><b>Swap <code>bTrue</code> and <code>bFalse</code>.</b> The statement becomes false and Lean says so at the point where the guard is packed into the pair. The failure is local and immediate, which is the dividend of stating guards as assertions rather than as side conditions.<br><br><b>Make guards heap-dependent.</b> The rule as stated stays true, but <code>bTrue b</code> stops being constant in its heap and framing it needs the frame to leave the read location alone.`
    },
    {
      "t": "sec",
      "s": "The rule"
    },
    {
      "t": "p",
      "h": `Now the loop. The proof is an induction on the derivation, and <code>Exec</code>'s command index is <code>Cmd.loop b c</code> — a constructor application, not a variable, so the recursor cannot abstract over it. The repair is the standing one: generalise the command, pin it with an equation, pay in impossible cases. What is new is what the two surviving cases do with the invariant, and that is worth working out before you read the hints.`
    },
    {
      "t": "ex",
      "id": "m13-3",
      "name": "the while rule",
      "hard": true,
      "why": `<b>The invariant rule.</b> Two lines of it are mathematics and the rest is the generalisation, which is worth owning outright: it is what you do whenever you induct on an inductively defined relation whose indices are not variables, in this or any other proof assistant.`,
      "setup": `<code>induction hex with</code> will demand a case for each of <code>Exec</code>'s ten constructors. The two that matter are <code>loopFalse</code> (guard false, state unchanged) and <code>loopTrue</code> (guard true, body, then the rest of the loop).`,
      "goal": "theorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b))",
      "hints": [
        `Try the direct proof and read the refusal: <code>error: Invalid target: Index in target's type is not a variable (consider using the 'cases' tactic instead)</code>, naming <code>Cmd.loop b c</code>. The suggestion is a red herring — <code>cases</code> gives you the two loop cases with no induction hypothesis, and <code>loopTrue</code> needs one.`,
        `State a helper with the command as a variable and the constraint as an ordinary hypothesis: <code>∀ {cmd s s'}, Exec cmd s s' → cmd = .loop b₀ c₀ → I s → I s' ∧ ¬b</code>.`,
        `Order matters. <code>intro cmd s s' hex</code> and then <code>induction hex</code>, leaving the equation and <code>I s</code> <i>inside</i> the goal, so that every case's induction hypothesis carries its own copy of the constraint and each case can <code>intro heq</code> for itself.`,
        `The eight non-loop cases are killed by <code>cases heq</code>, which is an equation between distinct constructors. In <code>loopTrue</code>, <code>hbody</code> re-establishes <code>I</code> after one iteration and <code>ihrest rfl</code> runs the rest.`
      ],
      "hint": `You cannot induct directly, because the loop's command is fixed while the induction generalises it. Prove a helper with the command as a variable plus an equation constraining it: <code>∀ {cmd s s'}, Exec cmd s s' → cmd = .loop b₀ c₀ → I s → I s' ∧ ¬b</code>. All the non-loop cases are killed by <code>cases heq</code>.`,
      "sol": "theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by\n  intro cmd s s' hex\n  induction hex with\n  | skip => intro heq; cases heq\n  | assign => intro heq; cases heq\n  | load _ => intro heq; cases heq\n  | write _ => intro heq; cases heq\n  | free _ => intro heq; cases heq\n  | seq _ _ _ _ => intro heq; cases heq\n  | iteTrue _ _ _ => intro heq; cases heq\n  | iteFalse _ _ _ => intro heq; cases heq\n  | loopFalse hb =>\n      intro heq hI\n      cases heq\n      exact ⟨hI, hb⟩\n  | loopTrue hb hbdy _ _ ihrest =>\n      intro heq hI\n      cases heq\n      exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)\n\ntheorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by\n  intro σ h s' hI hex\n  exact loop_invariant hbody hex rfl hI",
      "expl": `Every constructor except the two loop ones produces an equation between distinct constructors of <code>Cmd</code>, and <code>cases heq</code> discharges it by no-confusion. <code>loopFalse</code> exits with the invariant and the false guard; <code>loopTrue</code> uses <code>hbody</code> to re-establish the invariant after one iteration and the induction hypothesis for everything after that. Those are the two lines of content, and they are the informal argument written out.`,
      "walk": [
        {
          "tac": "intro cmd s s' hex",
          "h": `Introduce the command, both states and the derivation — but <b>not</b> the equation and <b>not</b> <code>I s.store s.heap</code>. Those two stay in the goal on purpose.`
        },
        {
          "tac": "induction hex with",
          "h": `The target is now <code>Exec cmd s s'</code> with all three indices genuine variables, so the recursor applies. Ten cases, each still ending in <code>… = Cmd.loop b₀ c₀ → I … → I … ∧ …</code>.`
        },
        {
          "tac": "| skip => intro heq; cases heq",
          "h": `Here the equation reads <code>Cmd.skip = Cmd.loop b₀ c₀</code>. <code>intro heq</code> names it; <code>cases heq</code> observes that no such equation exists and closes the case with no goals.`
        },
        {
          "tac": "| assign => intro heq; cases heq",
          "h": `Identically for <code>load</code>, <code>write</code>, <code>free</code>, <code>seq</code>, <code>iteTrue</code> and <code>iteFalse</code>. The lines differ only in how many constructor fields they bind with <code>_</code>, and the counts must match: <code>seq</code> has two sub-derivations plus two induction hypotheses, hence <code>| seq _ _ _ _ =></code>.`
        },
        {
          "tac": "| loopFalse hb =>",
          "h": `The exit case. <code>hb : BExpr.eval s✝.store b✝ = false</code>, where <code>b✝</code> is the constructor's own guard, not yet known to be <code>b₀</code>.`
        },
        {
          "tac": "intro heq hI",
          "h": `Take the two remaining hypotheses: <code>heq : Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀</code> and <code>hI : I s✝.store s✝.heap</code>.`
        },
        {
          "tac": "cases heq",
          "h": `This time the two sides are the <i>same</i> constructor, so no-confusion yields injectivity rather than absurdity: <code>b✝ = b₀</code> and <code>c✝ = c₀</code>, substituted on the spot. The case is renamed <code>loopFalse.refl</code>, and <code>hb</code> now reads <code>BExpr.eval s✝.store b₀ = false</code>.`
        },
        {
          "tac": "exact ⟨hI, hb⟩",
          "h": `<code>loopFalse</code> ends where it started, so the goal is exactly those two hypotheses paired.`
        },
        {
          "tac": "| loopTrue hb hbdy _ _ ihrest =>",
          "h": `Five binders: the guard evaluation, the body derivation, the rest-of-loop derivation (discarded, since the induction hypothesis says everything it says), the induction hypothesis for the body (useless — it would demand <code>c₀ = .loop b₀ c₀</code>), and the induction hypothesis for the rest, which is the one that matters.`
        },
        {
          "tac": "intro heq hI",
          "h": `Same two hypotheses, but <code>hI</code> is now the invariant at the state <i>before</i> the body runs.`
        },
        {
          "tac": "cases heq",
          "h": `Injectivity again. Crucially it also rewrites <code>ihrest</code>, whose hypothesis becomes <code>Cmd.loop b₀ c₀ = Cmd.loop b₀ c₀</code>.`
        },
        {
          "tac": "exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)",
          "h": `Inner application first. <code>hbody</code> is a <code>PartialHoare</code>: a store, a heap, a final state, a proof of <code>aAnd I (bTrue b₀)</code>, a derivation. The three underscores are the start store, the start heap and the post-body state, all recoverable from <code>hbdy</code>. It returns the invariant at the post-body state, and <code>ihrest rfl</code> carries that to the end.`
        },
        {
          "tac": "exact loop_invariant hbody hex rfl hI",
          "h": `(<code>partialHoare_while</code>, after the usual <code>intro σ h s' hI hex</code>.) <code>rfl</code> discharges <code>Cmd.loop b c = Cmd.loop b c</code>, and the three implicit arguments come from <code>hex</code>. Generalising was the whole difficulty; instantiating back down is free.`
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "loop_invariant — the states that matter",
          "start": `I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
⊢ ∀ {cmd : Cmd} {s s' : State},
    Exec cmd s s' → cmd = Cmd.loop b₀ c₀ → I s.store s.heap → I s'.store s'.heap ∧ BExpr.eval s'.store b₀ = false`,
          "steps": [
            {
              "tac": "intro cmd s s' hex",
              "state": `I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
cmd : Cmd
s s' : State
hex : Exec cmd s s'
⊢ cmd = Cmd.loop b₀ c₀ → I s.store s.heap → I s'.store s'.heap ∧ BExpr.eval s'.store b₀ = false`,
              "h": `Four things introduced, two implications left standing. A derivation in the context with everything else still under an arrow is the signature of a proof that is about to induct.`
            },
            {
              "tac": "induction hex with | seq _ _ _ _ => …",
              "state": `case seq
I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
cmd : Cmd
s s' s✝ s'✝ s''✝ : State
c₁✝ c₂✝ : Cmd
h₁✝ : Exec c₁✝ s✝ s'✝
h₂✝ : Exec c₂✝ s'✝ s''✝
h₁_ih✝ : c₁✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s'✝.store s'✝.heap ∧ BExpr.eval s'✝.store b₀ = false
h₂_ih✝ : c₂✝ = Cmd.loop b₀ c₀ → I s'✝.store s'✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false
⊢ c₁✝ ;; c₂✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false`,
              "h": `The impossible case, shown because it is where the generalisation is visible: <code>h₁_ih✝</code> and <code>h₂_ih✝</code> are induction hypotheses that carry the constraint with them. Here they are wasted — the goal dies on its equation — but <code>loopTrue</code> has this shape and there the second one is the entire proof. Note also the original <code>cmd</code>, <code>s</code>, <code>s'</code> still sitting in the context, now inert: the induction abstracted over fresh copies.`
            },
            {
              "tac": "| loopFalse hb => intro heq hI",
              "state": `case loopFalse
I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
cmd : Cmd
s s' s✝ : State
b✝ : BExpr
c✝ : Cmd
hb : BExpr.eval s✝.store b✝ = false
heq : Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀
hI : I s✝.store s✝.heap
⊢ I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false`,
              "h": `Look at the mismatch: <code>hb</code> is about <code>b✝</code>, the goal is about <code>b₀</code>. They are not yet the same guard, and the information that they are is locked inside <code>heq</code>.`
            },
            {
              "tac": "cases heq",
              "state": `case loopFalse.refl
I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
cmd : Cmd
s s' s✝ : State
hI : I s✝.store s✝.heap
hb : BExpr.eval s✝.store b₀ = false
⊢ I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false`,
              "h": `<code>b✝</code> and <code>c✝</code> are gone, substituted by <code>b₀</code> and <code>c₀</code>, and the case picked up a <code>.refl</code> suffix — that is <code>cases</code> on an equality, whose single constructor is <code>Eq.refl</code>. <code>hb</code> now literally matches the right conjunct.`
            },
            {
              "tac": "| loopTrue hb hbdy _ _ ihrest => intro heq hI; cases heq",
              "state": `case loopTrue.refl
I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
cmd : Cmd
s s' s✝ s'✝ s''✝ : State
hI : I s✝.store s✝.heap
hb : BExpr.eval s✝.store b₀ = true
hbdy : Exec c₀ s✝ s'✝
hbody_ih✝ : c₀ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s'✝.store s'✝.heap ∧ BExpr.eval s'✝.store b₀ = false
hrest✝ : Exec (Cmd.loop b₀ c₀) s'✝ s''✝
ihrest :
  Cmd.loop b₀ c₀ = Cmd.loop b₀ c₀ → I s'✝.store s'✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false
⊢ I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false`,
              "h": `Everything you need and one thing you do not. <code>hbody_ih✝</code> demands <code>c₀ = Cmd.loop b₀ c₀</code>, a body equal to the loop containing it, which is why the solution discards it. <code>ihrest</code> wants <code>rfl</code> and the invariant at <code>s'✝</code>; getting the invariant from <code>s✝</code> to <code>s'✝</code> is exactly what <code>hbody</code> does, with <code>hb</code> as the second conjunct of its precondition.`
            },
            {
              "tac": "exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)",
              "state": `No goals.`,
              "h": `<code>hbdy : Exec c₀ s✝ s'✝</code> is accepted where <code>Exec c₀ { store := s✝.store, heap := s✝.heap } s'✝</code> is expected. Structure eta, silently.`
            }
          ]
        },
        {
          "t": "detail",
          "title": "<code>cases heq</code>, twice, doing two different things",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `One tactic, two jobs. On <code>Cmd.skip = Cmd.loop b₀ c₀</code> it is disjointness, and the case dies. On <code>Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀</code> it is injectivity — and it goes further than <code>injection heq</code> would, substituting rather than handing back the component equations, which is why the goal afterwards mentions <code>b₀</code> and the case name gains <code>.refl</code>. <code>subst heq</code> would simply fail here, since neither side is a free variable.`
            }
          ]
        },
        {
          "t": "detail",
          "title": "Lean is more forgiving here than the folklore suggests",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `Lean 4's <code>induction</code> automatically reverts any context hypothesis mentioning the target's indices, and both <code>heq : cmd = …</code> and <code>hI : I s.store s.heap</code> do. So <code>intro cmd s s' hex heq hI</code> followed by <code>induction hex</code> also works: the two are reverted, generalised, and handed back in every case, and all ten <code>intro heq</code>s can be deleted. The corpus proof keeps them out of the context by hand because doing it by hand is what makes the mechanism visible.`
            },
            {
              "t": "p",
              "h": `The auto-revert does not cover anything that fails to mention an index. When the induction hypothesis has to be applied at a different value of some <i>other</i> variable, you revert it yourself — that is what <code>generalizing</code> is for, as in <code>induction h₁ generalizing s₂</code>, where <code>s₂</code> is an index of <code>h₂</code> and not of <code>h₁</code>.`
            }
          ]
        }
      ],
      "pitfall": `Naming too few fields in a case pattern. <code>induction</code> hands you the constructor's own arguments <i>and</i> one induction hypothesis per recursive argument, so <code>loopTrue</code> has five fields, not three. Write <code>| loopTrue hb hbdy ihrest =></code> and Lean does not complain: the names bind to the leading fields, <code>ihrest</code> silently becomes the rest-of-loop <i>derivation</i>, and the two induction hypotheses stay inaccessible. The complaint arrives at the point of use:<br><br><code>error: Function expected at</code><br><code>&nbsp;&nbsp;ihrest</code><br><code>but this term has type</code><br><code>&nbsp;&nbsp;Exec (Cmd.loop b₀ c₀) s'✝ s''✝</code><br><br>The asymmetry is worth knowing: too <i>many</i> names is caught immediately and precisely — <code>error: Too many variable names provided at alternative 'seq': 5 provided, but 4 expected</code> — while too few is caught nowhere. Count constructor arguments, then add one per recursive argument.<br><br>Second trap: forgetting what <code>hbody</code> eats. Drop the three underscores in <code>hbody _ _ _ ⟨hI, hb⟩ hbdy</code> and the error names a type you never wrote — <code>error: Invalid ⟨...⟩ notation: The expected type 'Var → Val' is not an inductive type</code>. <code>Var → Val</code> is <code>Store</code>; the pair went into the first argument slot. Whenever an error mentions a type you did not type, count the arguments of the function you are applying.`,
      "variants": `<b>Drop <code>bTrue b</code> from <code>hbody</code>.</b> Still true, and the proof still compiles if you drop <code>hb</code> from the pair — but you have given up the guard, and with it every loop whose progress depends on the condition. Note the direction: this weakens the rule, it does not break it.<br><br><b>Drop <code>bFalse b</code> from the conclusion.</b> Also true, also useless. Almost every real loop specification has the shape “invariant plus negated guard collapses to the postcondition”; without the second conjunct the rule can only tell you what you already knew.<br><br><b>Replace <code>PartialHoare</code> by <code>Hoare</code> in the conclusion.</b> False, and <code>not_hoare_forever</code> is the refutation. The single point of failure is the <code>loopTrue</code> case: its induction hypothesis exists only because a derivation of the rest of the loop was handed to you. With a total conclusion you would have to build that derivation, and there is nothing to build it from.<br><br><b>Let the body conclude a different invariant.</b> If <code>hbody</code> ended in <code>I'</code>, <code>ihrest</code> would want <code>I</code> and you would hold <code>I'</code>. There is no repair; “the same before and after” is not a convenience, it is what the word means.`
    },
    {
      "t": "p",
      "h": `The rule is now a theorem, so point it at the loop that motivated the whole distinction. Take <code>I := aTrue</code> and the tautologous guard. The body obligation is discharged by inverting <code>Exec .skip</code> and observing that <code>aTrue</code> is <code>True</code>. What comes out the other side is a perfectly correct triple whose postcondition no state satisfies:`
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "Compiles against the M13 prelude. forever and no_exec_forever are M6's, repeated so the snippet stands alone.",
      "src": `def forever : Cmd := .loop (.equals (.const 0) (.const 0)) .skip

theorem no_exec_forever : ∀ {c : Cmd} {s s' : State}, c = forever → Exec c s s' → False := by
  intro c s s' hc hex
  induction hex with
  | loopFalse hb => cases hc; simp [BExpr.eval, Atom.eval] at hb
  | loopTrue hb hbody hrest ihb ihr => exact ihr hc
  | _ => cases hc

-- the body obligation: skip preserves aTrue
theorem forever_body :
    PartialHoare (aAnd aTrue (bTrue (.equals (.const 0) (.const 0)))) .skip aTrue := by
  intro σ h s' _ hex
  cases hex
  trivial

-- so the rule fires …
theorem forever_partial :
    PartialHoare aTrue forever (aAnd aTrue (bFalse (.equals (.const 0) (.const 0)))) :=
  partialHoare_while forever_body

-- … and its postcondition holds at no state whatsoever
theorem forever_post_is_false (σ : Store) (h : Heap) :
    ¬ aAnd aTrue (bFalse (.equals (.const 0) (.const 0))) σ h := by
  intro ⟨_, hb⟩
  simp [bFalse, BExpr.eval, Atom.eval] at hb`
    },
    {
      "t": "p",
      "h": `Nothing there is wrong. <code>forever_partial</code> says that no execution of <code>forever</code> ends in a state satisfying an impossible assertion, and it is true because there are no executions. Read it as the diagnosis it is: a partial triple with an unsatisfiable postcondition is evidence of divergence, not a fact about a run.`
    },
    {
      "t": "sec",
      "s": "Making it stop"
    },
    {
      "t": "p",
      "h": `The missing ingredient is a <b>variant</b>: a natural number that strictly decreases on every iteration. On paper you would carry it beside the invariant as an expression <code>V</code> over the store, with obligations saying that <code>V</code> falls and that <code>V = 0</code> forces the guard false. Here it is folded into the invariant, which becomes a family <code>I : Nat → Assertion</code> in which <code>I n</code> asserts the invariant <i>and</i> that the variant is currently <code>n</code>.`
    },
    {
      "t": "cmp",
      "left": {
        "t": "The textbook shape",
        "h": `Two objects and three obligations relating them. Faithful to a lecture and awkward in Lean: <code>V</code> would be a <code>Store → Nat</code>, and every obligation would carry a hypothesis about its value.`,
        "src": `I : Assertion
V : Store → Nat

{ I ∧ b ∧ V = n } body { I ∧ V < n }
I ∧ V = 0  →  ¬b`
      },
      "right": {
        "t": "What we do",
        "h": `One object. The decrease is expressed by the <i>indices</i> of two assertions rather than by an inequality, so induction on <code>n</code> does all the work and no well-foundedness argument has to be supplied by hand.`,
        "src": `I : Nat → Assertion

∀ n, Hoare (aAnd (I (n+1)) (bTrue b)) c (I n)
∀ σ h, I 0 σ h → b.eval σ = false`
      }
    },
    {
      "t": "p",
      "h": `The price is rigidity: the variant must fall by <i>exactly</i> one. That is a simplification of the general rule rather than a limitation of variants, and exercise 5 shows the goal Lean leaves behind when a program violates it.`
    },
    {
      "t": "ex",
      "id": "m13-4",
      "name": "hoare_while_variant",
      "hard": true,
      "why": `One iteration takes you from <code>I (n+1)</code> to <code>I n</code>, and at <code>I 0</code> the guard must be false. Induction on <code>n</code> then <i>constructs</i> a terminating execution, so the conclusion is total. This is the first proof here that builds an <code>Exec</code> derivation of unbounded depth — the recursion assembles it, one <code>Exec.loopTrue</code> per iteration.`,
      "setup": `Back in <code>Hoare</code>-land, so every branch ends by exhibiting a state and a derivation. <code>Exec.loopFalse</code> and <code>Exec.loopTrue</code> are the only constructors you need.`,
      "goal": "theorem hoare_while_variant {I : Nat → Assertion} {b : BExpr} {c : Cmd}\n    (hstep : ∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n))\n    (hstop : ∀ σ h, I 0 σ h → b.eval σ = false) :\n    ∀ n, Hoare (I n) (.loop b c) (aExists fun m => aAnd (I m) (bFalse b))",
      "hints": [
        `Induct on <code>n</code>, not on a derivation — there is no derivation to induct on, you are producing one. So the shape is <code>intro n; induction n with | zero => … | succ n ih => …</code>.`,
        `Base case: <code>hstop</code> makes the guard false, so <code>Exec.loopFalse</code>. Step: split on the guard; if true, run the body and then the induction hypothesis and glue with <code>Exec.loopTrue</code>; if false, exit immediately.`,
        `To split on the guard you need the resulting equation, so write <code>cases hbv : b.eval σ with</code>. Without the <code>hbv :</code> you get two goals and no information, because <code>b.eval σ</code> does not occur in the goal for <code>cases</code> to substitute into.`,
        `The existentials flatten. The goal is <code>∃ s', Exec … ∧ ∃ m, I m … ∧ …</code>, so one anonymous constructor with five slots does it: <code>⟨state, derivation, m, invariant, guard⟩</code>. In the <code>zero</code> case that is <code>⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩</code>.`
      ],
      "hint": `Induct on <code>n</code>. Base case: the guard is false by <code>hstop</code>, so <code>Exec.loopFalse</code>. Step: case on the guard; if true, run the body then the induction hypothesis and glue with <code>Exec.loopTrue</code>; if false, exit immediately.`,
      "sol": "theorem hoare_while_variant {I : Nat → Assertion} {b : BExpr} {c : Cmd}\n    (hstep : ∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n))\n    (hstop : ∀ σ h, I 0 σ h → b.eval σ = false) :\n    ∀ n, Hoare (I n) (.loop b c) (aExists fun m => aAnd (I m) (bFalse b)) := by\n  intro n\n  induction n with\n  | zero =>\n      intro σ h hI\n      exact ⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩\n  | succ n ih =>\n      intro σ h hI\n      cases hbv : b.eval σ with\n      | true =>\n          obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩\n          obtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁\n          exact ⟨s₂, Exec.loopTrue hbv hex₁ hex₂, hpost⟩\n      | false =>\n          exact ⟨⟨σ, h⟩, Exec.loopFalse hbv, n + 1, hI, hbv⟩",
      "expl": `The postcondition is <code>∃ m, I m ∧ ¬b</code> and not <code>I 0 ∧ ¬b</code>, and that is a correction rather than a stylistic choice. A loop may exit early: the guard can go false while the variant is still positive, and then you land in <code>I (n+1)</code>. Writing <code>I 0</code> makes the theorem unprovable, and the failing case is exactly that early exit.`,
      "walk": [
        {
          "tac": "intro n; induction n with",
          "h": `Name the variant's starting value and induct on it. The induction hypothesis is the whole triple at <code>n</code> — a <code>Hoare</code>, not a statement about a state — which is what lets the step case call it at a different store and heap.`
        },
        {
          "tac": "| zero => intro σ h hI",
          "h": `The variant is already at the bottom, so the loop must not iterate. Goal: <code>∃ s', Exec (Cmd.loop b c) { store := σ, heap := h } s' ∧ aExists (fun m => aAnd (I m) (bFalse b)) s'.store s'.heap</code>.`
        },
        {
          "tac": "exact ⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩",
          "h": `Five slots for two nested existentials and two conjunctions. The final state is the initial one; <code>Exec.loopFalse</code> needs the guard false, which is <code>hstop σ h hI</code>; the witness for <code>m</code> is <code>0</code>; and the last two components are the invariant and the false guard again. <code>hstop σ h hI</code> appears twice, once inside the derivation and once in the postcondition — not redundancy, two uses of one proof.`
        },
        {
          "tac": "| succ n ih =>",
          "h": `<code>ih : Hoare (I n) (Cmd.loop b c) (aExists fun m => aAnd (I m) (bFalse b))</code> — the full triple one notch down.`
        },
        {
          "tac": "intro σ h hI",
          "h": `<code>hI : I (n + 1) σ h</code>. The loop may or may not run, and nothing so far says which.`
        },
        {
          "tac": "cases hbv : b.eval σ with",
          "h": `Split on the guard's value <i>and record the split</i>. The <code>hbv :</code> prefix is what produces <code>hbv : BExpr.eval σ b = true</code> in one branch and <code>= false</code> in the other.`
        },
        {
          "tac": "| true => obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩",
          "h": `The step obligation at index <code>n</code> has precondition <code>aAnd (I (n+1)) (bTrue b)</code>, and <code>⟨hI, hbv⟩</code> is that pair. Out come a post-body state <code>s₁</code>, a derivation, and <code>hI₁ : I n s₁.store s₁.heap</code> — the variant has dropped by one.`
        },
        {
          "tac": "obtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁",
          "h": `Apply the induction hypothesis at the <i>new</i> store and heap; this is why it had to be a full triple. Out comes a derivation of the rest of the loop.`
        },
        {
          "tac": "exact ⟨s₂, Exec.loopTrue hbv hex₁ hex₂, hpost⟩",
          "h": `<code>Exec.loopTrue</code> takes a true guard, a body derivation and a rest-of-loop derivation and returns a derivation of the whole loop. <code>hpost</code> passes through untouched — the <code>∃ m</code> was resolved by the induction hypothesis, at whatever value the loop actually exited.`
        },
        {
          "tac": "| false => exact ⟨⟨σ, h⟩, Exec.loopFalse hbv, n + 1, hI, hbv⟩",
          "h": `<b>The early exit.</b> The guard is false even though the variant is <code>n + 1 > 0</code>, so the loop stops here and the witness for <code>m</code> is <code>n + 1</code>. This one line is why the postcondition is an existential.`
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_while_variant, the three interesting states",
          "start": `I : Nat → Assertion
b : BExpr
c : Cmd
hstep : ∀ (n : Nat), Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n)
hstop : ∀ (σ : Store) (h : Heap), I 0 σ h → BExpr.eval σ b = false
⊢ ∀ (n : Nat), Hoare (I n) (Cmd.loop b c) (aExists fun m => aAnd (I m) (bFalse b))`,
          "steps": [
            {
              "tac": "intro n; induction n with | zero => intro σ h hI",
              "state": `case zero
I : Nat → Assertion
b : BExpr
c : Cmd
hstep : ∀ (n : Nat), Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n)
hstop : ∀ (σ : Store) (h : Heap), I 0 σ h → BExpr.eval σ b = false
σ : Store
h : Heap
hI : I 0 σ h
⊢ ∃ s', Exec (Cmd.loop b c) { store := σ, heap := h } s' ∧ aExists (fun m => aAnd (I m) (bFalse b)) s'.store s'.heap`,
              "h": `An <code>∃</code> and, inside it, <code>aExists</code> — itself an <code>∃</code> under a <code>def</code>, which Lean will not show you. The five-slot anonymous constructor is <code>⟨s', hex, m, left, right⟩</code>.`
            },
            {
              "tac": "obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩\nobtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁",
              "state": `case succ.true
I : Nat → Assertion
b : BExpr
c : Cmd
hstep : ∀ (n : Nat), Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n)
hstop : ∀ (σ : Store) (h : Heap), I 0 σ h → BExpr.eval σ b = false
n : Nat
ih : Hoare (I n) (Cmd.loop b c) (aExists fun m => aAnd (I m) (bFalse b))
σ : Store
h : Heap
hI : I (n + 1) σ h
hbv : BExpr.eval σ b = true
s₁ : State
hex₁ : Exec c { store := σ, heap := h } s₁
hI₁ : I n s₁.store s₁.heap
s₂ : State
hex₂ : Exec (Cmd.loop b c) { store := s₁.store, heap := s₁.heap } s₂
hpost : aExists (fun m => aAnd (I m) (bFalse b)) s₂.store s₂.heap
⊢ ∃ s', Exec (Cmd.loop b c) { store := σ, heap := h } s' ∧ aExists (fun m => aAnd (I m) (bFalse b)) s'.store s'.heap`,
              "h": `<code>hex₂</code> starts at <code>{ store := s₁.store, heap := s₁.heap }</code>, not at <code>s₁</code>, because <code>Hoare</code> takes a store and a heap and rebuilds a <code>State</code> internally. <code>Exec.loopTrue hbv hex₁ hex₂</code> typechecks anyway, on eta. In a proof assistant without eta for structures, this is the line that breaks.`
            },
            {
              "tac": "| false =>",
              "state": `case succ.false
I : Nat → Assertion
b : BExpr
c : Cmd
hstep : ∀ (n : Nat), Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n)
hstop : ∀ (σ : Store) (h : Heap), I 0 σ h → BExpr.eval σ b = false
n : Nat
ih : Hoare (I n) (Cmd.loop b c) (aExists fun m => aAnd (I m) (bFalse b))
σ : Store
h : Heap
hI : I (n + 1) σ h
hbv : BExpr.eval σ b = false
⊢ ∃ s', Exec (Cmd.loop b c) { store := σ, heap := h } s' ∧ aExists (fun m => aAnd (I m) (bFalse b)) s'.store s'.heap`,
              "h": `The case the postcondition's shape exists for. <code>hI</code> says the variant is <code>n + 1</code>; there is no route from here to <code>I 0</code>, and none is wanted — you supply <code>n + 1</code> as the witness.`
            }
          ]
        },
        {
          "t": "p",
          "h": `That <code>I 0</code> in the conclusion is unprovable is a claim, so here it is refuted. The instance is degenerate on purpose: a guard that is never true, so the loop exits on its first test and the variant never moves.`
        },
        {
          "t": "code",
          "tag": "illustration",
          "cap": "Compiles against the M13 prelude. The strengthened rule, refuted by a loop that exits immediately.",
          "src": `def neverTrue : BExpr := .equals (.const 0) (.const 1)

theorem neverTrue_eval (σ : Store) : neverTrue.eval σ = false := by
  simp [neverTrue, BExpr.eval, Atom.eval]

theorem variant_with_I0_is_false :
    ¬ (∀ (I : Nat → Assertion) (b : BExpr) (c : Cmd),
         (∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n)) →
         (∀ σ h, I 0 σ h → b.eval σ = false) →
         ∀ n, Hoare (I n) (.loop b c) (aAnd (I 0) (bFalse b))) := by
  intro hrule
  have hstep : ∀ n, Hoare (aAnd (fun σ (_ : Heap) => σ 0 = n + 1) (bTrue neverTrue))
      .skip (fun σ (_ : Heap) => σ 0 = n) := by
    intro n σ h hpre
    have hb : neverTrue.eval σ = true := hpre.2
    rw [neverTrue_eval] at hb
    exact Bool.noConfusion hb
  have hstop : ∀ σ h, (fun σ (_ : Heap) => σ 0 = 0) σ h → neverTrue.eval σ = false :=
    fun σ _ _ => neverTrue_eval σ
  obtain ⟨s', hex, hI0, _⟩ :=
    hrule (fun n σ _ => σ 0 = n) neverTrue .skip hstep hstop 1 (fun _ => 1) Heap.empty rfl
  cases hex with
  | loopFalse _ => exact Nat.noConfusion hI0
  | loopTrue hb _ _ => rw [neverTrue_eval] at hb; exact Bool.noConfusion hb`
        },
        {
          "t": "p",
          "h": `From the strengthened rule at <code>n = 1</code>, applied to the store mapping variable <code>0</code> to the value <code>1</code>, you obtain a final state whose store maps <code>0</code> to <code>0</code>. The only execution of this loop is <code>loopFalse</code>, which changes nothing, so that store still maps <code>0</code> to <code>1</code> and <code>Nat.noConfusion</code> closes it. Early exit is not a corner case: it is what happens every time a loop finishes ahead of its worst-case bound.`
        },
        {
          "t": "detail",
          "title": "Why induction on <code>n</code> rather than well-founded recursion",
          "tag": "design",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `The general rule lets the measure fall by any amount into any well-founded order, which means carrying an order, a proof it is well-founded, and an accessibility argument. Restricting to “falls by exactly one on <code>Nat</code>” replaces all of that with <code>induction n</code>.`
            },
            {
              "t": "p",
              "h": `Nothing is lost in principle. If your real measure drops by more than one, reindex: take <code>I n := (the invariant) ∧ V ≤ n</code>, and the obligations go through because <code>V ≤ n + 1</code> together with a decrease gives <code>V ≤ n</code>. What is lost is convenience — you do that reindexing by hand, and the next exercise's <code>x := 0</code> variant is exactly where the unreindexed version stops.`
            }
          ]
        }
      ],
      "pitfall": `Writing <code>cases b.eval σ with</code> instead of <code>cases hbv : b.eval σ with</code>. It <i>succeeds</i>. You get two goals, <code>succ.true</code> and <code>succ.false</code>, with identical contexts and identical goals, because <code>b.eval σ</code> does not occur in the goal and <code>cases</code> has nothing to substitute into. You then discover you cannot build the pair for <code>hstep</code>, since nothing in scope says the guard is true — and the tactic that failed is three lines above the error. Whenever you case on the value of an expression that is not in the goal, name the equation.<br><br>Smaller trap: <code>obtain ⟨s₂, hex₂, hpost⟩ := ih s₁ hI₁</code>. <code>ih</code> is a <code>Hoare</code>, which takes a store and a heap, not a <code>State</code>. Pass <code>s₁.store s₁.heap</code>.`,
      "variants": `<b>Drop <code>hstop</code>.</b> The base case becomes unprovable, and rightly: with no link between <code>I 0</code> and the guard, a loop can sit at variant zero and keep iterating. Take <code>I n := aTrue</code> with the tautologous guard and body <code>.skip</code> — <code>hstep</code> holds trivially and the loop is <code>forever</code>.<br><br><b>Weaken <code>hstep</code> to <code>Hoare (I (n+1)) c (I n)</code>, dropping the guard.</b> Sound but weaker, and worse here than in the partial rule: most real loop bodies decrease the variant only <i>because</i> the guard held.<br><br><b>Let the variant stay put.</b> Change <code>hstep</code> to <code>∀ n, Hoare (aAnd (I n) (bTrue b)) c (I n)</code> and the theorem is false, since the index no longer measures anything. Choose the family with care: <code>hstop</code> must still hold, and <code>I n := aTrue</code> flatly fails it. Take <code>I n := fun _ _ => n ≠ 0</code>, so that <code>I 0</code> is unsatisfiable and <code>hstop</code> is vacuous while <code>I 1</code> is <code>aTrue</code>; with body <code>.skip</code> the modified <code>hstep</code> holds and the conclusion at <code>n = 1</code> asserts that <code>forever</code> terminates. That the counterexample needs an unsatisfiable <code>I 0</code> is itself the content: what stopped the loop was <code>hstop</code> paired with a variant that actually falls.<br><br><b>Replace the postcondition by <code>aAnd (I 0) (bFalse b)</code>.</b> False; the machine-checked refutation is above.`
    },
    {
      "t": "ex",
      "id": "m13-5",
      "name": "a loop that actually terminates",
      "hard": false,
      "why": `The smallest program whose termination is a theorem rather than an accident, and the first time you have to <i>choose</i> an invariant instead of being handed one. The choice is instructive because here the invariant and the variant are the same object.`,
      "setup": `<code>hoare_while_variant</code> is available. <code>Atom.eval σ (.minus a b)</code> is truncated <code>Nat</code> subtraction.`,
      "goal": "def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))\n\ndef countdown (x : Var) : Cmd :=\n  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))\n\ntheorem countdown_spec (x : Var) : ∀ n,\n    Hoare (fun σ _ => σ x = n) (countdown x)\n      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x)))",
      "hints": [
        `Take <code>I n := fun σ _ => σ x = n</code>. The step obligation is that after <code>x := x - 1</code> the store maps <code>x</code> to <code>n</code>, given that it mapped it to <code>n + 1</code>; the stop obligation is that <code>σ x = 0</code> makes the guard false.`,
        `Apply the rule with <code>refine</code> so the obligations arrive as goals, and name the invariant while you are there: <code>refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_</code>.`,
        `Both goals close with one <code>simp</code>, and both need a hypothesis <i>listed in the bracket</i> — <code>simp</code> does not go looking through your context. The step goal needs <code>σ x = n + 1</code> so that <code>σ x - 1</code> becomes <code>n + 1 - 1</code>; the stop goal needs <code>σ x = 0</code> so that <code>decide (σ x = 0)</code> becomes <code>true</code>.`,
        `If the goal is an unreadable pile of projections, restate it with <code>show</code>. The two you want are <code>show Store.set σ x (σ x - 1) x = n</code> and <code>show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false</code>.`
      ],
      "hint": `Take <code>I n := fun σ _ => σ x = n</code>. The step obligation is that after <code>x := x - 1</code> the store maps <code>x</code> to <code>n</code>, given it mapped it to <code>n + 1</code>. The stop obligation is that <code>σ x = 0</code> makes the guard false.`,
      "sol": "def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))\n\ndef countdown (x : Var) : Cmd :=\n  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))\n\ntheorem countdown_spec (x : Var) : ∀ n,\n    Hoare (fun σ _ => σ x = n) (countdown x)\n      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x))) := by\n  refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_\n  · intro n σ h hpre\n    obtain ⟨hx, _⟩ := hpre\n    refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩\n    show Store.set σ x (σ x - 1) x = n\n    have hx' : σ x = n + 1 := hx\n    simp [Store.set, hx']\n  · intro σ h hI\n    have hx : σ x = 0 := hI\n    show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false\n    simp [Atom.eval, hx]",
      "expl": `The variant <i>is</i> the value of <code>x</code>, which is why the invariant is indexed by it and says nothing else. Both obligations are one <code>simp</code>. Replace the body with <code>x := 0</code> and watch the step obligation fail: the program still terminates, but a variant that must fall by exactly one cannot see it.`,
      "walk": [
        {
          "tac": "refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_",
          "h": `<code>refine</code> applies the lemma and leaves the two arguments as goals. The named <code>(I := …)</code> is not <i>forced</i> here: the precondition is <code>fun σ _ => σ x = n</code> under <code>∀ n</code>, so Lean faces <code>?I n =?= fun σ _ => σ x = n</code> with <code>n</code> a distinct bound variable — a <b>Miller pattern</b>, which pattern unification solves uniquely, so the bare <code>refine hoare_while_variant ?_ ?_</code> compiles too. Write it anyway. The invariant is the one thing here you had to invent, and it stops being inferable the moment the precondition you are handed is not already literally of the form <code>I n</code> — which is the normal case, since for a real loop the invariant is strictly weaker than what you start from.`
        },
        {
          "tac": "· intro n σ h hpre",
          "h": `The step obligation. <code>hpre</code> is the invariant at <code>n+1</code> paired with the guard.`
        },
        {
          "tac": "obtain ⟨hx, _⟩ := hpre",
          "h": `Split and discard the guard. This body decrements <code>x</code> whatever the guard says, so the guard is genuinely unnecessary — one of the rare cases where you can throw it away.`
        },
        {
          "tac": "refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩",
          "h": `Build the total triple: final state is the store with <code>x</code> decremented and the heap untouched, derivation is <code>Exec.assign</code>, postcondition left as a goal. <code>Exec.assign</code> takes no explicit arguments — its final state is fixed by the constructor and Lean checks it against the one you wrote.`
        },
        {
          "tac": "show Store.set σ x (σ x - 1) x = n",
          "h": `The goal is that equation buried under a lambda and two structure projections. <code>show</code> restates it beta-reduced and projection-free, which succeeds because the two are definitionally equal. Nothing changes for Lean; everything changes for you.`
        },
        {
          "tac": "have hx' : σ x = n + 1 := hx",
          "h": `A copy of <code>hx</code> with its type written out. <code>hx</code> already has that type, so the line is not needed — it is there so that the <code>simp</code> below says out loud which fact it depends on.`
        },
        {
          "tac": "simp [Store.set, hx']",
          "h": `<code>Store.set</code> unfolds to <code>if x = x then σ x - 1 else σ x</code>; <code>simp</code> collapses the conditional, rewrites with <code>hx'</code> to <code>n + 1 - 1</code>, and finishes by arithmetic. This is the one place truncated subtraction could have bitten, and it does not, because <code>hx'</code> guarantees a successor.`
        },
        {
          "tac": "show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false",
          "h": `The stop obligation, after <code>intro σ h hI</code> and the same naming trick. <code>counterGuard x</code> is <code>.not (.equals (.var x) (.const 0))</code>; <code>BExpr.eval</code> turns <code>.equals a b</code> into <code>a.eval σ == b.eval σ</code>, which for <code>Nat</code> is <code>decide (… = …)</code>, and <code>.not</code> into <code>!</code>. Writing that out is the single most useful line in the proof for a reader: it says what the guard <i>is</i>.`
        },
        {
          "tac": "simp [Atom.eval, hx]",
          "h": `<code>Atom.eval σ (.var x)</code> becomes <code>σ x</code> becomes <code>0</code>; <code>Atom.eval σ (.const 0)</code> becomes <code>0</code>; <code>decide (0 = 0)</code> becomes <code>true</code>; <code>!true</code> becomes <code>false</code>.`
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "countdown_spec, from the top",
          "start": `x : Var
⊢ ∀ (n : Val),
    Hoare (fun σ x_1 => σ x = n) (countdown x) (aExists fun m => aAnd (fun σ x_1 => σ x = m) (bFalse (counterGuard x)))`,
          "steps": [
            {
              "tac": "refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_",
              "state": `case refine_1
x : Var
⊢ ∀ (n : Nat),
    Hoare (aAnd (fun σ x_1 => σ x = n + 1) (bTrue (counterGuard x))) (Cmd.assign x ((Atom.var x).minus (Atom.const 1)))
      fun σ x_1 => σ x = n

case refine_2
x : Var
⊢ ∀ (σ : Store) (h : Heap), σ x = 0 → BExpr.eval σ (counterGuard x) = false`,
              "h": `Two goals, exactly the rule's two obligations, already specialised. Three printing details: the anonymous binder <code>_</code> shows up as <code>x_1</code> because <code>x</code> is taken; <code>.minus (.var x) (.const 1)</code> comes back as <code>(Atom.var x).minus (Atom.const 1)</code>, dot notation on the first explicit argument and the opposite of what the source wrote; and <code>I 0</code> in <code>refine_2</code> has already been beta-reduced, because it was applied.`
            },
            {
              "tac": "intro n σ h hpre\nobtain ⟨hx, _⟩ := hpre",
              "state": `case refine_1
x : Var
n : Nat
σ : Store
h : Heap
hx : σ x = n + 1
right✝ : bTrue (counterGuard x) σ h
⊢ ∃ s',
    Exec (Cmd.assign x ((Atom.var x).minus (Atom.const 1))) { store := σ, heap := h } s' ∧
      (fun σ x_1 => σ x = n) s'.store s'.heap`,
              "h": `<code>hx</code> arrives already beta-reduced to <code>σ x = n + 1</code>: destructuring forces the application, where display does not.`
            },
            {
              "tac": "refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩",
              "state": `case refine_1
x : Var
n : Nat
σ : Store
h : Heap
hx : σ x = n + 1
right✝ : bTrue (counterGuard x) σ h
⊢ (fun σ x_1 => σ x = n) { store := σ.set x (σ x - 1), heap := h }.store { store := σ.set x (σ x - 1), heap := h }.heap`,
              "h": `This is the goal the <code>show</code> exists to fix: <code>σ.set x (σ x - 1) x = n</code> under four layers of unreduced notation. Note <code>Store.set σ x v</code> printing as <code>σ.set x v</code> — generalised field notation, because <code>Store.set</code>'s first explicit argument is a <code>Store</code>.`
            },
            {
              "tac": "show Store.set σ x (σ x - 1) x = n",
              "state": `case refine_1
x : Var
n : Nat
σ : Store
h : Heap
hx : σ x = n + 1
right✝ : bTrue (counterGuard x) σ h
⊢ σ.set x (σ x - 1) x = n`,
              "h": `One line, and the goal is something a human can check.`
            },
            {
              "tac": "show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false",
              "state": `case refine_2
x : Var
σ : Store
h : Heap
hI : σ x = 0
hx : σ x = 0
⊢ (!decide (Atom.eval σ (Atom.var x) = Atom.eval σ (Atom.const 0))) = false`,
              "h": `The second obligation, with the guard finally visible. Two <code>def</code>s and one <code>match</code> were unfolded by <code>show</code> — all definitional, all silent.`
            }
          ]
        },
        {
          "t": "detail",
          "title": "Are the two <code>show</code>s and the two <code>have</code>s necessary?",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `No — none of the four. <code>simp</code> unfolds structure projections applied to literals and beta-reduces on its own, and it accepts <code>hx</code> and <code>hI</code> at their unreduced types, so this shorter proof also compiles:`
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": `theorem countdown_spec' (x : Var) : ∀ n,
    Hoare (fun σ _ => σ x = n) (countdown x)
      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x))) := by
  refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_
  · intro n σ h hpre
    obtain ⟨hx, _⟩ := hpre
    refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩
    simp [Store.set, hx]
  · intro σ h hI
    simp [counterGuard, BExpr.eval, Atom.eval, hI]`
            },
            {
              "t": "p",
              "h": `The corpus proof is longer on purpose. A <code>show</code> is an assertion about what you believe the goal to be, checked by the kernel: change the definition of <code>counterGuard</code> and it fails on the spot, quoting both the pattern it expected and the target it got. The <code>simp</code>-only version fails too, three definitions deeper, with <code>⊢ False</code> and no indication of which edit caused it. Spelling out <code>(!(decide …)) = false</code> also documents, inside the script, what the guard evaluates to — which no reader could otherwise recover without unfolding three definitions by hand.`
            }
          ]
        }
      ],
      "pitfall": `Expecting <code>simp</code> to find a hypothesis by itself. Drop <code>hx'</code> from the bracket — write <code>simp [Store.set]</code> — and the step obligation does not close:<br><br><code>error: unsolved goals</code><br><code>case refine_1</code><br><code>x : Var</code><br><code>n : Nat</code><br><code>σ : Store</code><br><code>h : Heap</code><br><code>hx : σ x = n + 1</code><br><code>right✝ : bTrue (counterGuard x) σ h</code><br><code>⊢ σ x - 1 = n</code><br><br><code>simp</code> unfolded <code>Store.set</code>, collapsed the conditional, and stopped: <code>σ x</code> is an opaque application and nothing in the default set knows its value. The fact that would finish it is in the context, named, two lines up, unused. Whenever a <code>simp</code> mysteriously stops short, read the goal it left and ask which fact in your context would have closed it.<br><br>The quieter trap is truncated subtraction. With the body <code>x := x - 2</code> the step obligation asks for <code>n + 1 - 2 = n</code>, which is false for every <code>n ≥ 1</code> — but at <code>n = 0</code> it reads <code>1 - 2 = 0</code>, which truncation makes <i>true</i>. A sanity check at zero passes and tells you nothing.`,
      "variants": `<b>Replace the body with <code>x := 0</code>.</b> The step obligation becomes unprovable and Lean shows you precisely why. After <code>show Store.set σ x 0 x = n</code> and <code>simp [Store.set]</code> you are left holding:<br><br><code>case refine_1</code><br><code>x : Var</code><br><code>n : Nat</code><br><code>σ : Store</code><br><code>h : Heap</code><br><code>hx : σ x = n + 1</code><br><code>right✝ : bTrue (counterGuard x) σ h</code><br><code>⊢ 0 = n</code><br><br>That is the whole story of this rule's rigidity in one goal. The program terminates; the rule cannot see it, because the variant fell from <code>n + 1</code> to <code>0</code> rather than to <code>n</code>. The fix is to reindex with <code>I n := (σ x ≤ n)</code>, not to change the program.<br><br><b>Reverse the guard</b> to <code>.equals (.var x) (.const 0)</code>, so the loop runs while <code>x = 0</code>. Now <code>hstop</code> is false — at <code>σ x = 0</code> the guard is <i>true</i> — and the loop diverges. The failing obligation is <code>refine_2</code>, but with the proof as written it fails a line earlier than you would guess, at the <code>show</code>, which still carries the <code>!</code> of the old guard:<br><br><code>error: 'show' tactic failed, pattern</code><br><code>&nbsp;&nbsp;(!decide (Atom.eval σ (Atom.var x) = Atom.eval σ (Atom.const 0))) = false</code><br><code>is not definitionally equal to target</code><br><code>&nbsp;&nbsp;BExpr.eval σ (counterGuard x) = false</code><br><br>The <code>show</code> earning its keep: it fails at the guard and names the guard. Delete it and end with <code>simp [counterGuard, BExpr.eval, Atom.eval, hx]</code> instead and you get the blunter diagnosis, <code>⊢ False</code>. The obligation is not hard; it is untrue.<br><br><b>Instantiate at a concrete starting value.</b> Nothing to do — <code>countdown_spec x 17</code> is already a theorem about every store with <code>σ x = 17</code>. That is what proving <code>hoare_while_variant</code> once and instantiating it buys over reasoning about a particular run.`
    },
    {
      "t": "sec",
      "s": "Where the language runs out"
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "The honest limitation",
      "h": `<code>load</code>, <code>write</code> and <code>free</code> take a <b>literal</b> <code>Loc</code>, not an expression. You cannot dereference a pointer held in a variable, and therefore <b>the linked-list programs M10 was written for are not expressible in this language</b>. That is a real limitation of the design, not an oversight you can work around with cleverness.`
    },
    {
      "t": "p",
      "h": `It stayed invisible until now because every program in M6 through M12 names its locations outright. The moment a loop walks a structure, the address it touches on iteration <i>k</i> is a value computed by iteration <i>k−1</i>, and a syntax admitting only literal addresses cannot say so. Loops are where the restriction becomes a wall.`
    },
    {
      "t": "p",
      "h": `The refactor is mechanical. Three constructors change type:`
    },
    {
      "t": "code",
      "tag": "sketch",
      "cap": "The address-expression language. Only three lines differ.",
      "src": `inductive Cmd where
  | skip
  | assign : Var  → Atom → Cmd
  | load   : Var  → Atom → Cmd      -- x := [a]     address is an expression
  | write  : Atom → Atom → Cmd      -- [a] := e
  | free   : Atom → Cmd             -- free a
  | seq    : Cmd → Cmd → Cmd
  | ite    : BExpr → Cmd → Cmd → Cmd
  | loop   : BExpr → Cmd → Cmd`
    },
    {
      "t": "p",
      "h": `The semantics changes in one place — <code>s.heap l</code> becomes <code>s.heap (a.eval s.store)</code> — and the primitive rules pick up a pure side condition pinning the address:`
    },
    {
      "t": "code",
      "tag": "sketch",
      "src": `theorem hoare_load' (x : Var) (a : Atom) (l : Loc) (v : Val) :
    Hoare (aAnd (fact (fun σ => a.eval σ = l)) (l ↦ v))
          (.load x a)
          (pure (fun σ => σ x = v) ∗ (l ↦ v))`
    },
    {
      "t": "p",
      "h": `The address fact is pure and sits beside the ownership assertion rather than inside it, which is what keeps the rule small-footprint: the triple still owns exactly one cell. It is <code>hoare_write_val</code>'s trick one level over, with a fact pinning the address instead of the value. Everything downstream — locality, the frame rule, the <code>wp</code> equations — survives with the same proofs, because none of them inspects where an address came from.`
    },
    {
      "t": "p",
      "h": `With that, a traversal becomes writable, and the invariant it needs is the one <code>lseg</code> exists for. Split the heap into the part already walked and the part not yet walked, and let the body move the boundary:`
    },
    {
      "t": "txt",
      "src": `  invariant:
    ∃ visited remaining current,
        ⌜original = visited ++ remaining⌝
      ∗ ⌜count = visited.length⌝
      ∗ lseg    visited head current
      ∗ listRep remaining current

  variant:  remaining.length`
    },
    {
      "t": "p",
      "h": `<code>lseg_append</code> re-establishes the invariant after each step and <code>lseg_listRep</code> reassembles the list at the end. The program never modifies memory: the entire proof is about how one heap is <i>described</i> at each iteration. Disposal is the other shape — the invariant is only <code>∃ remaining current, listRep remaining current</code>, because nothing needs to be remembered about the freed prefix, and there the heap really shrinks.`
    },
    {
      "t": "p",
      "h": `Both of those still start from a list somebody else built. Every heap in this course has arrived by assumption; no constructor of <code>Cmd</code> makes a cell that was not there before, and nothing in the language can produce an address that is not written in the program text. Adding a command that returns one is the last piece — and it is a command with a choice to make, which is exactly the hypothesis <code>partial_of_total</code> was leaning on.`
    },
    {
      "t": "dod",
      "h": `You can distinguish partial from total correctness, prove the invariant rule by induction on a derivation, and supply a variant when termination matters.`
    }
  ]
});
