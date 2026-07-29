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
      `State both readings of a triple — <code>Hoare</code> (total) and <code>PartialHoare</code> (partial) — and say precisely which quantifier moved and what that costs.`,
      `Prove the structural rules in their partial form by <i>inverting</i> execution derivations instead of building them, which is the one systematic difference between the two readings.`,
      `Prove the while rule by induction on an <code>Exec</code> derivation, using the <code>cmd = .loop b₀ c₀</code> generalisation that is the only reason the induction goes through at all.`,
      `Supply a <b>variant</b> — a <code>Nat</code> that strictly decreases each iteration — and thereby upgrade a partial triple to a total one, so that termination is part of what you proved rather than something you asserted.`,
      `Verify a complete terminating program end to end, and exhibit the exact goal Lean leaves behind when the variant fails to decrease by one.`
    ],
    "needs": [
      `<code>Exec</code> from M5 — in particular the two loop constructors <code>loopFalse</code> and <code>loopTrue</code>, and the reading of <code>Exec c s s'</code> as “<code>c</code> terminates safely from <code>s</code> in <code>s'</code>”, not as a step relation.`,
      `<code>Hoare</code> from M6, read out loud as <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>. The existential is doing the work.`,
      `Inversion with <code>cases hex with | seq hex₁ hex₂ =&gt; …</code> (M5, M8, M12) and induction over a derivation with <code>induction hex with</code> (M5's <code>exec_deterministic</code>).`,
      `<code>aAnd</code>, <code>aExists</code> and <code>⊢</code> from M3, and the anonymous constructor <code>⟨…⟩</code> in both roles — as a term that builds an <code>∃</code>/<code>∧</code> and as a pattern in <code>intro</code>/<code>obtain</code>.`
    ],
    "payoff": `Every loop anybody has ever verified is verified by exactly these two moves: an assertion that survives one iteration, and a well-founded quantity that shrinks. Here you get both as theorems rather than slogans — and, just as important, you get a program for which the invariant rule is provable and the total triple is <i>false</i>, which is what the distinction is actually for.`
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": `Our <code>Cmd</code> has had <code>ite</code> and <code>loop</code> since M5; we simply never used them. Now we do, and the first thing that happens is that a distinction which was invisible becomes essential.`
    },
    {
      "t": "p",
      "h": `Up to now every command in every proof was <i>finite</i>: a sequence of assignments, loads, writes and frees. For such a command “it lands in <code>Q</code>” and “if it lands anywhere it lands in <code>Q</code>” say the same thing, because it always lands somewhere. A loop can fail to land anywhere. Once that is possible, the two sentences come apart, and you have to pick which one you are proving.`
    },
    {
      "t": "txt",
      "src": `  Hoare P c Q         ∀ σ h, P σ h → ∃ s', Exec c ⟨σ,h⟩ s' ∧ Q s'
                      "it terminates safely AND lands in Q"     — TOTAL

  PartialHoare P c Q  ∀ σ h s', P σ h → Exec c ⟨σ,h⟩ s' → Q s'
                      "IF it terminates, it lands in Q"         — PARTIAL`
    },
    {
      "t": "p",
      "h": `Both are already in scope; <code>PartialHoare</code> was defined alongside <code>Hoare</code> back in M6 and then ignored. Here it is again:`
    },
    {
      "t": "code",
      "src": `def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap`
    },
    {
      "t": "anat",
      "src": `def PartialHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h s', P σ h → Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap`,
      "parts": [
        {
          "m": "∀ σ h s'",
          "h": `All three are universally quantified <i>up front</i>, including the final state. In <code>Hoare</code> the final state is bound by an <code>∃</code> in the conclusion. That single relocation of one binder is the entire difference between the two definitions, and it is why the proofs below look like the M6 proofs with the arrows reversed.`
        },
        {
          "m": "P σ h →",
          "h": `Same as in <code>Hoare</code>: the precondition is a hypothesis you get to use.`
        },
        {
          "m": "Exec c ⟨σ, h⟩ s' →",
          "h": `Here is the move. In <code>Hoare</code> this <code>Exec</code> was part of the conclusion — you had to <i>produce</i> a derivation. Here it is a hypothesis — you are <i>handed</i> a derivation and your job is to take it apart. Concretely: M6's <code>hoare_skip</code> is the term <code>fun σ h hp =&gt; ⟨⟨σ, h⟩, Exec.skip, hp⟩</code>, built outwards from a constructor; here you will write <code>cases hex</code>.`
        },
        {
          "m": "Q s'.store s'.heap",
          "h": `Unchanged. <code>Q</code> wants a store and a heap and <code>s'</code> is a <code>State</code>, so it gets the two projections — the same small friction you have been paying since M6.`
        }
      ]
    },
    {
      "t": "cmp",
      "left": {
        "t": "M6 · <code>Hoare</code> (total)",
        "h": `The execution is <b>output</b>. Every proof ends by exhibiting a final state and a derivation reaching it. That is why every M6 proof has an <code>exact ⟨…, Exec.something, …⟩</code> at the bottom.`,
        "src": `∀ σ h, P σ h →
  ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap`
      },
      "right": {
        "t": "M13 · <code>PartialHoare</code>",
        "h": `The execution is <b>input</b>. Every proof begins by destructing a derivation someone else supplied. That is why every proof below has a <code>cases hex</code> near the top and no <code>Exec</code> constructor anywhere.`,
        "src": `∀ σ h s', P σ h →
  Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap`
      }
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": `Total implies partial — that direction is free, given determinism, and is proved below. It is the converse that fails. Once <code>loop</code> exists they genuinely differ, and the standard invariant rule proves only the partial one. Termination needs a separate argument — a <b>variant</b>. Divergence is not the only way to lose the converse, though; read the next note before you file this one away.`
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "“Terminates” here also means “does not fault”",
      "h": `Be precise about what <code>PartialHoare</code> forgives, because our semantics folds two failures into one. <code>Exec</code> has <i>no</i> rule for <code>load x l</code> when <code>l</code> is unallocated — a faulting run does not produce a bad derivation, it produces no derivation. So a hypothesis <code>Exec c ⟨σ,h⟩ s'</code> is vacuous for faulting runs exactly as it is for diverging ones, and <code>PartialHoare</code> is silent about both. You do not need a loop to separate the two readings — a single <code>load</code> of a cell you do not own does it:`
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "Loop-free, and still the two readings disagree: reading an unowned cell.",
      "src": `theorem load_partial_vacuous (x : Var) (l : Loc) (Q : Assertion) :
    PartialHoare emp (.load x l) Q := by
  intro σ h s' he hex
  cases hex with
  | load hl =>
      have : Heap.empty l = some _ := he ▸ hl
      exact absurd this (by simp [Heap.empty])

theorem load_not_total (x : Var) (l : Loc) :
    ¬ Hoare emp (.load x l) aTrue := by
  intro hc
  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty rfl
  cases hex with
  | load hl => exact absurd hl (by simp [Heap.empty])`
    },
    {
      "t": "p",
      "h": `<code>PartialHoare emp (.load x l) Q</code> holds for <i>every</i> <code>Q</code>, including <code>aFalse</code>. That is the honest reading of “partial correctness” in a semantics where getting stuck is modelled by the absence of a derivation: it means “if the command runs to completion without faulting, then <code>Q</code>”. Separation logic normally wants the stronger, total reading — which is precisely why <code>Hoare</code>, not <code>PartialHoare</code>, has been the default for the last seven chapters.`
    },
    {
      "t": "detail",
      "title": "How <code>load_partial_vacuous</code> actually closes",
      "tag": "Lean",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": `Six lines, and the interesting thing about them is that the goal is never touched. After <code>cases hex with | load hl</code>:`
        },
        {
          "t": "state",
          "src": `case load
x : Var
l : Loc
Q : Assertion
σ : Store
h : Heap
he : emp σ h
v✝ : Val
hl : { store := σ, heap := h }.heap l = some v✝
⊢ Q { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.store
    { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.heap`,
          "cap": "The goal you are not going to prove."
        },
        {
          "t": "p",
          "h": `<code>Q</code> is an arbitrary assertion applied to a pile of projections, and there is nothing to be done with it. The proof does not try: it derives a contradiction from the hypotheses instead, which discharges <i>any</i> goal.`
        },
        {
          "t": "ul",
          "items": [
            `<code>he : emp σ h</code>. <code>emp</code> is <code>fun _ h =&gt; h = Heap.empty</code>, so definitionally <code>he : h = Heap.empty</code> and it may be used as an equation without unfolding anything.`,
            `<code>v✝</code> is the loaded value. <code>cases</code> invented it from the <code>load</code> constructor's implicit binder <code>{v}</code>, and marked it inaccessible — you cannot type that name.`,
            `<code>he ▸ hl</code> transports <code>hl</code> along <code>h = Heap.empty</code> (the <code>▸</code> of M5's <code>exec_deterministic</code>), giving <code>Heap.empty l = some v✝</code>. This is the whole content of the proof: the run needs a cell, <code>emp</code> says there are none.`,
            `The <code>have</code> is written <code>Heap.empty l = some _</code> rather than <code>… = some v✝</code> precisely <i>because</i> the name is inaccessible. The underscore is recovered by unification against the type of <code>he ▸ hl</code>.`,
            `<code>simp [Heap.empty]</code> proves the negation: <code>Heap.empty l</code> reduces to <code>none</code>, and <code>none = some _</code> is refuted by the constructor-disjointness lemma <code>simp</code> already has for <code>Option</code>. <code>absurd</code> then turns a proposition and its negation into the goal, whatever the goal is.`
          ]
        },
        {
          "t": "p",
          "h": `<code>load_not_total</code> is the same fact read the other way. <code>hc (fun _ =&gt; 0) Heap.empty rfl</code> instantiates the total triple at the empty heap — the <code>rfl</code> is the proof of <code>emp</code>, since <code>emp (fun _ =&gt; 0) Heap.empty</code> unfolds to <code>Heap.empty = Heap.empty</code> — and <code>obtain</code> extracts the execution the triple promises. Inverting it produces the same impossible <code>Heap.empty l = some v</code>. Nothing about <code>Q</code> was used in either direction, which is the point.`
        }
      ]
    },
    {
      "t": "p",
      "h": `Because our semantics is deterministic, total implies partial:`
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
      "t": "trace",
      "title": "partial_of_total, tactic by tactic",
      "start": `P Q : Assertion
c : Cmd
h : Hoare P c Q
⊢ PartialHoare P c Q`,
      "steps": [
        {
          "tac": "intro σ hh s' hp hex",
          "state": `P Q : Assertion
c : Cmd
h : Hoare P c Q
σ : Store
hh : Heap
s' : State
hp : P σ hh
hex : Exec c { store := σ, heap := hh } s'
⊢ Q s'.store s'.heap`,
          "h": `<code>PartialHoare</code> is a <code>def</code>, so <code>intro</code> unfolds it silently and pulls in all five binders at once. Note what Lean printed for the state: the source says <code>⟨σ, h⟩</code>, Lean prints <code>{ store := σ, heap := hh }</code>. It is the same term — the anonymous constructor is notation for the structure literal — but from here on every goal in this chapter will show you the long form. Get used to reading it back as <code>⟨σ, hh⟩</code>.`
        },
        {
          "tac": "obtain ⟨s'', hex'', hq⟩ := h σ hh hp",
          "state": `P Q : Assertion
c : Cmd
h : Hoare P c Q
σ : Store
hh : Heap
s' : State
hp : P σ hh
hex : Exec c { store := σ, heap := hh } s'
s'' : State
hex'' : Exec c { store := σ, heap := hh } s''
hq : Q s''.store s''.heap
⊢ Q s'.store s'.heap`,
          "h": `The total hypothesis gives us an execution and a final state of <i>its</i> choosing, named <code>s''</code>. We are now holding two derivations from the same start state: <code>hex</code> for the state we were handed, <code>hex''</code> for the state <code>Hoare</code> produced. The goal mentions <code>s'</code>; the useful fact <code>hq</code> mentions <code>s''</code>. Closing that gap is the whole proof.`
        },
        {
          "tac": "have : s' = s'' := exec_deterministic hex hex''",
          "state": `P Q : Assertion
c : Cmd
h : Hoare P c Q
σ : Store
hh : Heap
s' : State
hp : P σ hh
hex : Exec c { store := σ, heap := hh } s'
s'' : State
hex'' : Exec c { store := σ, heap := hh } s''
hq : Q s''.store s''.heap
this : s' = s''
⊢ Q s'.store s'.heap`,
          "h": `Determinism from M5 says two derivations with the same command and the same start state have the same end state. <code>have</code> with no name introduces the hypothesis as <code>this</code> — perfectly idiomatic when the fact is used on the very next line.`
        },
        {
          "tac": "rw [this]",
          "state": `P Q : Assertion
c : Cmd
h : Hoare P c Q
σ : Store
hh : Heap
s' : State
hp : P σ hh
hex : Exec c { store := σ, heap := hh } s'
s'' : State
hex'' : Exec c { store := σ, heap := hh } s''
hq : Q s''.store s''.heap
this : s' = s''
⊢ Q s''.store s''.heap`,
          "h": `Rewriting left-to-right with <code>s' = s''</code> replaces <code>s'</code> everywhere in the goal. The goal is now literally the type of <code>hq</code>.`
        },
        {
          "tac": "exact hq",
          "state": `No goals.`,
          "h": `Done. Notice how little of this was about Hoare logic: the content is “determinism”, and the rest is bookkeeping.`
        }
      ]
    },
    {
      "t": "detail",
      "title": "Why determinism is needed, and where it is about to be taken away",
      "tag": "design",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": `Without determinism, <code>Hoare P c Q</code> only promises that <i>some</i> run lands in <code>Q</code> — the angelic reading flagged in M12's <code>wp_seq</code> discussion. A partial triple promises something about <i>every</i> run. One does not imply the other: a command with a good run and a bad run satisfies the total triple and refutes the partial one.`
        },
        {
          "t": "p",
          "h": `This is not a hypothetical. M14 adds nondeterministic allocation — “choose any unallocated location” — and the first casualty is <code>exec_deterministic</code>, and therefore this theorem. If you do that chapter, <code>partial_of_total</code> is one of the proofs you must revisit, and the fix is to change <code>Hoare</code> to the demonic reading, not to patch the proof.`
        }
      ]
    },
    {
      "t": "p",
      "h": `The converse fails, and it is worth having the counterexample in hand rather than in the abstract. Take the loop whose guard is a tautology and whose body does nothing:`
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "A command with no executions at all. Every partial triple about it holds; no total triple does.",
      "src": `def alwaysTrue : BExpr := .not (.equals (.const 0) (.const 1))

theorem alwaysTrue_eval (σ : Store) : alwaysTrue.eval σ = true := by
  simp [alwaysTrue, BExpr.eval, Atom.eval]

def spin : Cmd := .loop alwaysTrue .skip

theorem spin_diverges : ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = spin → False := by
  intro cmd s s' hex
  induction hex with
  | skip => intro heq; cases heq
  | assign => intro heq; cases heq
  | load _ => intro heq; cases heq
  | write _ => intro heq; cases heq
  | free _ => intro heq; cases heq
  | seq _ _ _ _ => intro heq; cases heq
  | iteTrue _ _ _ => intro heq; cases heq
  | iteFalse _ _ _ => intro heq; cases heq
  | loopFalse hb =>
      intro heq
      cases heq
      rw [alwaysTrue_eval] at hb
      exact Bool.noConfusion hb
  | loopTrue _ _ _ _ ihrest =>
      intro heq
      cases heq
      exact ihrest rfl

theorem spin_partial (Q : Assertion) : PartialHoare aTrue spin Q := by
  intro σ h s' _ hex
  exact (spin_diverges hex rfl).elim

theorem spin_not_total (Q : Assertion) : ¬ Hoare aTrue spin Q := by
  intro hc
  obtain ⟨s', hex, _⟩ := hc (fun _ => 0) Heap.empty trivial
  exact spin_diverges hex rfl`
    },
    {
      "t": "p",
      "h": `Read <code>spin_diverges</code> as: no derivation of <code>Exec</code> whatsoever has <code>spin</code> as its command. Its proof is the same generalisation trick you are about to meet in exercise 3, so it is worth a second look after you have done that one. Once you have it, <code>spin_partial</code> is one line — <code>(spin_diverges hex rfl).elim</code> is <code>False.elim</code> in dot notation, which turns the contradiction into whatever the goal happens to be. The consequence is that <code>spin</code> satisfies every partial triple, including <code>PartialHoare aTrue spin aFalse</code>. It satisfies a total triple only when the precondition is unsatisfiable: <code>Hoare P spin Q</code> demands a final state for each <code>P</code>-state, and there are none to be had, so it holds exactly when no state satisfies <code>P</code>.`
    },
    {
      "t": "h3",
      "s": "The two rules"
    },
    {
      "t": "p",
      "h": `Guards as assertions, so that the rules can be stated in the assertion language:`
    },
    {
      "t": "code",
      "src": `def bTrue (b : BExpr) : Assertion := fun σ _ => b.eval σ = true

def bFalse (b : BExpr) : Assertion := fun σ _ => b.eval σ = false`
    },
    {
      "t": "detail",
      "title": "Why lift the guard into an assertion at all",
      "tag": "design",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": `The obvious alternative is to write the side condition inline and keep the rule's precondition anonymous:`
        },
        {
          "t": "txt",
          "src": `  PartialHoare (fun σ h => P σ h ∧ b.eval σ = true) c₁ Q     -- inline
  PartialHoare (aAnd P (bTrue b))                    c₁ Q     -- what we do`
        },
        {
          "t": "p",
          "h": `These are the same proposition. The second one is worth two definitions because it is built out of <code>aAnd</code>, which means every entailment lemma from M3 and M4 applies to it unchanged. <code>and_left</code>, <code>and_intro</code>, <code>partialHoare_consequence</code>, <code>star_pure_left</code> — none of them know what <code>bTrue</code> is, and none of them need to. Inline lambdas would have to be unfolded by hand at every step.`
        },
        {
          "t": "p",
          "h": `The second reason is smaller but you will feel it immediately. Because <code>bTrue b σ h</code> unfolds definitionally to <code>b.eval σ = true</code>, the guard hypothesis that <code>cases hex</code> hands you fits into an <code>aAnd</code> pair with no coercion: you write <code>⟨hp, hb⟩</code> and Lean accepts it. Both exercises 2 and 3 rely on that.`
        },
        {
          "t": "p",
          "h": `Note also that <code>bTrue</code> ignores its heap argument — <code>fun σ _ =&gt; …</code>. Guards are pure store predicates in this language; there is no <code>[l] == 0</code> in <code>BExpr</code>. That is what makes the guard survive framing without any extra hypothesis, and it is the same simplification that keeps <code>counterGuard</code> below down to one line.`
        }
      ]
    },
    {
      "t": "p",
      "h": `Here is the rule the rest of the chapter is about. It is the oldest rule in program verification and it has not changed since Hoare wrote it down:`
    },
    {
      "t": "txt",
      "src": `       { I ∧ b } body { I }
  ───────────────────────────────────       (partial correctness)
   { I } loop b body { I ∧ ¬b }`
    },
    {
      "t": "p",
      "h": `The invariant <code>I</code> must be preserved by one iteration <i>given the guard</i>, and on exit you learn both <code>I</code> and the negation of the guard. That negation is where the useful information usually comes from.`
    },
    {
      "t": "steps",
      "title": "What the rule is asking you for, and what it gives back",
      "items": [
        {
          "k": "Establish I before the loop",
          "h": `Not part of the rule — it is the precondition of the triple you feed into <code>partialHoare_consequence</code>. In practice this is where most of the design work happens: you have to guess an <code>I</code> weak enough to hold on entry.`
        },
        {
          "k": "Preserve I across one iteration",
          "h": `The single hypothesis <code>hbody : PartialHoare (aAnd I (bTrue b)) c I</code>. You may assume the guard is true, because the body only runs when it is. Dropping <code>bTrue b</code> here would still give a sound rule, just a much weaker one — see the exercise's <b>variants</b>.`
        },
        {
          "k": "Read off the exit condition",
          "h": `The conclusion gives you <code>aAnd I (bFalse b)</code>. Almost always <code>I</code> alone is too weak to be the postcondition you wanted, and the extra conjunct <code>bFalse b</code> is what closes the gap — e.g. “<code>i ≤ n</code>” plus “not <code>i ≠ n</code>” gives “<code>i = n</code>”.`
        },
        {
          "k": "Say nothing about termination",
          "h": `Nothing in the three points above mentions how many iterations happen, and nothing could: the rule is provable for <code>spin</code>. This is a feature — it is why the rule is so cheap — but it means the conclusion is a <i>partial</i> triple and you cannot silently promote it.`
        }
      ]
    },
    {
      "t": "p",
      "h": `That last point deserves to be broken rather than asserted. Apply the rule to <code>spin</code> with <code>I := aTrue</code>. The body obligation is trivial, so you get a partial triple whose postcondition is <b>unsatisfiable</b>:`
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "The invariant rule, correctly applied, yielding a postcondition no state can satisfy.",
      "src": `theorem spin_body : PartialHoare (aAnd aTrue (bTrue alwaysTrue)) .skip aTrue := by
  intro σ h s' _ hex
  cases hex
  trivial

theorem spin_absurd_post : PartialHoare aTrue spin (aAnd aTrue (bFalse alwaysTrue)) :=
  partialHoare_while spin_body

theorem spin_post_is_false (σ : Store) (h : Heap) :
    ¬ aAnd aTrue (bFalse alwaysTrue) σ h := by
  intro ⟨_, hb⟩
  rw [show bFalse alwaysTrue σ h = (alwaysTrue.eval σ = false) from rfl] at hb
  rw [alwaysTrue_eval] at hb
  exact Bool.noConfusion hb`
    },
    {
      "t": "p",
      "h": `Two idioms in there are worth naming. <code>spin_body</code> ends <code>cases hex; trivial</code>: inverting <code>Exec .skip</code> pins the end state to the start state, and the remaining goal is <code>aTrue …</code>, which is <code>True</code> — <code>trivial</code> is the tactic for goals that are closed by a constructor with no arguments. And <code>spin_post_is_false</code> opens with <code>rw [show bFalse alwaysTrue σ h = (alwaysTrue.eval σ = false) from rfl] at hb</code>. That looks baroque and is doing something simple: <code>rw</code> needs an <i>equation</i> to rewrite with, and the only equation available here is the definitional one between the folded and unfolded forms of <code>bFalse</code>. <code>show T from rfl</code> is the term-level way to write it down. The alternative, <code>simp only [bFalse] at hb</code>, would do the same job.`
    },
    {
      "t": "p",
      "h": `Nothing here is wrong. <code>spin_absurd_post</code> is a true statement — it says “no execution of <code>spin</code> ends in a state satisfying an impossible assertion”, which is true because there are no executions. The lesson is that a partial triple with an absurd postcondition is <i>evidence of divergence</i>, not a proof of anything about a run.`
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>PartialHoare P c Q</code>",
          "h": `If <code>c</code> runs from a <code>P</code>-state to completion without faulting, the result satisfies <code>Q</code>. Vacuously true whenever <code>c</code> diverges or faults.`
        },
        {
          "k": "<code>bTrue b</code> / <code>bFalse b</code>",
          "h": `The guard <code>b</code> lifted to an <code>Assertion</code>, so that <code>aAnd</code> and every M3/M4 entailment lemma apply to it. Both ignore the heap.`
        },
        {
          "k": "<code>loop_invariant</code>",
          "h": `The generalised helper: the induction the while rule actually needs, with the command left as a variable and pinned down by an equation. Exercise 3.`
        },
        {
          "k": "<code>partialHoare_while</code>",
          "h": `The invariant rule itself. Two lines, once <code>loop_invariant</code> exists.`
        },
        {
          "k": "<code>hoare_while_variant</code>",
          "h": `The total-correctness rule. Same invariant, now indexed by a <code>Nat</code> that must fall by one each iteration and force the guard false at zero. Exercise 4.`
        },
        {
          "k": "<code>counterGuard</code> / <code>countdown</code>",
          "h": `The smallest concrete terminating program: <code>while x ≠ 0 do x := x - 1</code>. Exercise 5.`
        }
      ]
    },
    {
      "t": "sec",
      "s": "Exercises · partial correctness"
    },
    {
      "t": "ex",
      "id": "m13-1",
      "name": "partialHoare_skip / seq / consequence",
      "hard": false,
      "why": `The structural rules again, in the partial reading. Same proofs, one direction of quantification flipped. Doing all three in one sitting is the point: you want to feel that the <i>only</i> systematic change from M6 is that <code>Exec</code> moved from the conclusion to the hypotheses, so constructions become inversions. Everything else — how <code>P</code> is used, how <code>Q</code> is discharged — is untouched.`,
      "setup": `<code>PartialHoare</code>, <code>Entails</code> (<code>⊢</code>) and <code>Exec</code> are all in scope. You will not need a single <code>Exec</code> constructor in this exercise; if you find yourself typing <code>Exec.seq</code> you have taken a wrong turn.`,
      "goal": "theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P\n\ntheorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R\n\ntheorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :\n    PartialHoare P' c Q'",
      "hints": [
        `Start all three the same way. <code>PartialHoare</code> unfolds to a chain of five binders, so <code>intro σ h s' hp hex</code> gets you to a goal of the form <code>… s'.store s'.heap</code> with an <code>Exec</code> hypothesis in hand. Order matters: the state <code>s'</code> comes <i>before</i> the two implications.`,
        `For <code>seq</code>, invert the derivation to find the middle state instead of constructing it. <code>cases hex with | seq hex₁ hex₂ =&gt; …</code> splits <code>Exec (c₁ ;; c₂) ⟨σ,h⟩ s'</code> into the two halves — but look carefully at what Lean called the state between them.`,
        `Lean names the middle state <code>s'✝</code>, with a dagger: inaccessible, unusable. <code>rename_i sMid</code> renames the most recent inaccessible hypothesis. After that, <code>h₁ σ h sMid hp hex₁ : Q sMid.store sMid.heap</code>, and feeding that to <code>h₂</code> finishes.`,
        `For <code>consequence</code> nothing needs to be destructed at all: <code>hpre</code> converts <code>P'</code> to <code>P</code>, <code>hc</code> converts the whole thing to <code>Q</code> at <code>s'</code>, and <code>hpost</code> converts that to <code>Q'</code>. One <code>exact</code>, three nested applications.`
      ],
      "hint": `For <code>seq</code>, invert the derivation to find the middle state instead of constructing it.`,
      "sol": "theorem partialHoare_skip (P : Assertion) : PartialHoare P .skip P := by\n  intro σ h s' hp hex\n  cases hex; exact hp\n\ntheorem partialHoare_seq {P Q R : Assertion} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare P c₁ Q) (h₂ : PartialHoare Q c₂ R) :\n    PartialHoare P (c₁ ;; c₂) R := by\n  intro σ h s' hp hex\n  cases hex with\n  | seq hex₁ hex₂ =>\n      rename_i sMid\n      exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂\n\ntheorem partialHoare_consequence {P P' Q Q' : Assertion} {c : Cmd}\n    (hpre : P' ⊢ P) (hc : PartialHoare P c Q) (hpost : Q ⊢ Q') :\n    PartialHoare P' c Q' := by\n  intro σ h s' hp hex\n  exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)",
      "expl": `The contrast with M6 is instructive. In the total version you <i>build</i> the execution; in the partial version you are <i>given</i> one and take it apart. That is the whole difference between the two readings.`,
      "walk": [
        {
          "tac": "intro σ h s' hp hex",
          "h": `(<code>skip</code>) Unfolds <code>PartialHoare</code> and names all five binders. The goal is <code>P s'.store s'.heap</code> and you are holding <code>hex : Exec Cmd.skip { store := σ, heap := h } s'</code>.`
        },
        {
          "tac": "cases hex; exact hp",
          "h": `<code>Exec .skip</code> has exactly one constructor, and it forces the end state to equal the start state. So <code>cases hex</code> substitutes <code>s' := { store := σ, heap := h }</code> throughout and the goal becomes <code>P { store := σ, heap := h }.store { store := σ, heap := h }.heap</code>. Structure projections applied to a structure literal reduce, so that <i>is</i> <code>P σ h</code>, which is <code>hp</code>. <code>exact</code> checks up to definitional equality, so it goes through with no rewriting.`
        },
        {
          "tac": "intro σ h s' hp hex",
          "h": `(<code>seq</code>) Identical opening. <code>hex : Exec (c₁ ;; c₂) { store := σ, heap := h } s'</code>.`
        },
        {
          "tac": "cases hex with",
          "h": `Inversion. Only one constructor of <code>Exec</code> can produce a <code>;;</code> command, so exactly one case survives.`
        },
        {
          "tac": "| seq hex₁ hex₂ =>",
          "h": `Names the two sub-derivations. The <code>seq</code> constructor also carries three implicit states and two implicit commands; you are naming only the explicit fields, so the middle state arrives unnamed.`
        },
        {
          "tac": "rename_i sMid",
          "h": `The middle state was introduced as <code>s'✝</code> — an inaccessible name you cannot type. <code>rename_i</code> renames trailing inaccessible hypotheses, most recent last; one argument renames the last one. Now <code>sMid : State</code>, <code>hex₁ : Exec c₁ { store := σ, heap := h } sMid</code>, <code>hex₂ : Exec c₂ sMid s'</code>.`
        },
        {
          "tac": "exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂",
          "h": `<code>h₁ σ h sMid hp hex₁ : Q sMid.store sMid.heap</code> — the precondition and the first half of the run give you <code>Q</code> at the middle state. <code>h₂</code> then wants exactly a store, a heap, a final state, a <code>Q</code> at that store and heap, and a derivation; all five are to hand. Note you must pass the projections <code>sMid.store sMid.heap</code>, not <code>sMid</code>: <code>PartialHoare</code> takes a store and a heap, not a <code>State</code>.`
        },
        {
          "tac": "intro σ h s' hp hex",
          "h": `(<code>consequence</code>) Third time. <code>hp : P' σ h</code> now, because the precondition of the triple being proved is <code>P'</code>.`
        },
        {
          "tac": "exact hpost s'.store s'.heap (hc σ h s' (hpre σ h hp) hex)",
          "h": `Read it inside out. <code>hpre σ h hp : P σ h</code> — an <code>Entails</code> is literally a function <code>∀ σ h, P σ h → Q σ h</code>, so it applies. <code>hc σ h s' … hex : Q s'.store s'.heap</code>. <code>hpost s'.store s'.heap …  : Q' s'.store s'.heap</code>. No tactic reasoning at all; this is a term.`
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "partialHoare_skip",
          "start": `P : Assertion
⊢ PartialHoare P Cmd.skip P`,
          "steps": [
            {
              "tac": "intro σ h s' hp hex",
              "state": `P : Assertion
σ : Store
h : Heap
s' : State
hp : P σ h
hex : Exec Cmd.skip { store := σ, heap := h } s'
⊢ P s'.store s'.heap`,
              "h": `Five binders in one <code>intro</code>. <code>.skip</code> in the source is printed back as <code>Cmd.skip</code>: the dot-notation is elaboration-time sugar that resolves against the expected type, and the pretty-printer does not restore it.`
            },
            {
              "tac": "cases hex",
              "state": `case skip
P : Assertion
σ : Store
h : Heap
hp : P σ h
⊢ P { store := σ, heap := h }.store { store := σ, heap := h }.heap`,
              "h": `Two things happened. <code>s'</code> is <i>gone</i> from the context — the <code>skip</code> constructor pins the end state to the start state, so <code>cases</code> substituted it away rather than leaving an equation. And the goal now displays the projections un-reduced. Lean does not beta/iota-reduce goals for display; it reduces only when it has to.`
            },
            {
              "tac": "exact hp",
              "state": `No goals.`,
              "h": `<code>exact</code> compares the type of <code>hp</code> with the goal up to definitional equality, and <code>{ store := σ, heap := h }.store</code> reduces to <code>σ</code> by iota. No <code>simp</code>, no <code>rfl</code>, nothing to do.`
            }
          ]
        },
        {
          "t": "trace",
          "title": "partialHoare_seq — and where the middle state goes",
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
              "h": `Nothing surprising. The whole content of the proof is in <code>hex</code>.`
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
              "h": `There it is: <code>s'✝</code>. The dagger marks an <b>inaccessible</b> name. Lean invented it from the constructor's implicit binder <code>{s'}</code>, which already clashes with our <code>s'</code>, and marks it unusable so you cannot accidentally depend on a name you did not choose. It appears in the goal display and in the types of <code>hex₁</code> and <code>hex₂</code>, and you cannot write it.`
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
              "h": `<code>rename_i</code> takes the last <i>k</i> inaccessible hypotheses and gives them the <i>k</i> names you supply. Here <code>k = 1</code>. Now <code>sMid</code> is a name you can type, and the proof is a one-liner.`
            },
            {
              "tac": "exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂",
              "state": `No goals.`,
              "h": `The middle assertion <code>Q</code> is threaded through <code>sMid</code>. This is the same shape as <code>hoare_seq</code> in M6, read backwards.`
            }
          ]
        },
        {
          "t": "cmp",
          "left": {
            "t": "M6 · <code>hoare_seq</code>",
            "h": `Two <code>obtain</code>s pull final states out of the two hypotheses, and the proof ends by <i>gluing</i> the derivations together with the <code>Exec.seq</code> constructor. The middle state comes from <code>h₁</code>.`,
            "src": `intro σ h hp
obtain ⟨s₁, hex₁, hq⟩ := h₁ σ h hp
obtain ⟨s₂, hex₂, hr⟩ := h₂ s₁.store s₁.heap hq
exact ⟨s₂, Exec.seq hex₁ hex₂, hr⟩`
          },
          "right": {
            "t": "M13 · <code>partialHoare_seq</code>",
            "h": `One <code>cases</code> <i>splits</i> a given derivation, and the proof ends by applying the two hypotheses. The middle state comes from <code>hex</code>. Same three objects, opposite direction of travel.`,
            "src": `intro σ h s' hp hex
cases hex with
| seq hex₁ hex₂ =>
    rename_i sMid
    exact h₂ sMid.store sMid.heap s' (h₁ σ h sMid hp hex₁) hex₂`
          }
        },
        {
          "t": "detail",
          "title": "Alternatives to <code>rename_i</code>",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `You have three ways out of an inaccessible name, and it is worth knowing all three because different proofs make different ones natural.`
            },
            {
              "t": "ul",
              "items": [
                `<code>rename_i sMid</code> — rename after the fact. What the solution uses. Renames the last inaccessible hypothesis; <code>rename_i a b</code> renames the last two.`,
                `<code>cases hex with | @seq _ sMid _ _ _ hex₁ hex₂ =&gt; …</code> — prefixing the constructor with <code>@</code> makes its implicit binders nameable at the pattern. <code>Exec.seq</code> is declared <code>| seq {s s' s'' c₁ c₂} (h₁ …) (h₂ …)</code>, so <code>@seq</code> wants <b>seven</b> names in that order and the middle state is the <i>second</i>. More precise than <code>rename_i</code>, considerably noisier, and you have to get the arity exactly right — see below for what happens when you do not.`,
                `Never name it at all: write <code>h₁ σ h _ hp hex₁</code> and let unification recover the state from <code>hex₁</code>'s type. That works here, but the resulting line is harder to read, and it stops working the moment you need the state in two places.`
              ]
            },
            {
              "t": "p",
              "h": `The <code>@</code> form has a trap worth seeing once, because it fails in the least helpful way available. Write <code>| @seq sMid _ _ hex₁ hex₂ =&gt;</code> — five names instead of seven — and Lean does <b>not</b> object to the pattern. It binds them to the first five fields, in order: <code>sMid</code> to the <i>start</i> state <code>s</code>, the two underscores to <code>s'</code> (the state you actually wanted) and <code>s''</code>, and <code>hex₁</code>, <code>hex₂</code> to the two <i>commands</i>. Start state, end state and both commands are already fixed by the goal, so <code>cases</code> substitutes them away, and the only field you might have kept — the middle state — you spent an underscore on. Every name you wrote disappears, and the error you get is:`
            },
            {
              "t": "state",
              "src": `error(lean.unknownIdentifier): Unknown identifier \`sMid.store\`
error(lean.unknownIdentifier): Unknown identifier \`sMid.heap\`
error(lean.unknownIdentifier): Unknown identifier \`sMid\`
error(lean.unknownIdentifier): Unknown identifier \`hex₁\`
error(lean.unknownIdentifier): Unknown identifier \`hex₂\``,
              "cap": "Lean 4.32.2, all five reported on the one line that uses them."
            },
            {
              "t": "p",
              "h": `Five “unknown identifier” reports for five names that are sitting in your source, on the line above. This is the general shape of under-counted binder patterns in Lean and it is worth recognising on sight: the names bind, they just bind to the wrong things, and the complaint arrives at the point of <i>use</i>.`
            },
            {
              "t": "p",
              "h": `The same situation arose in M8's <code>heapLocal_seq</code> and M12's <code>wp_write</code> (<code>rename_i old</code>), for the same reason: <code>cases</code> introduces the constructor's implicit binders and those are always inaccessible.`
            }
          ]
        }
      ],
      "pitfall": `Getting the <code>intro</code> order wrong, which fails <i>silently</i> and then reports a nonsense error twenty characters later. <code>intro σ h hp s' hex</code> looks right — precondition before final state — but <code>PartialHoare</code> binds <code>s'</code> third, so <code>hp</code> becomes the name of the state and <code>s'</code> becomes the name of the proof of <code>P σ h</code>:<br><br><code>hp : State</code><br><code>s' : P σ h</code><br><code>hex : Exec Cmd.skip { store := σ, heap := h } hp</code><br><code>⊢ P hp.store hp.heap</code><br><br>Now <code>cases hex</code> substitutes the state away — that state is called <code>hp</code> — and the final line fails with <code>error(lean.unknownIdentifier): Unknown identifier &#96;hp&#96;</code>. The error names a hypothesis you can see in your own source, which is maximally confusing. When a name “disappears”, check the binder order in the definition first.`,
      "variants": `<b>Drop determinism.</b> Nothing in these three proofs uses <code>exec_deterministic</code>, so all three survive verbatim into a nondeterministic language. That is not an accident: partial correctness quantifies over all runs, which is exactly the demonic reading, so it is the robust notion. It is <code>partial_of_total</code> that breaks.<br><br><b>Reverse <code>seq</code>'s hypotheses.</b> If you swap and try to prove <code>PartialHoare P (c₁ ;; c₂) R</code> from <code>h₁ : PartialHoare P c₂ Q</code>, the <code>cases</code> still succeeds but <code>hex₁ : Exec c₁ …</code> no longer matches <code>h₁</code>'s command, and there is nothing you can do — the middle state is a real object with a real store and heap, and no lemma will let you commute the two halves.<br><br><b>Weaken <code>consequence</code> to <code>hpost : Q' ⊢ Q</code>.</b> The proof breaks at the last application, and the statement is false: strengthening a postcondition after the fact would let you conclude <code>aFalse</code> from any triple.`
    },
    {
      "t": "ex",
      "id": "m13-2",
      "name": "partialHoare_ite",
      "hard": false,
      "why": `The conditional is the smallest rule in which the guard <i>does something</i>, and it is the template for the loop rule that follows. Both branches get the same <code>P</code> and the same target <code>Q</code>; what distinguishes them is a single extra conjunct that inversion hands you for free. If you understand where <code>hb</code> comes from here, the <code>loopTrue</code> case of exercise 3 will not surprise you.`,
      "setup": `<code>bTrue</code> and <code>bFalse</code> are in scope, and <code>aAnd P Q σ h</code> unfolds to <code>P σ h ∧ Q σ h</code> — so the anonymous constructor <code>⟨_, _⟩</code> builds one directly.`,
      "goal": "theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q",
      "hints": [
        `<code>cases hex</code>: exactly two constructors can apply, and each hands you the guard evaluation you need.`,
        `The two cases are <code>iteTrue</code> and <code>iteFalse</code>. Each carries two explicit fields — the guard evaluation and the sub-derivation — so name them <code>hb</code> and <code>hex'</code>.`,
        `In the <code>iteTrue</code> case you have <code>hp : P σ h</code> and <code>hb : b.eval σ = true</code>, and <code>h₁</code> wants <code>aAnd P (bTrue b) σ h</code>. That is a conjunction, so build it with <code>⟨hp, hb⟩</code> — no unfolding needed, because <code>bTrue b σ h</code> <i>is</i> <code>b.eval σ = true</code> by definition.`
      ],
      "hint": `<code>cases hex</code>: exactly two constructors can apply, and each hands you the guard evaluation you need.`,
      "sol": "theorem partialHoare_ite {P Q : Assertion} {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : PartialHoare (aAnd P (bTrue b)) c₁ Q)\n    (h₂ : PartialHoare (aAnd P (bFalse b)) c₂ Q) :\n    PartialHoare P (.ite b c₁ c₂) Q := by\n  intro σ h s' hp hex\n  cases hex with\n  | iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'\n  | iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'",
      "expl": `Two lines. The inversion supplies <code>hb</code>, which is precisely the extra conjunct each branch hypothesis demands.`,
      "walk": [
        {
          "tac": "intro σ h s' hp hex",
          "h": `The usual opening. <code>hex : Exec (Cmd.ite b c₁ c₂) { store := σ, heap := h } s'</code>, goal <code>Q s'.store s'.heap</code>.`
        },
        {
          "tac": "cases hex with",
          "h": `Inversion on the <code>ite</code> command. Of the ten <code>Exec</code> constructors, only <code>iteTrue</code> and <code>iteFalse</code> can have produced this derivation, so Lean generates exactly two goals — and it will not let you write a case for a constructor that cannot fire: adding <code>| skip =&gt; …</code> gets you <code>error: Alternative &lsquo;skip&rsquo; is not needed</code>. The <code>with</code> block is checked against the cases that survive unification, not against the constructor list.`
        },
        {
          "tac": "| iteTrue hb hex'  => exact h₁ σ h s' ⟨hp, hb⟩ hex'",
          "h": `<code>hb : BExpr.eval { store := σ, heap := h }.store b = true</code> and <code>hex' : Exec c₁ { store := σ, heap := h } s'</code>. The pair <code>⟨hp, hb⟩</code> has type <code>P σ h ∧ b.eval σ = true</code>, which is <code>aAnd P (bTrue b) σ h</code> after unfolding two <code>def</code>s and one projection — all definitional, so <code>exact</code> accepts it silently.`
        },
        {
          "tac": "| iteFalse hb hex' => exact h₂ σ h s' ⟨hp, hb⟩ hex'",
          "h": `Verbatim mirror image, with <code>bFalse</code> and <code>h₂</code>. The symmetry is real: the two <code>Exec</code> constructors differ only in <code>= true</code> versus <code>= false</code> and in which branch they run.`
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
              "h": `Note that <code>h₁</code> and <code>h₂</code> print with <code>aAnd</code> and <code>bTrue</code> intact — Lean does not unfold <code>def</code>s for display. You have to remember that <code>aAnd P (bTrue b) σ h</code> means <code>P σ h ∧ b.eval σ = true</code>; the goal display will never tell you.`
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
              "h": `Read <code>hb</code> carefully, because this printing will recur all chapter. The constructor's field is <code>hb : b.eval s.store = true</code> with <code>s</code> instantiated to our start state, so Lean prints <code>BExpr.eval { store := σ, heap := h }.store b</code>: prefix form, structure literal, un-reduced projection. It is definitionally <code>b.eval σ</code> and <code>exact</code> will treat it as such — but no amount of staring will make Lean print it that way.`
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
              "h": `First goal closed; this is the second one, identical except for <code>= false</code>, <code>c₂</code>, and which hypothesis applies. <code>exact h₂ σ h s' ⟨hp, hb⟩ hex'</code> finishes it.`
            }
          ]
        },
        {
          "t": "p",
          "h": `The rule is <i>complete</i> as well as sound, in the sense that nothing was thrown away: the conditional's whole semantic content is “one of two constructors fired, and each tells you the guard's value”. Inversion recovers exactly that and no more.`
        }
      ],
      "pitfall": `Attaching <code>hb</code> to the wrong branch hypothesis. Swap <code>h₁</code> and <code>h₂</code> in the two cases and the error is not about the branch — it is about the guard:<br><br><code>error: Application type mismatch: The argument</code><br><code>&nbsp;&nbsp;hb</code><br><code>has type</code><br><code>&nbsp;&nbsp;BExpr.eval { store := σ, heap := h }.store b = true</code><br><code>but is expected to have type</code><br><code>&nbsp;&nbsp;bFalse b σ h</code><br><code>in the application</code><br><code>&nbsp;&nbsp;⟨hp, hb⟩</code><br><br>Note that the message compares an <i>unfolded</i> type against a <i>folded</i> one. That is normal in Lean: the elaborator reports what it had, not what it tried. Read <code>bFalse b σ h</code> as <code>b.eval σ = false</code> and the mismatch is obvious.`,
      "variants": `<b>Drop <code>bTrue b</code> from <code>h₁</code>'s precondition.</b> The rule stays sound — <code>PartialHoare P c₁ Q</code> is a stronger hypothesis than <code>PartialHoare (aAnd P (bTrue b)) c₁ Q</code>, so you could still finish with <code>exact h₁ σ h s' hp hex'</code>. But you have thrown away the only fact that distinguishes the branches, and no interesting conditional can be verified: “if <code>x = 0</code> then … else …” needs to know <code>x = 0</code> inside the first branch.<br><br><b>Swap <code>bTrue</code> and <code>bFalse</code>.</b> The statement becomes false, and Lean tells you so at the point where the guard is packed into the pair — see the pitfall. The failure is local and immediate, which is a nice property of stating guards as assertions rather than as side conditions.<br><br><b>Make guards heap-dependent.</b> If <code>BExpr</code> could dereference — <code>[l] == 0</code> — then <code>bTrue b</code> would no longer ignore its heap, and the rule as stated would still be true, but framing it would require the frame to leave <code>l</code> alone. That is the same argument as M8's <code>Preserves</code>, and it is why keeping guards pure is worth the loss of expressiveness.`
    },
    {
      "t": "ex",
      "id": "m13-3",
      "name": "the while rule",
      "hard": true,
      "why": `<b>The invariant rule.</b> The proof is by induction on the execution derivation, and it needs one standard piece of technique. That technique — generalise the index, then constrain it with an equation — is not about loops at all; it is the move you make whenever you want to induct on an inductively defined relation whose indices are not variables. You will use it in every proof assistant you ever touch, so it is worth the half hour.`,
      "setup": `<code>Exec</code>'s ten constructors are all in scope, and <code>induction hex with</code> will demand a case for each of them. The two that matter are <code>loopFalse</code> (guard false, state unchanged) and <code>loopTrue</code> (guard true, body, then the rest of the loop).`,
      "goal": "theorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b))",
      "hints": [
        `Try the direct proof first, and read the error. <code>intro σ h s' hI hex</code> then <code>induction hex</code> gives you <code>error: Invalid target: Index in target's type is not a variable (consider using the &lsquo;cases&rsquo; tactic instead)</code>, naming <code>Cmd.loop b c</code>. Understand that message before going further: the induction principle for <code>Exec</code> quantifies over <i>all</i> commands, and yours is pinned to a specific one.`,
        `You cannot induct directly, because the loop's command is fixed while the induction generalises it. Prove a helper with the command as a variable plus an equation constraining it: <code>∀ {cmd s s'}, Exec cmd s s' → cmd = .loop b₀ c₀ → I s → I s' ∧ ¬b</code>.`,
        `Order matters in the helper: <code>intro cmd s s' hex</code> and then <code>induction hex</code>, leaving the equation and <code>I s</code> <i>inside</i> the goal. That way every case's goal still begins <code>… = .loop b₀ c₀ → …</code>, and each case can <code>intro heq</code> for itself.`,
        `All the non-loop cases are killed by <code>cases heq</code>: the equation is between two distinct constructors of <code>Cmd</code>, which is impossible, and <code>cases</code> knows it. In <code>loopTrue</code>, <code>hbody</code> re-establishes <code>I</code> after one iteration and <code>ihrest rfl</code> handles the rest of the loop.`
      ],
      "hint": `You cannot induct directly, because the loop’s command is fixed while the induction generalises it. Prove a helper with the command as a variable plus an equation constraining it: <code>∀ {cmd s s'}, Exec cmd s s' → cmd = .loop b₀ c₀ → I s → I s' ∧ ¬b</code>. All the non-loop cases are killed by <code>cases heq</code>.`,
      "sol": "theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by\n  intro cmd s s' hex\n  induction hex with\n  | skip => intro heq; cases heq\n  | assign => intro heq; cases heq\n  | load _ => intro heq; cases heq\n  | write _ => intro heq; cases heq\n  | free _ => intro heq; cases heq\n  | seq _ _ _ _ => intro heq; cases heq\n  | iteTrue _ _ _ => intro heq; cases heq\n  | iteFalse _ _ _ => intro heq; cases heq\n  | loopFalse hb =>\n      intro heq hI\n      cases heq\n      exact ⟨hI, hb⟩\n  | loopTrue hb hbdy _ _ ihrest =>\n      intro heq hI\n      cases heq\n      exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)\n\ntheorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by\n  intro σ h s' hI hex\n  exact loop_invariant hbody hex rfl hI",
      "expl": `The <code>cmd = .loop b₀ c₀</code> trick is worth internalising — it is the standard way to induct on a derivation whose index you need to keep general. Every constructor except the two loop ones produces an impossible equation between distinct constructors, and <code>cases heq</code> discharges it by no-confusion. In <code>loopTrue</code>, <code>hbody</code> re-establishes <code>I</code> after one iteration and the induction hypothesis handles the rest; in <code>loopFalse</code>, you exit with <code>I</code> and the false guard. That is the informal argument, and the Lean proof has exactly those two lines of content.`,
      "walk": [
        {
          "tac": "intro cmd s s' hex",
          "h": `Introduce the command, both states and the derivation — but <b>not</b> the equation and <b>not</b> <code>I s.store s.heap</code>. Those two stay in the goal on purpose; that is what makes the induction hypothesis usable.`
        },
        {
          "tac": "induction hex with",
          "h": `Now the target of the induction is <code>Exec cmd s s'</code> with all three indices genuine variables, so Lean will accept it. Ten cases, and the goal in each one still ends in <code>… = Cmd.loop b₀ c₀ → I … → I … ∧ …</code>.`
        },
        {
          "tac": "| skip => intro heq; cases heq",
          "h": `In this case the goal's equation reads <code>Cmd.skip = Cmd.loop b₀ c₀</code>. <code>intro heq</code> names it; <code>cases heq</code> observes that <code>Cmd</code> is an inductive type, that <code>skip</code> and <code>loop</code> are different constructors, and that therefore no such equation exists. The case closes with no goals — this is <i>no-confusion</i>, generated automatically for every inductive type.`
        },
        {
          "tac": "| assign => intro heq; cases heq",
          "h": `Same, and identically for <code>load</code>, <code>write</code>, <code>free</code>, <code>seq</code>, <code>iteTrue</code> and <code>iteFalse</code> — seven more lines that differ only in how many constructor fields they bind with <code>_</code>. The underscore counts must match: <code>seq</code> has two sub-derivations plus two induction hypotheses, hence <code>| seq _ _ _ _ =&gt;</code>.`
        },
        {
          "tac": "| loopFalse hb =>",
          "h": `The exit case. <code>hb : BExpr.eval s✝.store b✝ = false</code>, where <code>b✝</code> is the constructor's own guard — not yet known to be <code>b₀</code>.`
        },
        {
          "tac": "intro heq hI",
          "h": `Now take both remaining hypotheses: <code>heq : Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀</code> and <code>hI : I s✝.store s✝.heap</code>.`
        },
        {
          "tac": "cases heq",
          "h": `This time the equation is between two <i>identical</i> constructors, so no-confusion gives injectivity instead of absurdity: <code>b✝ = b₀</code> and <code>c✝ = c₀</code>, which <code>cases</code> substitutes. The case is renamed <code>loopFalse.refl</code>, and <code>hb</code> now reads <code>BExpr.eval s✝.store b₀ = false</code> — which is exactly the second half of what we must prove.`
        },
        {
          "tac": "exact ⟨hI, hb⟩",
          "h": `Because <code>loopFalse</code> ends in the state it started in, the goal is <code>I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false</code> — the two hypotheses, paired.`
        },
        {
          "tac": "| loopTrue hb hbdy _ _ ihrest =>",
          "h": `Five binders: the guard evaluation, the body derivation, the rest-of-loop derivation (discarded — the induction hypothesis carries everything it says), the induction hypothesis for the body (useless: it would require <code>c₀ = .loop b₀ c₀</code>), and the induction hypothesis for the rest, which is the one that matters.`
        },
        {
          "tac": "intro heq hI",
          "h": `Same two hypotheses as before, but now <code>hI</code> is <code>I</code> at the state <i>before</i> the body runs.`
        },
        {
          "tac": "cases heq",
          "h": `Injectivity again: <code>b✝ := b₀</code>, <code>c✝ := c₀</code>. Crucially this also rewrites <code>ihrest</code>, whose hypothesis becomes <code>Cmd.loop b₀ c₀ = Cmd.loop b₀ c₀</code> — discharged by <code>rfl</code> on the next line.`
        },
        {
          "tac": "exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)",
          "h": `Read the inner application first. <code>hbody</code> is a <code>PartialHoare</code>, so it takes a store, a heap, a final state, a proof of <code>aAnd I (bTrue b₀)</code> and a derivation; the three underscores are the start store, start heap and the post-body state, all recoverable by unification from <code>hbdy</code>. It returns <code>I</code> at the post-body state. Then <code>ihrest rfl</code> takes that and runs the induction all the way to the end. Two applications; that is the entire mathematical content of the while rule.`
        },
        {
          "tac": "intro σ h s' hI hex",
          "h": `(<code>partialHoare_while</code>) Ordinary opening. Goal <code>aAnd I (bFalse b) s'.store s'.heap</code>, which is the conjunction the helper produces.`
        },
        {
          "tac": "exact loop_invariant hbody hex rfl hI",
          "h": `<code>rfl</code> discharges the side condition <code>Cmd.loop b c = Cmd.loop b c</code>. The three implicit arguments <code>cmd</code>, <code>s</code>, <code>s'</code> are inferred from <code>hex</code>. Note that <code>hI : I σ h</code> is accepted where <code>I { store := σ, heap := h }.store { store := σ, heap := h }.heap</code> is expected — projections of a literal, reducing as usual.`
        }
      ],
      "deep": [
        {
          "t": "steps",
          "title": "The generalisation trick, in three moves",
          "items": [
            {
              "k": "The problem",
              "h": [
                {
                  "t": "p",
                  "h": `The recursor for <code>Exec</code> proves a statement of the form <code>∀ cmd s s', Exec cmd s s' → M cmd s s'</code>. To use it, Lean has to read your goal as an instance of that shape — which means <code>cmd</code>, <code>s</code> and <code>s'</code> must be <i>variables</i> it can abstract over. In <code>partialHoare_while</code> the command is <code>Cmd.loop b c</code>, a constructor application. Lean cannot abstract it, and says so:`
                },
                {
                  "t": "state",
                  "src": `error: Invalid target: Index in target's type is not a variable (consider using the \`cases\` tactic instead)
  Cmd.loop b c`,
                  "cap": "Lean 4.32.2, verbatim."
                },
                {
                  "t": "p",
                  "h": `The suggestion to use <code>cases</code> is a red herring here: <code>cases</code> would give you the two loop cases with no induction hypothesis, and the <code>loopTrue</code> case needs one.`
                }
              ]
            },
            {
              "k": "The fix",
              "h": [
                {
                  "t": "p",
                  "h": `State a more general lemma in which the command <i>is</i> a variable, and put the constraint you actually want into an ordinary hypothesis:`
                },
                {
                  "t": "txt",
                  "src": `  ∀ {cmd s s'}, Exec cmd s s' → cmd = .loop b₀ c₀ → I s → I s' ∧ ¬b₀
                     ^^^^ variable        ^^^^^^^^^^^^^^^^^^ the constraint,
                                                             now a hypothesis`
                },
                {
                  "t": "p",
                  "h": `This is logically equivalent to the original — instantiate <code>cmd := .loop b₀ c₀</code> and supply <code>rfl</code> — but now the recursor applies. The cost is that you must handle all ten cases; the eight impossible ones cost one line each.`
                }
              ]
            },
            {
              "k": "Why the equation stays in the goal",
              "h": [
                {
                  "t": "p",
                  "h": `<code>intro cmd s s' hex</code> stops <i>before</i> the equation. Leaving it in the goal makes each case's induction hypothesis carry its own copy of the constraint — which is exactly what <code>ihrest rfl</code> consumes in the <code>loopTrue</code> case. The shape you saw after the <code>intro</code> — derivation in the context, everything else still under arrows — is the visible sign that this has been done right.`
                },
                {
                  "t": "p",
                  "h": `Be careful what you conclude from that, though, because Lean is more forgiving here than the folklore suggests. Lean 4's <code>induction</code> automatically reverts any context hypothesis that mentions the target's indices, and both <code>heq : cmd = …</code> and <code>hI : I s.store s.heap</code> do. So <code>intro cmd s s' hex heq hI</code> followed by <code>induction hex</code> also works: the two are reverted, generalised, and handed back in every case, and you can then delete all ten <code>intro heq</code>s. The corpus proof keeps them out of the context anyway, because doing it by hand is what makes the mechanism visible.`
                },
                {
                  "t": "p",
                  "h": `What the auto-revert does <i>not</i> cover is anything that does not mention an index. If the induction hypothesis has to be applicable at a different value of some other variable, you must revert that yourself, which is what <code>generalizing</code> is for — as in M5's <code>exec_deterministic</code>, <code>induction h₁ generalizing s₂</code>, where <code>s₂</code> is an index of <code>h₂</code> and not of <code>h₁</code>.`
                }
              ]
            }
          ]
        },
        {
          "t": "trace",
          "title": "loop_invariant — the four states that matter",
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
              "h": `Four things introduced, two implications left standing. That shape — a derivation in the context, everything else still under an arrow — is the signature of a proof that is about to induct.`
            },
            {
              "tac": "induction hex with | skip => …",
              "state": `case skip
I : Assertion
b₀ : BExpr
c₀ : Cmd
hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I
cmd : Cmd
s s' s✝ : State
⊢ Cmd.skip = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false`,
              "h": `The original <code>cmd</code>, <code>s</code>, <code>s'</code> are still in the context but are now inert — the induction abstracted over fresh copies, and <code>s✝</code> is the <code>skip</code> constructor's own state. The equation in the goal is <code>Cmd.skip = Cmd.loop b₀ c₀</code>: after <code>intro heq</code>, <code>cases heq</code> kills it.`
            },
            {
              "tac": "(the seq case, for contrast)",
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
              "h": `This is what the generalisation bought you: <code>h₁_ih✝</code> and <code>h₂_ih✝</code> are induction hypotheses that carry the constraint along. Here they are useless — the goal is impossible anyway — but the <code>loopTrue</code> case has the same shape and there the second one is the whole proof. Note also the <code>| seq _ _ _ _</code> pattern in the solution: four fields, two derivations and two induction hypotheses.`
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
              "h": `Look at the mismatch: <code>hb</code> is about <code>b✝</code>, the goal is about <code>b₀</code>. They are not yet the same guard — that information is locked up in <code>heq</code>.`
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
              "h": `<code>b✝</code> and <code>c✝</code> have vanished, substituted by <code>b₀</code> and <code>c₀</code>, and the case picked up a <code>.refl</code> suffix — that is <code>cases</code> on an equality, whose single constructor is <code>Eq.refl</code>. <code>hb</code> now literally matches the right conjunct. <code>exact ⟨hI, hb⟩</code>.`
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
              "h": `Everything you need, and one thing you do not. <code>hbody_ih✝</code> demands <code>c₀ = Cmd.loop b₀ c₀</code> — a body equal to the loop containing it, impossible for well-founded syntax — which is why the solution discards it with <code>_</code>. <code>ihrest</code>, by contrast, wants <code>Cmd.loop b₀ c₀ = Cmd.loop b₀ c₀</code>, i.e. <code>rfl</code>, and <code>I</code> at <code>s'✝</code>. Getting <code>I</code> at <code>s'✝</code> from <code>I</code> at <code>s✝</code> is precisely what <code>hbody</code> does, using <code>hb</code> as the second conjunct of its precondition.`
            },
            {
              "tac": "exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)",
              "state": `No goals.`,
              "h": `<code>hbdy : Exec c₀ s✝ s'✝</code> is accepted where <code>Exec c₀ { store := s✝.store, heap := s✝.heap } s'✝</code> is expected. That is structure <b>eta</b>: for a structure, <code>s</code> and <code>⟨s.store, s.heap⟩</code> are definitionally equal, so the two types are the same type. Lean 4 has this built in; without it, half the proofs in this chapter would need an explicit <code>cases s</code>.`
            }
          ]
        },
        {
          "t": "trace",
          "title": "partialHoare_while, once the helper exists",
          "start": `I : Assertion
b : BExpr
c : Cmd
hbody : PartialHoare (aAnd I (bTrue b)) c I
⊢ PartialHoare I (Cmd.loop b c) (aAnd I (bFalse b))`,
          "steps": [
            {
              "tac": "intro σ h s' hI hex",
              "state": `I : Assertion
b : BExpr
c : Cmd
hbody : PartialHoare (aAnd I (bTrue b)) c I
σ : Store
h : Heap
s' : State
hI : I σ h
hex : Exec (Cmd.loop b c) { store := σ, heap := h } s'
⊢ aAnd I (bFalse b) s'.store s'.heap`,
              "h": `Note the goal is still folded as <code>aAnd I (bFalse b) …</code>. It unfolds to <code>I s'.store s'.heap ∧ b.eval s'.store = false</code>, which is exactly <code>loop_invariant</code>'s conclusion.`
            },
            {
              "tac": "exact loop_invariant hbody hex rfl hI",
              "state": `No goals.`,
              "h": `Four arguments: the body obligation, the derivation, <code>rfl</code> for the constraint, and the invariant at the start. The generalisation was the whole difficulty; instantiating it back down is free.`
            }
          ]
        },
        {
          "t": "detail",
          "title": "What <code>cases heq</code> is doing, twice, in two different ways",
          "tag": "Lean",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `Every inductive type in Lean comes with an automatically generated <code>noConfusion</code> principle, which says two things at once:`
            },
            {
              "t": "ul",
              "items": [
                `<b>Disjointness.</b> Distinct constructors are never equal. So <code>Cmd.skip = Cmd.loop b₀ c₀</code> implies anything — including your goal. This is what closes the eight impossible cases.`,
                `<b>Injectivity.</b> The same constructor is equal only when its arguments are. So <code>Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀</code> yields <code>b✝ = b₀</code> and <code>c✝ = c₀</code>. This is what makes the two loop cases usable.`
              ]
            },
            {
              "t": "p",
              "h": `<code>cases</code> on an equality hypothesis invokes whichever half applies, and in the injective case it goes further and <i>substitutes</i>, so you never see the derived equations. That is why the goal after <code>cases heq</code> mentions <code>b₀</code> where it used to mention <code>b✝</code>, and why the case name gains <code>.refl</code>.`
            },
            {
              "t": "p",
              "h": `Two tactics do almost the same job and it is worth knowing why the solution picks this one. <code>injection heq</code> gives you the component equations as named hypotheses without substituting — more control, more lines. <code>subst heq</code> requires one side to be a free variable and would fail here, since both sides are constructor applications.`
            }
          ]
        },
        {
          "t": "cmp",
          "left": {
            "t": "What does not work",
            "kind": "bad",
            "h": `Induct on the derivation directly. Lean rejects the tactic before it starts, because <code>Cmd.loop b c</code> is not a variable it can abstract over.`,
            "src": `intro σ h s' hI hex
induction hex with
| loopFalse hb => exact ⟨hI, hb⟩
| loopTrue hb hbdy hrest ihb ihr => …

-- error: Invalid target: Index in target's
-- type is not a variable
--   Cmd.loop b c`
          },
          "right": {
            "t": "What works",
            "kind": "good",
            "h": `Generalise the command, keep the constraint as a hypothesis, and pay for it with eight one-line impossible cases.`,
            "src": `∀ {cmd s s'}, Exec cmd s s' →
  cmd = .loop b₀ c₀ →
  I s.store s.heap →
  I s'.store s'.heap ∧ b₀.eval s'.store = false`
          }
        }
      ],
      "pitfall": `Naming too few fields in a case pattern. <code>induction</code> hands you the constructor's own arguments <i>and</i> one induction hypothesis per recursive argument, so <code>loopTrue</code> has five fields, not three. Write <code>| loopTrue hb hbdy ihrest =&gt;</code> and Lean does not complain about the pattern: names bind to the leading fields, so <code>ihrest</code> silently becomes the rest-of-loop <i>derivation</i> and the two induction hypotheses stay inaccessible. The complaint arrives later, at the point of use:<br><br><code>error: Function expected at</code><br><code>&nbsp;&nbsp;ihrest</code><br><code>but this term has type</code><br><code>&nbsp;&nbsp;Exec (Cmd.loop b₀ c₀) s'✝ s''✝</code><br><br>The failure is asymmetric, which is worth knowing: too <i>many</i> names is caught immediately and precisely — <code>error: Too many variable names provided at alternative &lsquo;seq&rsquo;: 5 provided, but 4 expected</code> — while too few is caught nowhere. Count constructor arguments, then add one per recursive argument.<br><br>The second trap is forgetting what <code>hbody</code> eats. It is a <code>PartialHoare</code>, so before the pair it wants a store, a heap and a final state; that is what the three underscores in <code>hbody _ _ _ ⟨hI, hb⟩ hbdy</code> are. Drop them and the error names a type you never wrote:<br><br><code>error: Invalid ⟨...⟩ notation: The expected type &lsquo;Var → Val&rsquo; is not an inductive type</code><br><br><code>Var → Val</code> is <code>Store</code> — the pair went into the first argument slot. Whenever an error mentions a type you did not type, count the arguments of the function you are applying.`,
      "variants": `<b>Drop <code>bTrue b</code> from <code>hbody</code>.</b> The rule remains true and the proof still compiles if you also drop <code>hb</code> from the pair — but you have given up the guard, and with it every loop whose progress depends on the condition. Note the direction: this <i>weakens</i> the rule (a stronger hypothesis, same conclusion), it does not break it.<br><br><b>Drop <code>bFalse b</code> from the conclusion.</b> Also still true, also useless. Almost every real loop specification has the shape “invariant plus negated guard collapses to the postcondition”; without the second conjunct the rule can only tell you what you already knew.<br><br><b>Replace <code>PartialHoare</code> by <code>Hoare</code> in the conclusion.</b> Now it is <b>false</b>, and <code>spin</code> from the top of the chapter is the counterexample: take <code>I := aTrue</code> and <code>b := alwaysTrue</code>; the body obligation holds, the conclusion would assert that <code>spin</code> terminates, and <code>spin_not_total</code> says it does not. The single point of failure is the <code>loopTrue</code> case: the induction hypothesis is available only because a derivation of the rest of the loop was <i>handed to you</i>. With a total conclusion you would have to build that derivation, and there is nothing to build it from.<br><br><b>Make the body's invariant different from the loop's.</b> If <code>hbody</code> concluded <code>I'</code> rather than <code>I</code>, <code>ihrest</code> would want <code>I</code> and you would have <code>I'</code>. There is no fix; “the invariant is the same before and after” is not a convenience, it is what the word means.`
    },
    {
      "t": "sec",
      "s": "Exercises · total correctness"
    },
    {
      "t": "p",
      "h": `Partial correctness is silent about termination. The standard remedy is a <b>variant</b>: a natural number that strictly decreases on every iteration. We index the invariant by it.`
    },
    {
      "t": "p",
      "h": `There is a design choice hiding in that last sentence. On paper you would keep one invariant <code>I</code> and add a separate expression <code>V</code> over the store, with the obligations “<code>V</code> decreases” and “<code>V = 0</code> implies the guard is false”. Here we fold the two together into a family <code>I : Nat → Assertion</code>, so that <code>I n</code> means “the invariant holds <i>and</i> the variant currently equals <code>n</code>”:`
    },
    {
      "t": "cmp",
      "left": {
        "t": "The textbook shape",
        "h": `Two objects — an assertion and a numeric expression — and three obligations relating them. Faithful to how you would present it in a lecture, and awkward in Lean: <code>V</code> would have to be a <code>Store → Nat</code>, and every obligation would carry a hypothesis about its value.`,
        "src": `I : Assertion
V : Store → Nat

{ I ∧ b ∧ V = n } body { I ∧ V < n }
I ∧ V = 0  →  ¬b`
      },
      "right": {
        "t": "What we do",
        "h": `One object. <code>I n</code> is the invariant refined by “the variant is exactly <code>n</code>”, and the decrease is expressed by the <i>indices</i> of the two assertions rather than by an inequality. Induction on <code>n</code> then does all the work, with no well-foundedness argument to supply by hand.`,
        "src": `I : Nat → Assertion

∀ n, Hoare (aAnd (I (n+1)) (bTrue b)) c (I n)
∀ σ h, I 0 σ h → b.eval σ = false`
      }
    },
    {
      "t": "p",
      "h": `The price of the second form is rigidity: it demands the variant fall by <i>exactly</i> one. That is not a limitation of variants in general — it is a deliberate simplification, and exercise 5's <b>variants</b> note shows the exact goal Lean leaves behind when a program violates it.`
    },
    {
      "t": "ex",
      "id": "m13-4",
      "name": "hoare_while_variant",
      "hard": true,
      "why": `One iteration takes you from <code>I (n+1)</code> to <code>I n</code>; at <code>I 0</code> the guard must be false. Induction on <code>n</code> then <i>constructs</i> the terminating execution, so the conclusion is a total triple. This is the first proof in the chapter where you build an <code>Exec</code> derivation of unbounded depth — the recursion in the induction is what assembles it, one <code>Exec.loopTrue</code> per iteration.`,
      "setup": `You are back in <code>Hoare</code>-land, so every branch ends by exhibiting a state and a derivation. <code>Exec.loopFalse</code> and <code>Exec.loopTrue</code> are the two constructors you will need; nothing else.`,
      "goal": "theorem hoare_while_variant {I : Nat → Assertion} {b : BExpr} {c : Cmd}\n    (hstep : ∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n))\n    (hstop : ∀ σ h, I 0 σ h → b.eval σ = false) :\n    ∀ n, Hoare (I n) (.loop b c) (aExists fun m => aAnd (I m) (bFalse b))",
      "hints": [
        `Induct on <code>n</code>, not on a derivation — there is no derivation to induct on, you are producing one. So the shape is <code>intro n; induction n with | zero =&gt; … | succ n ih =&gt; …</code>.`,
        `Base case: the guard is false by <code>hstop</code>, so <code>Exec.loopFalse</code>. Step: case on the guard; if true, run the body then the induction hypothesis and glue with <code>Exec.loopTrue</code>; if false, exit immediately.`,
        `To case on the guard you need the resulting equation, so write <code>cases hbv : b.eval σ with</code>, not <code>cases b.eval σ with</code>. Without the <code>hbv :</code> you get two goals and no information, because <code>b.eval σ</code> does not occur in the goal for <code>cases</code> to substitute into.`,
        `Both existentials flatten. The goal is <code>∃ s', Exec … ∧ ∃ m, I m … ∧ …</code>, so a single anonymous constructor with five slots does it: <code>⟨state, derivation, m, invariant, guard⟩</code>. In the <code>zero</code> case that is <code>⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩</code>.`
      ],
      "hint": `Induct on <code>n</code>. Base case: the guard is false by <code>hstop</code>, so <code>Exec.loopFalse</code>. Step: case on the guard; if true, run the body then the induction hypothesis and glue with <code>Exec.loopTrue</code>; if false, exit immediately.`,
      "sol": "theorem hoare_while_variant {I : Nat → Assertion} {b : BExpr} {c : Cmd}\n    (hstep : ∀ n, Hoare (aAnd (I (n + 1)) (bTrue b)) c (I n))\n    (hstop : ∀ σ h, I 0 σ h → b.eval σ = false) :\n    ∀ n, Hoare (I n) (.loop b c) (aExists fun m => aAnd (I m) (bFalse b)) := by\n  intro n\n  induction n with\n  | zero =>\n      intro σ h hI\n      exact ⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩\n  | succ n ih =>\n      intro σ h hI\n      cases hbv : b.eval σ with\n      | true =>\n          obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩\n          obtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁\n          exact ⟨s₂, Exec.loopTrue hbv hex₁ hex₂, hpost⟩\n      | false =>\n          exact ⟨⟨σ, h⟩, Exec.loopFalse hbv, n + 1, hI, hbv⟩",
      "expl": `Note the shape of the postcondition: <code>∃ m, I m ∧ ¬b</code>, not <code>I 0 ∧ ¬b</code>. This is a correction worth making. The loop may exit early — the guard can become false while the variant is still positive — and in that case you land in <code>I (n+1)</code>, not <code>I 0</code>. Writing <code>I 0</code> in the conclusion makes the theorem unprovable, and the failing case is exactly the early exit. The existential is the honest statement.`,
      "walk": [
        {
          "tac": "intro n",
          "h": `The conclusion is <code>∀ n, Hoare …</code>, so name the variant's starting value. Everything after this is a statement about a fixed <code>n</code>.`
        },
        {
          "tac": "induction n with",
          "h": `Ordinary <code>Nat</code> induction. The induction hypothesis will be the whole triple at <code>n</code> — a <code>Hoare</code>, not a state — which is what lets the step case call it at a completely different store and heap.`
        },
        {
          "tac": "| zero =>",
          "h": `Goal: <code>Hoare (I 0) (Cmd.loop b c) …</code>. The variant is already at the bottom, so the loop must not iterate.`
        },
        {
          "tac": "intro σ h hI",
          "h": `Unfold <code>Hoare</code>. Goal: <code>∃ s', Exec (Cmd.loop b c) { store := σ, heap := h } s' ∧ aExists (fun m =&gt; aAnd (I m) (bFalse b)) s'.store s'.heap</code>.`
        },
        {
          "tac": "exact ⟨⟨σ, h⟩, Exec.loopFalse (hstop σ h hI), 0, hI, hstop σ h hI⟩",
          "h": `Five slots for two nested existentials and two conjunctions. The final state is the initial one; <code>Exec.loopFalse</code> needs the guard to be false, which is exactly <code>hstop σ h hI</code>; the witness for <code>m</code> is <code>0</code>; and the last two components are <code>I 0</code> and the false guard again. Note <code>hstop σ h hI</code> appears twice — once inside the derivation, once as the postcondition's second conjunct. That is not redundancy: they are proofs of the same proposition used in two different places.`
        },
        {
          "tac": "| succ n ih =>",
          "h": `<code>ih : Hoare (I n) (Cmd.loop b c) (aExists fun m =&gt; aAnd (I m) (bFalse b))</code> — the full triple one notch down.`
        },
        {
          "tac": "intro σ h hI",
          "h": `<code>hI : I (n + 1) σ h</code>. Now the loop may or may not run, and nothing so far tells you which.`
        },
        {
          "tac": "cases hbv : b.eval σ with",
          "h": `Split on the guard's actual value <i>and record the split</i>. The <code>hbv :</code> prefix is what produces <code>hbv : BExpr.eval σ b = true</code> in one branch and <code>= false</code> in the other; without it you would get two identical goals and no way to tell them apart.`
        },
        {
          "tac": "| true => obtain ⟨s₁, hex₁, hI₁⟩ := hstep n σ h ⟨hI, hbv⟩",
          "h": `The step obligation at index <code>n</code> has precondition <code>aAnd (I (n+1)) (bTrue b)</code>, and <code>⟨hI, hbv⟩</code> is exactly that pair. It returns a post-body state <code>s₁</code>, a derivation of the body, and <code>hI₁ : I n s₁.store s₁.heap</code> — the variant has dropped by one.`
        },
        {
          "tac": "obtain ⟨s₂, hex₂, hpost⟩ := ih s₁.store s₁.heap hI₁",
          "h": `Apply the induction hypothesis at the <i>new</i> store and heap. This is why <code>ih</code> had to be a full triple rather than a statement about the original <code>σ</code> and <code>h</code>. Out comes <code>hex₂ : Exec (Cmd.loop b c) { store := s₁.store, heap := s₁.heap } s₂</code> — the rest of the loop.`
        },
        {
          "tac": "exact ⟨s₂, Exec.loopTrue hbv hex₁ hex₂, hpost⟩",
          "h": `<code>Exec.loopTrue</code> takes the guard being true, a body derivation and a rest-of-loop derivation, and produces a derivation of the whole loop. The postcondition <code>hpost</code> is carried through unchanged — the existential <code>∃ m</code> was already resolved by the induction hypothesis, at whatever value it exited.`
        },
        {
          "tac": "| false => exact ⟨⟨σ, h⟩, Exec.loopFalse hbv, n + 1, hI, hbv⟩",
          "h": `<b>The early exit.</b> The guard is false even though the variant is <code>n + 1 &gt; 0</code>, so the loop stops here and the witness for <code>m</code> is <code>n + 1</code>, not <code>0</code>. This one line is the reason the postcondition is an existential.`
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
              "h": `An <code>∃</code> and, inside it, <code>aExists</code> — which is itself an <code>∃</code> under a <code>def</code>. Lean will not show you that; you have to know that <code>aExists P σ h</code> is <code>∃ x, P x σ h</code>. The five-slot anonymous constructor is exactly <code>⟨s', hex, m, left, right⟩</code>.`
            },
            {
              "tac": "| succ n ih => intro σ h hI; cases hbv : b.eval σ with | true =>",
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
⊢ ∃ s', Exec (Cmd.loop b c) { store := σ, heap := h } s' ∧ aExists (fun m => aAnd (I m) (bFalse b)) s'.store s'.heap`,
              "h": `<code>hbv</code> is the payoff of writing <code>cases hbv :</code>. Note that the goal is unchanged by the <code>cases</code> — <code>b.eval σ</code> does not appear in it — which is precisely why the equation had to be recorded explicitly.`
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
              "h": `Look at <code>hex₂</code>: its start state is <code>{ store := s₁.store, heap := s₁.heap }</code>, not <code>s₁</code>. That is because <code>Hoare</code> takes a store and a heap separately and rebuilds a <code>State</code> internally. <code>Exec.loopTrue hbv hex₁ hex₂</code> nevertheless typechecks, because structure eta makes <code>s₁</code> and <code>⟨s₁.store, s₁.heap⟩</code> the same term. If you ever meet a proof assistant without eta for structures, this is the line that breaks.`
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
              "h": `Here is the case the whole design of the postcondition exists for. <code>hI</code> says the variant is <code>n + 1</code>; there is no way to get from here to <code>I 0</code>, and none is needed — you supply <code>n + 1</code> as the witness. Hold this state in mind while reading the next block.`
            }
          ]
        },
        {
          "t": "p",
          "h": `The <code>expl</code> above says that writing <code>I 0</code> in the conclusion makes the theorem unprovable. That is a claim, so here is the refutation, in full. The instance is the degenerate one: a guard that is never true, so the loop always exits on its first test.`
        },
        {
          "t": "code",
          "tag": "illustration",
          "cap": "The strengthened rule, with I 0 in place of ∃ m, I m — refuted by a loop that exits immediately.",
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
          "h": `Read the last three lines. From the strengthened rule at <code>n = 1</code>, applied to the store that maps variable <code>0</code> to the value <code>1</code>, we obtain a final state whose store maps <code>0</code> to <code>0</code>. But the only execution of this loop is <code>loopFalse</code>, which changes nothing, so that store still maps <code>0</code> to <code>1</code>, and <code>Nat.noConfusion</code> closes the contradiction. The variant never moved; the guard was false from the start. That is the early exit, and it is not a corner case — it is what happens every time a loop finishes ahead of its worst-case bound.`
        },
        {
          "t": "detail",
          "title": "Why induction on <code>n</code> and not well-founded recursion",
          "tag": "design",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": `The general variant rule allows the measure to fall by any amount into any well-founded order. Formalising that means carrying an order, a proof it is well-founded, and an accessibility argument. Restricting to “falls by exactly one on <code>Nat</code>” replaces all of that with <code>induction n</code>, which Lean generates for free.`
            },
            {
              "t": "p",
              "h": `Nothing is lost in principle: if your real measure drops by more than one, reindex. Given <code>V</code> that falls from <code>V₀</code> to something smaller, take <code>I n := (the invariant) ∧ V ≤ n</code> and the obligations go through, because <code>V ≤ n + 1</code> and a decrease give <code>V ≤ n</code>. What is lost is convenience: you have to do that reindexing by hand, and exercise 5's <code>x := 0</code> variant shows exactly where the unreindexed version fails.`
            }
          ]
        }
      ],
      "pitfall": `Writing <code>cases b.eval σ with</code> instead of <code>cases hbv : b.eval σ with</code>. It <i>succeeds</i>. You get two goals, named <code>succ.true</code> and <code>succ.false</code>, with contexts that are identical and goals that are identical, because <code>b.eval σ</code> does not occur in the goal and so <code>cases</code> has nothing to substitute into. You then discover that you cannot build <code>⟨hI, ?⟩</code> for <code>hstep</code>, because nothing in scope says the guard is true. The tactic that failed is three lines above the error, which is the worst kind of failure to debug. Whenever you case on the value of an expression that is <i>not</i> in the goal, name the equation.<br><br>Second, smaller trap: <code>obtain ⟨s₂, hex₂, hpost⟩ := ih s₁ hI₁</code>. <code>ih</code> is a <code>Hoare</code>, which takes a store and a heap, not a <code>State</code>. Pass <code>s₁.store s₁.heap</code>.`,
      "variants": `<b>Drop <code>hstop</code>.</b> The base case becomes unprovable, and rightly so: with no link between <code>I 0</code> and the guard, a loop can sit at variant zero and keep iterating. Take <code>I n := aTrue</code>, <code>b := alwaysTrue</code> and body <code>.skip</code>: <code>hstep</code> holds trivially and the loop is <code>spin</code>, which does not terminate.<br><br><b>Weaken <code>hstep</code> to <code>Hoare (I (n+1)) c (I n)</code>, dropping the guard.</b> Sound but much weaker, exactly as in exercise 3. Worse here, though: most real loop bodies only decrease the variant <i>because</i> the guard held.<br><br><b>Allow the variant to stay put.</b> Change <code>hstep</code> to <code>∀ n, Hoare (aAnd (I n) (bTrue b)) c (I n)</code> and the theorem is false: the index no longer measures anything, so nothing forces progress. <code>spin</code> refutes it again — but choose the family with care, because <code>hstop</code> still has to hold, and <code>I n := aTrue</code> flatly fails it. Take instead <code>I n := fun _ _ =&gt; n ≠ 0</code>, so <code>I 0</code> is unsatisfiable and <code>hstop</code> is vacuous while <code>I 1</code> is <code>aTrue</code>; with body <code>.skip</code> the modified <code>hstep</code> holds, and the conclusion at <code>n = 1</code> asserts that <code>spin</code> terminates. That the counterexample needs an unsatisfiable <code>I 0</code> is itself the content: the only thing stopping the loop was the pairing of <code>hstop</code> with a variant that actually falls.<br><br><b>Replace the postcondition by <code>aAnd (I 0) (bFalse b)</code>.</b> False; see the illustration above for the machine-checked refutation.`
    },
    {
      "t": "ex",
      "id": "m13-5",
      "name": "a loop that actually terminates",
      "hard": false,
      "why": `The smallest program whose termination is a theorem rather than an accident. This is where the <code>plus</code>/<code>minus</code> extension from M5 earns its two lines. It is also the first time in the chapter that you have to <i>choose</i> an invariant rather than being handed one, and the choice is instructive: the variant and the invariant are the same object.`,
      "setup": `<code>hoare_while_variant</code> from the previous exercise is available. <code>Store.set σ x v</code> is the store update from M5, and <code>Atom.eval σ (.minus a b)</code> is truncated <code>Nat</code> subtraction.`,
      "goal": "def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))\n\ndef countdown (x : Var) : Cmd :=\n  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))\n\ntheorem countdown_spec (x : Var) : ∀ n,\n    Hoare (fun σ _ => σ x = n) (countdown x)\n      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x)))",
      "hints": [
        `Take <code>I n := fun σ _ =&gt; σ x = n</code>. The step obligation is that after <code>x := x - 1</code> the store maps <code>x</code> to <code>n</code>, given it mapped it to <code>n + 1</code>. The stop obligation is that <code>σ x = 0</code> makes the guard false.`,
        `Apply the rule with <code>refine</code>, so the two obligations arrive as goals rather than as terms you have to supply inline, and name the invariant while you are there: <code>refine hoare_while_variant (I := fun n σ _ =&gt; σ x = n) ?_ ?_</code>.`,
        `Both goals close with one <code>simp</code>, and both need a hypothesis <i>listed in the simp set</i> — <code>simp</code> does not go looking through your context. The step goal is about <code>Store.set</code> and needs <code>σ x = n + 1</code>, so that <code>σ x - 1</code> becomes <code>n + 1 - 1</code>; the stop goal is about <code>BExpr.eval</code> and needs <code>σ x = 0</code>, so that <code>decide (σ x = 0)</code> becomes <code>true</code> and its negation <code>false</code>.`,
        `If the goal displayed is an unreadable pile of projections, use <code>show</code> to restate it in the form you actually want to prove. <code>show Store.set σ x (σ x - 1) x = n</code> and <code>show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false</code> are the two you need.`
      ],
      "hint": `Take <code>I n := fun σ _ => σ x = n</code>. The step obligation is that after <code>x := x - 1</code> the store maps <code>x</code> to <code>n</code>, given it mapped it to <code>n + 1</code>. The stop obligation is that <code>σ x = 0</code> makes the guard false.`,
      "sol": "def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))\n\ndef countdown (x : Var) : Cmd :=\n  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))\n\ntheorem countdown_spec (x : Var) : ∀ n,\n    Hoare (fun σ _ => σ x = n) (countdown x)\n      (aExists fun m => aAnd (fun σ _ => σ x = m) (bFalse (counterGuard x))) := by\n  refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_\n  · intro n σ h hpre\n    obtain ⟨hx, _⟩ := hpre\n    refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩\n    show Store.set σ x (σ x - 1) x = n\n    have hx' : σ x = n + 1 := hx\n    simp [Store.set, hx']\n  · intro σ h hI\n    have hx : σ x = 0 := hI\n    show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false\n    simp [Atom.eval, hx]",
      "expl": `The variant <i>is</i> the value of <code>x</code>, which is why the invariant is indexed by it. Both obligations are one <code>simp</code> each. Try replacing the body with <code>x := 0</code> and watch the step obligation fail — the variant must decrease by exactly one, so a program that jumps to zero needs a different (weaker, more general) variant rule.`,
      "walk": [
        {
          "tac": "refine hoare_while_variant (I := fun n σ _ => σ x = n) ?_ ?_",
          "h": `<code>refine</code> applies the lemma but leaves the two <code>?_</code> arguments as goals instead of demanding terms. The named argument <code>(I := …)</code> pins the invariant by hand — and it is worth knowing that here it is not <i>forced</i>. The goal's precondition is <code>fun σ _ =&gt; σ x = n</code> sitting under <code>∀ n</code>, so Lean faces <code>?I n =?= fun σ _ =&gt; σ x = n</code> with <code>n</code> a distinct bound variable. That is a <b>Miller pattern</b> — a metavariable applied to distinct local variables — and pattern unification solves it uniquely, so <code>refine hoare_while_variant ?_ ?_</code> compiles just as well, with the same two goals. Write <code>(I := …)</code> anyway, for two reasons. The invariant is the one thing in this proof you had to invent, and a script that does not say what it is has hidden its only idea. And the inference stops working the moment the precondition you are handed is not already literally of the form <code>I n</code> — which is the normal case, since for a real loop the invariant is strictly weaker than the precondition you start from.`
        },
        {
          "tac": "· intro n σ h hpre",
          "h": `First obligation, the step. <code>hpre : aAnd (fun σ _ =&gt; σ x = n + 1) (bTrue (counterGuard x)) σ h</code> — invariant at <code>n+1</code>, plus the guard.`
        },
        {
          "tac": "obtain ⟨hx, _⟩ := hpre",
          "h": `Split the conjunction and discard the guard. This body decrements <code>x</code> whatever the guard says, so the guard is genuinely unnecessary here — one of the rare cases where you can throw it away.`
        },
        {
          "tac": "refine ⟨⟨Store.set σ x (σ x - 1), h⟩, Exec.assign, ?_⟩",
          "h": `Build the total triple: the final state is the store with <code>x</code> decremented and the heap untouched, the derivation is <code>Exec.assign</code>, and the postcondition is left as a goal. <code>Exec.assign</code> takes no explicit arguments — its final state is determined by the constructor, and Lean checks it matches the one you wrote.`
        },
        {
          "tac": "show Store.set σ x (σ x - 1) x = n",
          "h": `The goal at this point reads <code>(fun σ x_1 =&gt; σ x = n) { store := σ.set x (σ x - 1), heap := h }.store { … }.heap</code>. <code>show</code> restates it in beta-reduced, projection-free form; it succeeds because the two are definitionally equal. This changes nothing for Lean and everything for you.`
        },
        {
          "tac": "have hx' : σ x = n + 1 := hx",
          "h": `A copy of <code>hx</code> under a name, with the type written out. <code>hx</code>'s type is already <code>σ x = n + 1</code>, so this line is not strictly necessary — it is there to make the subsequent <code>simp</code> call self-documenting about which fact it needs.`
        },
        {
          "tac": "simp [Store.set, hx']",
          "h": `<code>Store.set</code> unfolds to <code>if x = x then σ x - 1 else σ x</code>; <code>simp</code> discharges the <code>if</code> to <code>σ x - 1</code>, rewrites with <code>hx'</code> to <code>n + 1 - 1</code>, and arithmetic on <code>Nat</code> literals finishes. This is the only place truncated subtraction could have bitten, and it does not, because <code>hx'</code> guarantees the value is a successor.`
        },
        {
          "tac": "· intro σ h hI",
          "h": `Second obligation, the stop condition. <code>hI : σ x = 0</code>, goal <code>BExpr.eval σ (counterGuard x) = false</code>.`
        },
        {
          "tac": "have hx : σ x = 0 := hI",
          "h": `Again a named restatement. <code>hI</code>'s type is the application of the lambda we supplied for <code>I 0</code>; writing it out confirms that it really did reduce to what you expect.`
        },
        {
          "tac": "show (!(decide (Atom.eval σ (.var x) = Atom.eval σ (.const 0)))) = false",
          "h": `<code>counterGuard x</code> is <code>.not (.equals (.var x) (.const 0))</code>, and <code>BExpr.eval</code> turns <code>.equals a b</code> into <code>a.eval σ == b.eval σ</code>, which for <code>Nat</code> is <code>decide (… = …)</code>, and <code>.not</code> into <code>!</code>. Spelling this out is the single most useful line in the proof for a reader: it says exactly what the guard <i>is</i>.`
        },
        {
          "tac": "simp [Atom.eval, hx]",
          "h": `<code>Atom.eval σ (.var x)</code> becomes <code>σ x</code> becomes <code>0</code> by <code>hx</code>; <code>Atom.eval σ (.const 0)</code> becomes <code>0</code>; <code>decide (0 = 0)</code> becomes <code>true</code>; <code>!true</code> becomes <code>false</code>. Goal closed.`
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
              "h": `Two goals, exactly the two obligations of the rule, already specialised. Three printing details worth naming. The anonymous binder <code>_</code> is displayed as <code>x_1</code>, because <code>x</code> is taken. <code>.minus (.var x) (.const 1)</code> comes back as <code>(Atom.var x).minus (Atom.const 1)</code> — dot notation on the <i>first explicit argument</i>, which is the opposite of what the source wrote. And <code>I 0</code> in <code>refine_2</code> has already been beta-reduced to <code>σ x = 0</code>, because it was applied.`
            },
            {
              "tac": "intro n σ h hpre",
              "state": `case refine_1
x : Var
n : Nat
σ : Store
h : Heap
hpre : aAnd (fun σ x_1 => σ x = n + 1) (bTrue (counterGuard x)) σ h
⊢ ∃ s',
    Exec (Cmd.assign x ((Atom.var x).minus (Atom.const 1))) { store := σ, heap := h } s' ∧
      (fun σ x_1 => σ x = n) s'.store s'.heap`,
              "h": `<code>Hoare</code> unfolded. Note that the postcondition is an un-applied lambda applied to two projections — Lean will not reduce it for display, which is why the <code>show</code> two steps below earns its place.`
            },
            {
              "tac": "obtain ⟨hx, _⟩ := hpre",
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
              "h": `<code>hx</code> arrives already beta-reduced to <code>σ x = n + 1</code> — destructuring forces the application, unlike display. The discarded conjunct becomes <code>right✝</code>: <code>_</code> in an <code>obtain</code> pattern does not delete a hypothesis, it makes it inaccessible.`
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
              "h": `This is the goal the <code>show</code> exists to fix. It is <code>σ.set x (σ x - 1) x = n</code> with four layers of unreduced notation on top. Note <code>Store.set σ x v</code> printing as <code>σ.set x v</code>: generalised field notation, because <code>σ : Store</code> and <code>Store.set</code>'s first explicit argument is a <code>Store</code>.`
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
              "h": `One line, and the goal is now something a human can check. <code>show</code> does not change the proof state in any way Lean cares about — it changes the goal to a definitionally equal one — but it is the difference between a proof you can maintain and one you cannot.`
            },
            {
              "tac": "have hx' : σ x = n + 1 := hx\nsimp [Store.set, hx']",
              "state": `case refine_2
x : Var
σ : Store
h : Heap
hI : σ x = 0
hx : σ x = 0
⊢ BExpr.eval σ (counterGuard x) = false`,
              "h": `First obligation closed; this is the second, after <code>intro σ h hI</code> and the <code>have</code>. The goal is folded up inside <code>counterGuard</code> and <code>BExpr.eval</code>.`
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
              "h": `Now you can see the guard. Two <code>def</code>s and one <code>match</code> were unfolded by <code>show</code> — all definitional, all silent. <code>simp [Atom.eval, hx]</code> finishes: the two <code>Atom.eval</code>s become <code>0</code> and <code>0</code>, <code>decide (0 = 0)</code> becomes <code>true</code>, and <code>!true = false</code>.`
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
              "h": `No — none of the four. <code>simp</code> unfolds structure projections applied to literals and beta-reduces on its own, and <code>simp</code>'s argument list accepts <code>hx</code> and <code>hI</code> at their unreduced types, so this shorter proof also compiles:`
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
              "h": `The corpus proof is longer on purpose, and the difference is not cosmetic. A <code>show</code> is an assertion about what you believe the goal to be, checked by the kernel. Change the definition of <code>counterGuard</code> and the <code>show</code> fails on the spot, quoting both the pattern it expected and the target it got — the <b>variants</b> note below reverses the guard and shows that error verbatim. The <code>simp</code>-only version fails too, but three definitions deeper, with <code>⊢ False</code> and no indication of which edit caused it. Spelling out <code>(!(decide …)) = false</code> also documents, in the proof script, what the guard actually evaluates to — which no reader could otherwise recover without unfolding three definitions by hand.`
            }
          ]
        },
        {
          "t": "steps",
          "title": "Why this program terminates, in the terms the rule uses",
          "items": [
            {
              "k": "Pick the variant",
              "h": `The value of <code>x</code>. There is no other candidate — it is the only thing the program changes.`
            },
            {
              "k": "Pick the invariant",
              "h": `<code>I n := (σ x = n)</code>. Notice that it says nothing except where the variant is. That is unusual and it is why this is the smallest example: for a real loop, <code>I n</code> would be “the real invariant, <i>and</i> the variant is <code>n</code>”, and only the second conjunct would come from the counter.`
            },
            {
              "k": "Discharge the step",
              "h": `From <code>σ x = n + 1</code>, one execution of <code>x := x - 1</code> gives <code>σ x = n</code>. Truncated subtraction is harmless here precisely because the hypothesis guarantees a successor.`
            },
            {
              "k": "Discharge the stop",
              "h": `From <code>σ x = 0</code>, the guard <code>x ≠ 0</code> evaluates to <code>false</code>. This is the clause that rules out sitting at the bottom of the variant forever.`
            },
            {
              "k": "Read the conclusion",
              "h": `<code>∃ m, σ x = m ∧ ¬(x ≠ 0)</code>. Weaker than you might have hoped — but combine the two conjuncts and <code>m</code> is forced to be <code>0</code>, so nothing was actually lost. Working that out is a good five-minute exercise in the entailment calculus of M3.`
            }
          ]
        }
      ],
      "pitfall": `Expecting <code>simp</code> to find a hypothesis by itself. Drop <code>hx'</code> from the simp set — write <code>simp [Store.set]</code> — and the step obligation does not close:<br><br><code>error: unsolved goals</code><br><code>case refine_1</code><br><code>x : Var</code><br><code>n : Nat</code><br><code>σ : Store</code><br><code>h : Heap</code><br><code>hx : σ x = n + 1</code><br><code>right✝ : bTrue (counterGuard x) σ h</code><br><code>⊢ σ x - 1 = n</code><br><br><code>simp</code> unfolded <code>Store.set</code>, discharged the <code>if</code>, and then stopped: <code>σ x</code> is an opaque application and nothing in the default simp set knows its value. The fact that would finish it is in the context, named, two lines up, unused. <code>simp</code> uses local hypotheses only when you list them (or when you write <code>simp_all</code>). That is worth internalising as a first hypothesis whenever a <code>simp</code> “mysteriously” stops short: read the goal it left, and see which fact in your context would have finished it.<br><br>The second trap is quieter: forgetting that <code>Val = Nat</code> and subtraction is truncated. If the invariant had been <code>σ x = n</code> with the body <code>x := x - 2</code>, the step obligation would ask you to prove <code>n + 1 - 2 = n</code>, which is false for every <code>n ≥ 1</code> — but at <code>n = 0</code> it reads <code>1 - 2 = 0</code>, which truncation makes <i>true</i>. A sanity check at <code>n = 0</code> passes and tells you nothing.`,
      "variants": `<b>Replace the body with <code>x := 0</code>.</b> The step obligation becomes unprovable, and Lean shows you precisely why. After <code>show Store.set σ x 0 x = n</code> and <code>simp [Store.set]</code> Lean reports <code>error: unsolved goals</code> and leaves you holding:<br><br><code>case refine_1</code><br><code>x : Var</code><br><code>n : Nat</code><br><code>σ : Store</code><br><code>h : Heap</code><br><code>hx : σ x = n + 1</code><br><code>right✝ : bTrue (counterGuard x) σ h</code><br><code>⊢ 0 = n</code><br><br>That is the whole story of this rule's rigidity in one goal. The program does terminate; the rule as stated cannot see it, because the variant fell from <code>n + 1</code> to <code>0</code> rather than to <code>n</code>. The fix is to reindex — take <code>I n := (σ x ≤ n)</code> — not to change the program.<br><br><b>Reverse the guard</b> to <code>.equals (.var x) (.const 0)</code>, i.e. loop while <code>x = 0</code>. Now <code>hstop</code> is false: at <code>σ x = 0</code> the guard is <i>true</i>, so the loop cannot stop, and indeed it diverges. The failing obligation is <code>refine_2</code> — but with the proof as written it fails a line earlier than you would guess, at the <code>show</code>, which still carries the <code>!</code> of the old guard:<br><br><code>error: 'show' tactic failed, pattern</code><br><code>&nbsp;&nbsp;(!decide (Atom.eval σ (Atom.var x) = Atom.eval σ (Atom.const 0))) = false</code><br><code>is not definitionally equal to target</code><br><code>&nbsp;&nbsp;BExpr.eval σ (counterGuard x) = false</code><br><br>That is the <code>show</code> earning its keep, exactly as the detail block above claims: it fails at the guard and names the guard. Delete it and replace the last line with <code>simp [counterGuard, BExpr.eval, Atom.eval, hx]</code> and you get the clearer diagnosis — <code>simp</code> reduces the obligation all the way down and leaves you with <code>⊢ False</code>. The obligation is not hard; it is untrue.<br><br><b>Instantiate at a concrete starting value.</b> Nothing changes — the specification is universally quantified over <code>n</code> and over the store, so <code>countdown_spec x 17</code> is already a theorem about every store with <code>σ x = 17</code>, with no further work. That is the point of proving <code>hoare_while_variant</code> once and instantiating it, rather than reasoning about a particular run.`
    },
    {
      "t": "sec",
      "s": "Where this development stops, and what comes next"
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "The honest limitation",
      "h": `Our <code>load</code>, <code>write</code> and <code>free</code> take a <b>literal</b> <code>Loc</code>, not an expression. That means you cannot dereference a pointer held in a variable — and therefore <b>the linked-list capstones are not expressible in this language</b>. This is a real limitation of the design, not an oversight you can work around with cleverness.`
    },
    {
      "t": "p",
      "h": `It is worth being clear about why this was not obvious earlier. Every program verified in M6 through M12 mentions its locations explicitly, because every one of them was written to fit the rules being demonstrated. The moment a loop walks a data structure, the address it touches on iteration <i>k</i> is a value computed by iteration <i>k−1</i>, and a syntax that only admits literal addresses cannot express that. Loops are where the restriction stops being invisible.`
    },
    {
      "t": "p",
      "h": `The fix is mechanical and is the natural next milestone:`
    },
    {
      "t": "code",
      "tag": "sketch",
      "cap": "The address-expression refactor. Only three lines change.",
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
      "h": `The semantics changes in one place — <code>s.heap l</code> becomes <code>s.heap (a.eval s.store)</code> — and the primitive rules pick up a pure side condition fixing the address:`
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
      "h": `Note the shape of that precondition: a <i>pure</i> fact pinning the address, separated from the ownership assertion. That separation is what keeps the rule small-footprint — the triple still owns exactly one cell — and it is the same trick as <code>hoare_write_val</code> in M9, where a pure fact pinned the value being written.`
    },
    {
      "t": "p",
      "h": `Everything downstream — locality, the frame rule, the <code>wp</code> equations — goes through with the same proofs, because none of them inspects how the address was obtained. With that in place, the two capstones become reachable:`
    },
    {
      "t": "h4",
      "s": "Capstone A · length of a linked list"
    },
    {
      "t": "txt",
      "src": `  invariant:
    ∃ visited remaining current,
        ⌜original = visited ++ remaining⌝
      ∗ ⌜count = visited.length⌝
      ∗ lseg    visited head current
      ∗ listRep remaining current`
    },
    {
      "t": "p",
      "h": `The heap is split into the visited prefix and the untraversed suffix. The loop body <i>moves the boundary</i> and touches nothing else; <code>lseg_append</code> is what re-establishes the invariant after each step, and <code>lseg_listRep</code> is what reassembles the list at the end. Notice that the program never modifies memory — the entire proof is about how the same heap is <i>described</i> at each iteration.`
    },
    {
      "t": "p",
      "h": `The variant is <code>remaining.length</code>, and reindexing it into the <code>I : Nat → Assertion</code> form of <code>hoare_while_variant</code> is exactly the step exercise 4's detail block describes: <code>I n</code> becomes “the invariant above, with <code>remaining.length = n</code>”.`
    },
    {
      "t": "h4",
      "s": "Capstone B · dispose a linked list"
    },
    {
      "t": "txt",
      "src": `  precondition:   listRep xs head
  postcondition:  emp
  invariant:      ∃ remaining current, listRep remaining current
  variant:        remaining.length`
    },
    {
      "t": "p",
      "h": `Here the heap genuinely shrinks. The invariant is much simpler than in Capstone A because nothing needs to be remembered about the freed prefix — which is a nice illustration of the point that a good invariant owns exactly what the rest of the computation needs, and no more.`
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Where to pick this up",
      "h": `These two are the natural place to continue. The machinery is all proved; what is missing is the address-expression refactor and roughly a hundred lines of loop bookkeeping.`
    },
    {
      "t": "dod",
      "h": `You can distinguish partial from total correctness, prove the invariant rule by induction on a derivation, and supply a variant when termination matters.`
    }
  ]
});
