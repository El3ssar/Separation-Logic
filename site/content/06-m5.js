/* M5 — A tiny imperative language
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m5 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm5',
  num: 'M5',
  phase: 'Phase 2 · Program logic',
  title: 'A tiny imperative language',
  blurb: 'Syntax, a big-step relational semantics, and an executable interpreter proved to agree with it.',

  orient: {
    youWill: [
      'Read an <code>inductive … : … → Prop</code> as a set of inference rules, and say why the arrow before <code>Prop</code> is what lets <code>cases</code> discard nine constructors out of ten.',
      'Do <b>inversion</b>: take an execution hypothesis apart instead of reasoning about it.',
      'Run <code>induction</code> over a derivation, and say precisely why the <code>seq</code> case fails without <code>generalizing</code>.',
      'Write a fuel-indexed interpreter that Lean accepts as terminating, and prove it computes exactly the relation.',
      'Read a goal in which a hypothesis <i>displays</i> as an unreduced <code>match</code> and is definitionally the thing you want.'
    ],
    needs: [
      'M0’s <code>cases hl : e with …</code>, <code>obtain</code>, <code>subst</code>, and <code>update</code> with its four laws — <code>Store.set</code> is <code>update</code> retyped.',
      '<code>Heap.write</code> and <code>Heap.erase</code> from M1. Those are the only heap operations this language can perform.',
      'Nothing from M2–M4. <code>∗</code> does not occur in this chapter.'
    ],
    payoff: 'Every theorem in the rest of the workbook is a statement about <code>Exec</code>: a triple is one existential over it, the frame rule is a locality property of it, a loop invariant is an induction on it.'
  },

  blocks: [

    /* ================================================================
       1 — the grammar
       ================================================================ */

    { t: 'h3', s: 'Eight constructors' },

    { t: 'p', h: 'A command is a tree. Here is the whole grammar; <code>Atom</code> and <code>BExpr</code> are the two expression languages, both defined in the next section, and neither of them can fail.' },

    { t: 'code', src: `inductive Cmd where
  | skip
  | assign : Var → Atom → Cmd
  | load   : Var → Loc → Cmd
  | write  : Loc → Atom → Cmd
  | free   : Loc → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : BExpr → Cmd → Cmd → Cmd
  | loop   : BExpr → Cmd → Cmd

infixr:60 " ;; " => Cmd.seq` },

    { t: 'txt',
      cap: 'The eight constructors and the concrete syntax they stand for.',
      src: `  Cmd.skip                    skip
  Cmd.assign x e              x := e            (store only)
  Cmd.load   x l              x := [l]          (heap read  — can fault)
  Cmd.write  l e              [l] := e          (heap write — can fault)
  Cmd.free   l                free l            (deallocate — can fault)
  Cmd.seq    c₁ c₂            c₁ ;; c₂
  Cmd.ite    b c₁ c₂          if b then c₁ else c₂
  Cmd.loop   b c              while b do c` },

    { t: 'p', h: 'Three of the eight can fault, and they are the three that name a location: <code>load</code>, <code>write</code> and <code>free</code> all need the cell to be there. The other five compute on a total store or move control around, and cannot go wrong. Everything decided in this chapter is decided by those three.' },

    { t: 'p', h: '“Smallest” is a constraint, not modesty. Every constructor is a case in every later <code>cases</code> and every later <code>induction</code>, and the proofs in M8 and M13 are long already. So: three memory operations, allocation added in the optional M14, one variable assignment, three control constructs, nothing else.' },

    { t: 'note', kind: 'key', title: 'Why the loop constructors are here already',
      h: 'The obvious plan is to build the loop-free language now and extend it in M13. Resist it. Extending an inductive type means redoing every proof about it, because every <code>cases</code> and every <code>induction</code> acquires two new goals. Declare <code>ite</code> and <code>loop</code> today, ignore them until M13, and nothing ever gets reworked.' },

    { t: 'note', kind: 'warn', title: 'The limitation you are accepting',
      h: '<code>load : Var → Loc → Cmd</code> takes a <i>literal</i> location, not an expression. You can write <code>x := [7]</code> and not <code>x := [y]</code>: the language cannot compute an address. Making the address an <code>Atom</code> would force every heap rule in M7 to quantify over that expression’s value, doubling the bookkeeping for no new phenomenon. The price is paid in M10, whose linked-list predicates describe structures no program here can walk — following a next-pointer means loading from an address held in a variable. M10 accepts this rather than fighting it: its corpus is assertions and entailments, with no <code>Cmd</code>, no <code>Exec</code> and no triple in it.' },

    { t: 'detail', title: 'Why the semicolon is doubled', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'A single <code>;</code> is the tactic sequencer, and declaring <code>infixr:60 " ; " =&gt; Cmd.seq</code> really does break proofs — though not where you would guess. The declaration is accepted, and <code>def eg : Cmd := .skip ; .skip</code> elaborates fine. What breaks is every later tactic block, because <code>;</code> is now a <i>term</i>-level infix as well:' },
        { t: 'code', tag: 'sketch',
          src: `infixr:60 " ; " => Cmd.seq

theorem t {s s' : State} (h : Exec Cmd.skip s s') : s' = s := by
  cases h; rfl` },
        { t: 'state', cap: 'The first of two errors.',
          src: `Application type mismatch: The argument
  h
has type
  Exec Cmd.skip s s'
of sort \`Prop\` but is expected to have type
  Cmd
of sort \`Type\` in the application
  Cmd.seq h` },
        { t: 'p', h: 'The second is eight unsolved goals labelled <code>case skip</code>, <code>case assign</code>, and so on. Having failed to build <code>Cmd.seq h rfl</code>, <code>cases</code> ends up splitting a <i>command</i> instead of the derivation, and the <code>rfl</code> that should have closed the goal was swallowed by the notation. Doubling the token costs nothing and avoids all of it.' }
      ] },

    /* ================================================================
       2 — expressions and states
       ================================================================ */

    { t: 'h3', s: 'Expressions get a function, commands get a relation' },

    { t: 'p', h: 'Only the heap is partial, and that single asymmetry divides the labour for the rest of the chapter. Reading a variable cannot fail, so an expression is given by an evaluation function landing in <code>Val</code> with no <code>Option</code> anywhere. Reading a cell can fail, so a command needs something that can decline to produce an answer.' },

    { t: 'anat',
      src: `inductive Atom where
  | const : Nat → Atom
  | var   : Var → Atom
  | plus  : Atom → Atom → Atom
  | minus : Atom → Atom → Atom
  deriving Repr

def Atom.eval (σ : Store) : Atom → Val
  | .const v  => v
  | .var x    => σ x
  | .plus a b => a.eval σ + b.eval σ
  | .minus a b => a.eval σ - b.eval σ

def Store.set (σ : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else σ y

structure State where
  store : Store
  heap  : Heap`,
      parts: [
        { m: 'inductive Atom where', h: 'The first <code>inductive</code> declaration in the workbook. Two Lean facts to take from it. A constructor’s full name is <code>Atom.const</code>, and you may write <code>.const</code> wherever Lean already knows the expected type is <code>Atom</code> — that leading-dot form is used constantly below and is nothing but name resolution against the expected type. And Lean generates a <b>recursor</b> from the declaration; <code>cases</code> and <code>induction</code> are applications of it, which is why they are exhaustive.' },
        { m: 'deriving Repr', h: 'Generates a printer, so <code>#eval (Atom.plus (.const 3) (.var 1))</code> answers instead of failing. Nothing logical depends on it. <code>Cmd</code> and <code>State</code> do <i>not</i> derive it — <code>#eval bump</code> reports <i>could not synthesize a <code>Repr</code> or <code>ToString</code> instance for type <code>Cmd</code></i> — which is why the <code>#eval</code>s at the end of this chapter project a number out of the final state instead of printing it.' },
        { m: 'def Atom.eval (σ : Store) : Atom → Val', h: 'The store comes <i>first</i>; the <code>Atom</code> is the anonymous last argument consumed by the pattern match. That argument order is why every goal in this chapter prints <code>Atom.eval s.store e</code> where you wrote <code>e.eval s.store</code>.' },
        { m: '| .const v  => v', h: 'The equation <code>Atom.eval σ (.const v) = v</code> holds <b>definitionally</b>. So <code>rfl</code> proves it, and <code>exact</code> sees through it with no rewriting — which is the entire content of two cases of <code>run_complete</code>.' },
        { m: 'a.eval σ + b.eval σ', h: 'The recursive calls are on strict subterms of <code>.plus a b</code>, so Lean accepts this with no termination proof. Hold on to that: the interpreter at the end of the chapter is exactly the case where the trick is unavailable.' },
        { m: 'fun y => if y = x then v else σ y', h: 'This is M0’s <code>update</code>, retyped. <code>Store = Var → Val = Nat → Nat</code>, so <code>@Store.set = @update</code> holds by <code>rfl</code>, and <code>update_same</code>, <code>update_other</code>, <code>update_shadow</code> and <code>update_comm</code> are already lemmas about stores.' },
        { m: 'structure State where', h: 'A <code>structure</code> is a one-constructor inductive with named projections: build one with <code>⟨σ, h⟩</code>, take it apart with <code>s.store</code> and <code>s.heap</code>. Two states are equal exactly when both fields are, and Lean closes such a goal by <code>rfl</code> when the fields are syntactically equal.' }
      ] },

    { t: 'note', kind: 'warn', title: 'The printer will not echo what you wrote',
      h: 'Dot notation appears <i>on output</i> only when the receiver is the first explicit argument. In <code>Atom.eval (σ : Store) : Atom → Val</code> the <code>Atom</code> is second, so you write <code>e.eval s.store</code> and Lean prints <code>Atom.eval s.store e</code>. <code>Store.set (σ : Store) …</code> does take its receiver first, so the same goal prints <code>s.store.set x v</code> where the source says <code>Store.set s.store x v</code>. Both surprises occur in every goal state below, and in both cases it is the same term.' },

    { t: 'note', kind: 'info', title: 'A two-line extension worth making early',
      h: 'The syllabus gives <code>Atom</code> only <code>const</code> and <code>var</code>. That is enough through M12, but it makes every loop trivial, because no expression can ever change value. <code>plus</code> and <code>minus</code> cost two lines, break nothing (every later proof is generic in <code>e : Atom</code>), and let M13 verify a loop that terminates for a reason. Truncation costs nothing here: M13’s loop counts a variable down to zero and its invariant is stated in terms of the value that is actually there. <code>Val := Int</code> would break nothing and buy nothing, and it would make <code>#eval</code> output less readable.' },

    { t: 'code', src: `inductive BExpr where
  | equals : Atom → Atom → BExpr
  | not    : BExpr → BExpr

def BExpr.eval (σ : Store) : BExpr → Bool
  | .equals a b => a.eval σ == b.eval σ
  | .not b      => !(b.eval σ)` },

    { t: 'p', h: '<code>==</code> is the <code>Bool</code>-valued test, so <code>BExpr.eval</code> lands in <code>Bool</code>. That is a decision, and the alternative is the one a mathematician reaches for first.' },

    { t: 'cmp',
      left: { t: 'Rejected: guards are propositions', kind: 'bad',
              h: '<code>BExpr.eval : Store → BExpr → Prop</code>. Cleaner to read. But then the interpreter cannot branch on a guard without a <code>Decidable</code> instance conjured at every use, and the two <code>ite</code> rules of <code>Exec</code> acquire premises <code>φ</code> and <code>¬ φ</code> that no longer contradict each other by computation — you have to reason to kill the impossible branch.' },
      right: { t: 'Chosen: guards are booleans', kind: 'good',
               h: '<code>BExpr.eval : Store → BExpr → Bool</code>. The premises become <code>b.eval s.store = true</code> and <code>= false</code>, so a mismatched branch dies in one line: rewrite one with the other and you have <code>true = false</code>. Four of the ten cases of <code>exec_deterministic</code> are exactly that line.' } },

    /* ================================================================
       3 — the function Lean refuses
       ================================================================ */

    { t: 'h3', s: 'The semantics Lean refuses' },

    { t: 'p', h: 'Running a command is a partial function from states to states, so define it as one. Lean will not let you.' },

    { t: 'code', tag: 'sketch',
      cap: 'Every clause but one is structural. The <code>loop</code> clause calls itself at the <i>same</i> command.',
      src: `def runBad : Cmd → State → Option State
  | .skip, s => some s
  | .loop b c, s =>
      match b.eval s.store with
      | true  =>
          match runBad c s with
          | some s' => runBad (.loop b c) s'
          | none    => none
      | false => some s
  | _, _ => none` },

    { t: 'state', cap: 'What Lean says. The last four lines are a goal, not a message.',
      src: `fail to show termination for
  runBad
with errors
failed to infer structural recursion:
Cannot use parameter #1:
  failed to eliminate recursive application
    runBad (Cmd.loop b c) s'
Cannot use parameter #2:
  the type State does not have a \`.brecOn\` recursor

failed to prove termination, possible solutions:
  - Use \`have\`-expressions to prove the remaining goals
  - Use \`termination_by\` to specify a different well-founded relation
  - Use \`decreasing_by\` to specify your own tactic for discharging this kind of goal
b : BExpr
c : Cmd
s s' : State
⊢ False` },

    { t: 'p', h: 'Lean tries structural recursion on each argument in turn. Parameter #1 is the command, which does not get smaller. Parameter #2 is a <code>structure</code> with no recursion in it, so there is nothing to recurse on. It then falls back on well-founded recursion, cannot find an order either, and hands you <code>⊢ False</code> to prove.' },

    { t: 'p', h: 'There is a second objection, and it survives even if you defeat the first. The result is an <code>Option</code>, so <code>none</code> is one answer to two different questions. A program that reads an unallocated cell returns <code>none</code>. A program that loops forever returns <code>none</code>. Nothing in the type separates them, and a specification that ruled out only one of the two would be worthless.' },

    { t: 'p', h: 'Take the second objection seriously and the first dissolves. Stop asking for the answer. Define the relation.' },

    /* ================================================================
       4 — Exec
       ================================================================ */

    { t: 'sec', s: 'What it means to run one' },

    { t: 'p', h: '<code>Exec c s s\'</code>: starting from <code>s</code>, the command <code>c</code> terminates and ends in <code>s\'</code>. Ten rules, one for each way a command can finish.' },

    { t: 'anat',
      cap: 'The ten rules. Seven callouts, covering every feature of the declaration you will meet again.',
      src: `inductive Exec : Cmd → State → State → Prop where
  | skip {s} : Exec .skip s s
  | assign {s x e} :
      Exec (.assign x e) s ⟨Store.set s.store x (e.eval s.store), s.heap⟩
  | load {s x l v} (hl : s.heap l = some v) :
      Exec (.load x l) s ⟨Store.set s.store x v, s.heap⟩
  | write {s l e old} (hl : s.heap l = some old) :
      Exec (.write l e) s ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩
  | free {s l v} (hl : s.heap l = some v) :
      Exec (.free l) s ⟨s.store, Heap.erase s.heap l⟩
  | seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') :
      Exec (c₁ ;; c₂) s s''
  | iteTrue {s s' b c₁ c₂} (hb : b.eval s.store = true) (h : Exec c₁ s s') :
      Exec (.ite b c₁ c₂) s s'
  | iteFalse {s s' b c₁ c₂} (hb : b.eval s.store = false) (h : Exec c₂ s s') :
      Exec (.ite b c₁ c₂) s s'
  | loopFalse {s b c} (hb : b.eval s.store = false) :
      Exec (.loop b c) s s
  | loopTrue {s s' s'' b c} (hb : b.eval s.store = true)
      (hbody : Exec c s s') (hrest : Exec (.loop b c) s' s'') :
      Exec (.loop b c) s s''`,
      parts: [
        { m: 'inductive Exec : Cmd → State → State → Prop where', h: 'All three arguments sit <i>after</i> the colon, so they are <b>indices</b>, not parameters. That distinction is the entire reason <code>cases</code> can do inversion: Lean is allowed to unify the indices of your hypothesis with those of each constructor’s conclusion and discard the constructors that cannot match. Parameters are fixed across all constructors and are never unified away. Note also that you could not declare <i>this</i> relation with <code>Cmd</code> as a parameter — <code>inductive Exec (c : Cmd) : …</code> — because each rule concludes at a different command. Those are two faces of the same fact.' },
        { m: '| skip {s} : Exec .skip s s', h: 'Braces make <code>s</code> implicit: Lean recovers it from the indices when you write <code>Exec.skip</code>. The same <code>s</code> occupies both state positions, and that single repetition is the whole content of the first exercise — inversion reads it back out as an equation.' },
        { m: '(hl : s.heap l = some v)', h: 'A <b>premise</b>, in round brackets, therefore explicit: to build this derivation you must hand over a proof that the cell exists. There is no rule for loading from an unallocated location, so there is no derivation. This one hypothesis is the whole fault model of the language.' },
        { m: '⟨Store.set s.store x v, s.heap⟩', h: 'New store, unchanged heap. The <code>v</code> written into the store is the same <code>v</code> the premise found in the heap; the rule is what ties them together, and the <code>load</code> case of <code>exec_deterministic</code> is nothing but pulling the tie apart again.' },
        { m: '{s l e old}', h: '<code>old</code> is used only in the premise and does not appear in the conclusion. So the rule says: the cell must exist, and I do not care what is in it. That is the small-footprint shape M7 will write as <code>l ↦ _</code>, and it is why the <code>write</code> case of determinism is a bare <code>rfl</code> while <code>load</code> needs work.' },
        { m: '(h₁ : Exec c₁ s s\') (h₂ : Exec c₂ s\' s\'\')', h: 'Two recursive premises sharing an intermediate state. <code>s\'</code> is implicit, hence <i>existentially</i> quantified from outside: to prove <code>Exec (c₁ ;; c₂) s s\'\'</code> you must produce some <code>s\'</code>. Invert such a hypothesis and <code>cases</code> hands the intermediate state back as a fresh variable.' },
        { m: '(hrest : Exec (.loop b c) s\' s\'\')', h: 'The recursive premise is at the <i>same</i> command. That is legal for a relation — the derivation tree still gets smaller even though the command does not — and it is precisely the clause <code>runBad</code> choked on.' }
      ] },

    { t: 'txt',
      cap: 'The constructors, drawn the way you would write them on a blackboard.',
      src: `  Read each constructor as an inference rule:

      s.heap l = some v                      Exec c₁ s s'      Exec c₂ s' s''
    ─────────────────────────────────      ──────────────────────────────────
     Exec (load x l) s ⟨σ[x:=v], h⟩              Exec (c₁ ;; c₂) s s''


     b.eval s.store = true    Exec c s s'    Exec (loop b c) s' s''
    ──────────────────────────────────────────────────────────────
                       Exec (loop b c) s s''

  A proof of \`Exec c s s'\` IS a finite tree built from these rules.
  \`induction\` walks such a tree; \`cases\` looks at its last step only.` },

    { t: 'p', h: 'Nothing in the declaration mentions failure, and it does not need to. <code>load x l</code> with the cell absent matches no rule, so <code>Exec (.load x l) s s\'</code> has no proof for any <code>s\'</code>. A loop that never exits has no proof either: <code>loopFalse</code> needs the guard to be false and <code>loopTrue</code> needs a derivation for the rest of the loop, and there is neither. Faulting and diverging have become the same non-fact, which is what lets one <code>∃ s\'</code> in front of <code>Exec</code> exclude both at once.' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus; compiles against the M5 prelude. Two lines, and the second is the whole fault model.',
      src: `-- "stuck" is a theorem, not a convention: with the cell absent,
-- no final state exists at all.
theorem load_stuck (x : Var) (l : Loc) (s : State) (hl : s.heap l = none) :
    ¬ ∃ s', Exec (.load x l) s s' := by
  intro ⟨s', hex⟩
  cases hex with
  | load hl' => rw [hl] at hl'; exact absurd hl' (by simp)` },

    { t: 'p', h: 'That is the shape of every inversion argument in the chapter. <code>cases hex</code> leaves only the <code>load</code> rule; its premise <code>hl\' : s.heap l = some v</code> is rewritten by <code>hl</code> into <code>none = some v</code>, which <code>simp</code> refutes. <i>Rewrite one premise with the other, then refute</i> closes four of the ten cases of <code>exec_deterministic</code> as well.' },

    /* ================================================================
       5 — inversion
       ================================================================ */

    { t: 'sec', s: 'Reading a derivation backwards' },

    { t: 'p', h: 'A derivation is a term of an inductive family, so there are two things to do with it. <code>cases h</code> asks which rule was applied last, and gives one goal per rule that could have concluded what <code>h</code> concludes. <code>induction h</code> asks the same question and additionally hands you, in each recursive case, the statement you are proving already established for the sub-derivations. Inversion is induction with the hypotheses thrown away.' },

    { t: 'p', h: 'The cheapest inversion in the language: exactly one rule concludes at <code>.skip</code>, and it repeats its state.' },

    { t: 'ex',
      id: 'm5-1',
      name: 'exec_skip_inv',
      hard: false,
      why: 'Your first inversion. The habit it builds: when a hypothesis is a derivation you take it apart, rather than reasoning about it. You will not cite the resulting lemma again — the move is what you keep.',
      setup: 'Everything so far is in scope. You need no lemmas, only <code>cases</code> and <code>rfl</code>.',
      goal: 'theorem exec_skip_inv {s s\' : State} (h : Exec .skip s s\') : s\' = s',
      hints: [
        'You have a proof that something is in an inductively defined relation. Do to it what you would do to a proof of <code>A ∨ B</code>: split on how it was built.',
        '<code>cases h</code>. Nine of the ten constructors conclude with a command that is not <code>.skip</code>, and Lean discards them by unifying the indices. One goal survives.',
        'After <code>cases h</code> the goal is <code>s = s</code> — not <code>s\' = s</code> any more, because the constructor’s own equation eliminated <code>s\'</code>. So: <code>cases h; rfl</code>.'
      ],
      hint: '<code>cases h; rfl</code>.',
      sol: 'theorem exec_skip_inv {s s\' : State} (h : Exec .skip s s\') : s\' = s := by\n  cases h; rfl',
      expl: '<code>cases</code> unifies the indices of the relation with the constructor’s. <code>Exec.skip</code> has both states equal, so after <code>cases</code> the goal is <code>s = s</code>.',
      walk: [
        { tac: 'cases h', h: 'Lean unifies the indices of <code>h : Exec .skip s s\'</code> against the conclusion of each of the ten constructors. Only <code>Exec.skip : Exec .skip s s</code> matches on the command index, and unifying its two state indices with <code>s</code> and <code>s\'</code> forces <code>s\'</code> to <i>be</i> <code>s</code>, so Lean substitutes it away everywhere — including in the goal.' },
        { tac: 'rfl', h: 'The goal is <code>s = s</code>. Both sides are literally the same variable.' }
      ],
      deep: [
        { t: 'trace', title: 'exec_skip_inv, tactic by tactic',
          start: 's s\' : State\nh : Exec Cmd.skip s s\'\n⊢ s\' = s',
          steps: [
            { tac: 'cases h',
              state: 'case skip\ns : State\n⊢ s = s',
              h: 'Everything changed at once. <code>s\'</code> is gone from the context — not renamed, <i>eliminated</i>, because the <code>skip</code> rule can only conclude with the two states equal. The <code>case skip</code> line names the surviving constructor; there is no <code>case assign</code> and no <code>case load</code>, because neither can conclude <code>Exec Cmd.skip _ _</code>. Note also that you wrote <code>.skip</code> and Lean prints <code>Cmd.skip</code>: the leading dot is elaboration-time sugar and does not survive into the term.' },
            { tac: 'rfl', state: 'No goals.', h: '' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'Why the goal is not <code>s\' = s\'</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Unifying <code>Exec .skip s s\'</code> with <code>Exec .skip ?s ?s</code> gives <code>?s = s</code> from the first index and <code>?s = s\'</code> from the second, hence <code>s = s\'</code>. Lean substitutes one for the other and keeps whichever was introduced <i>earlier</i>, which is <code>s</code>. It never matters, but it does explain why the variable that vanishes is sometimes not the one you expected.' }
          ] }
      ],
      pitfall: 'Reaching for <code>rw [h]</code> or <code>exact h.symm</code>. <code>h</code> is not an equation, it is a derivation. The equation you want is <i>extracted</i> from it by case analysis; it is not sitting there waiting to be used.',
      variants: 'Try the same statement for <code>load</code>: <code>(h : Exec (.load x l) s s\') : ∃ v, s.heap l = some v ∧ s\' = ⟨Store.set s.store x v, s.heap⟩</code>. Now <code>cases h with | load hl =&gt; …</code> hands you the premise <code>hl</code> and the shape of <code>s\'</code> together, and <code>exact ⟨_, hl, rfl⟩</code> finishes. The pattern is general: inversion on a constructor with <i>k</i> premises gives you those <i>k</i> premises plus the equations its indices force. For <code>skip</code>, <i>k</i> = 0 and there is one equation, which is why this exercise is one line.'
    },

    /* ================================================================
       6 — determinism
       ================================================================ */

    { t: 'sec', s: 'Two derivations, one command' },

    { t: 'p', h: 'Determinism is where <code>induction</code> earns its place, and it is the first proof in this workbook that uses the tactic at all. You are handed two derivations of the same command from the same state and asked to identify the results. You cannot induct on both.' },

    { t: 'steps', title: 'How “induct on one derivation, invert the other” goes',
      items: [
        { k: 'Induct on the first derivation',
          h: 'One goal per rule that <code>h₁</code> could have ended with, plus induction hypotheses for its sub-derivations.' },
        { k: 'Generalise the other final state',
          h: '<code>generalizing s₂</code> reverts <code>s₂</code> — and <code>h₂</code>, which mentions it — into the goal before the induction runs, and re-introduces them in each case. Each induction hypothesis then reads <code>∀ {s₂}, Exec c₁ s s₂ → s\' = s₂</code> instead of being pinned to the one <code>s₂</code> you started with. In the <code>seq</code> case you will need it at the <i>intermediate</i> state, which is not that one.' },
        { k: 'Invert the second derivation inside each case',
          h: 'Inside <code>skip</code>, <code>h₂ : Exec .skip s s₂</code>, so <code>cases h₂</code> leaves one branch. Inside <code>iteTrue</code>, <code>h₂ : Exec (.ite b c₁ c₂) s s₂</code>, so it leaves <i>two</i> — and the mismatched one is refuted by the guards.' },
        { k: 'Close each branch by one of four moves',
          h: [
            { t: 'ul', items: [
              '<b>Deterministic by construction</b> (<code>skip</code>, <code>assign</code>, <code>write</code>, <code>free</code>) — both sides are the same expression; <code>rfl</code>.',
              '<b>Value-carrying</b> (<code>load</code>) — two lookups of one cell; <code>rw</code>, then <code>cases</code> on <code>some v = some v\'</code>.',
              '<b>Compositional</b> (<code>seq</code>, <code>loopTrue</code>) — the first induction hypothesis identifies the intermediate states, the second finishes.',
              '<b>Guard clash</b> (the four <code>ite</code>/<code>loop</code> cross-cases) — <code>rw [hb] at hb\'</code> turns <code>hb\'</code> into <code>true = false</code>.'
            ] }
          ] }
      ] },

    { t: 'note', kind: 'info', title: 'Reading <code>induction … with | name args =&gt; …</code>',
      h: 'The names after <code>|</code> are constructor names of <code>Exec</code>, and the identifiers after each name bind that constructor’s arguments <i>in order</i>, with the induction hypotheses appended at the end. <code>| seq _ _ ih₁ ih₂ =&gt;</code> means: ignore the two premises, name their induction hypotheses. <code>| loopTrue hb _ _ ihb ihr =&gt;</code> means: keep the guard, drop the two sub-derivations, name their hypotheses. An argument you write <code>_</code> for is still in the context — it just gets an inaccessible name like <code>h₁✝</code>, which is why the goal states below are full of daggers.' },

    { t: 'ex',
      id: 'm5-2',
      name: 'exec_deterministic',
      hard: true,
      why: 'The language has no nondeterminism, so at most one final state exists. M13 needs this to derive partial correctness from total correctness. It is also the standard drill for “induction on one derivation, inversion on the other”, which is how every later chapter argues about executions.',
      setup: 'No lemmas from earlier chapters. Everything is <code>induction</code>, <code>cases</code>, <code>rw</code>, <code>rfl</code>, <code>absurd</code>, and two uses of <code>▸</code> — one in <code>seq</code>, one in <code>loopTrue</code>, and they are the same move.',
      goal: 'theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂',
      hints: [
        'Two derivations, one goal. Induct on one and take the other apart, case by case.',
        '<code>induction h₁ generalizing s₂</code>, then in each case <code>cases h₂</code>. The <code>generalizing</code> is essential: without it the induction hypothesis is stated only for the fixed <code>s₂</code> you started with, and the <code>seq</code> case fails.',
        'In the <code>seq</code> case you get <code>ih₁ : ∀ {s₂}, Exec c₁ s s₂ → s\' = s₂</code> and <code>ih₂</code> likewise, plus <code>h₁\'</code> and <code>h₂\'</code> from inverting <code>h₂</code>. So <code>ih₁ h₁\'</code> is an equation between the two intermediate states. Transport <code>h₂\'</code> along it with <code>▸</code> and feed the result to <code>ih₂</code>.',
        'The four cross-cases have <code>hb : b.eval s.store = true</code> and <code>hb\' : b.eval s.store = false</code> in scope. <code>rw [hb] at hb\'</code> makes <code>hb\' : true = false</code>; then <code>exact absurd hb\' (by simp)</code>.'
      ],
      hint: '<code>induction h₁ generalizing s₂</code>, then in each case <code>cases h₂</code>. The <code>generalizing</code> is essential: without it, the induction hypothesis is stated only for the fixed <code>s₂</code> you started with, and the <code>seq</code> case fails.',
      sol: 'theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by\n  induction h₁ generalizing s₂ with\n  | skip => cases h₂; rfl\n  | assign => cases h₂; rfl\n  | load hl => cases h₂ with | load hl\' => rw [hl] at hl\'; cases hl\'; rfl\n  | write hl => cases h₂ with | write hl\' => rfl\n  | free hl => cases h₂ with | free hl\' => rfl\n  | seq _ _ ih₁ ih₂ =>\n      cases h₂ with\n      | seq h₁\' h₂\' => exact ih₂ (ih₁ h₁\' ▸ h₂\')\n  | iteTrue hb _ ih =>\n      cases h₂ with\n      | iteTrue hb\' h\' => exact ih h\'\n      | iteFalse hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | iteFalse hb _ ih =>\n      cases h₂ with\n      | iteTrue hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | iteFalse hb\' h\' => exact ih h\'\n  | loopFalse hb =>\n      cases h₂ with\n      | loopFalse hb\' => rfl\n      | loopTrue hb\' _ _ => rw [hb] at hb\'; exact absurd hb\' (by simp)\n  | loopTrue hb _ _ ihb ihr =>\n      cases h₂ with\n      | loopFalse hb\' => rw [hb] at hb\'; exact absurd hb\' (by simp)\n      | loopTrue hb\' hbody\' hrest\' => exact ihr (ihb hbody\' ▸ hrest\')',
      expl: 'Three shapes of case. (i) <b>Deterministic-by-construction</b> (<code>skip</code>, <code>assign</code>, <code>write</code>, <code>free</code>): inversion pins down the result, <code>rfl</code> closes it. (ii) <b>Value-carrying</b> (<code>load</code>): both derivations read the same location, so <code>rw [hl] at hl\'</code> then <code>cases hl\'</code> forces the two loaded values equal. (iii) <b>Compositional</b> (<code>seq</code>, <code>loopTrue</code>): the first induction hypothesis identifies the intermediate states, <code>▸</code> transports along that equation, the second finishes. The four mismatch cases die on <code>rw [hb] at hb\'</code> — the guard cannot be both <code>true</code> and <code>false</code>.',
      walk: [
        { tac: 'induction h₁ generalizing s₂ with', h: 'Ten goals, one per constructor of <code>Exec</code>. Every induction hypothesis is now universally quantified over its own final state.' },
        { tac: '| skip => cases h₂; rfl', h: '<code>h₂ : Exec .skip s s₂</code>, so inversion forces <code>s₂ = s</code> and the goal collapses to <code>s = s</code>. <code>exec_skip_inv</code>, inlined.' },
        { tac: '| assign => cases h₂; rfl', h: 'Same shape. <code>assign</code> has no premises and a fully determined result, so after inversion both sides are the literal expression <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code>.' },
        { tac: '| load hl => cases h₂ with | load hl\' => rw [hl] at hl\'; cases hl\'; rfl', h: 'The only atomic case with content. <code>hl : s.heap l = some v</code> came from <code>h₁</code>, <code>hl\' : s.heap l = some v\'</code> from <code>h₂</code>. <code>rw [hl] at hl\'</code> replaces the left-hand side of <code>hl\'</code>, leaving <code>some v = some v\'</code>; <code>cases hl\'</code> uses injectivity of <code>some</code> to identify <code>v\'</code> with <code>v</code>.' },
        { tac: '| write hl => cases h₂ with | write hl\' => rfl', h: 'No <code>rw</code>, and that is the point: <code>write</code>’s premise binds <code>old</code>, which does not appear in the result. The two derivations may have found different old values; the resulting heaps are the same expression regardless. <code>hl\'</code> is never used — <code>cases h₂ with | write =&gt; rfl</code> compiles just as well, and the name is there for symmetry with <code>load</code>.' },
        { tac: '| free hl => cases h₂ with | free hl\' => rfl', h: 'Identical: <code>Heap.erase s.heap l</code> does not mention the value that was there.' },
        { tac: '| seq _ _ ih₁ ih₂ =>', h: 'The underscores drop the sub-derivations; only their induction hypotheses are needed.' },
        { tac: 'cases h₂ with', h: 'Only <code>Exec.seq</code> can conclude <code>Exec (c₁ ;; c₂) s s₂</code>, so one branch — but it introduces a <i>fresh</i> intermediate state, which is the crux.' },
        { tac: '| seq h₁\' h₂\' => exact ih₂ (ih₁ h₁\' ▸ h₂\')', h: 'Read it inside out. <code>ih₁ h₁\'</code> equates the two intermediate states. <code>e ▸ h</code> rewrites the type of <code>h</code> along the equation <code>e</code>, so <code>ih₁ h₁\' ▸ h₂\'</code> takes <code>h₂\'</code> and retypes it at the other intermediate state. Now <code>ih₂</code> applies.' },
        { tac: '| iteTrue hb _ ih =>', h: 'Keep the guard evaluation <code>hb</code>; you need it to refute the mismatched branch.' },
        { tac: 'cases h₂ with', h: 'Two constructors conclude <code>Exec (.ite b c₁ c₂) s s₂</code>, so two goals this time.' },
        { tac: '| iteTrue hb\' h\' => exact ih h\'', h: 'Both derivations took the same branch; the induction hypothesis for that branch applies directly. <code>hb\'</code> is unused.' },
        { tac: '| iteFalse hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)', h: 'The impossible branch. <code>rw [hb] at hb\'</code> rewrites the occurrence of <code>b.eval s.store</code> inside <code>hb\'</code>, producing <code>true = false</code>; <code>by simp</code> supplies its negation.' },
        { tac: '| iteFalse hb _ ih =>', h: 'The mirror image. Same two branches, roles swapped.' },
        { tac: 'cases h₂ with', h: 'Two goals again.' },
        { tac: '| iteTrue hb\' h\' => rw [hb] at hb\'; exact absurd hb\' (by simp)', h: 'Now the rewrite yields <code>false = true</code>. <code>rw [hb] at hb\'</code> is written the same way in both branches; the direction is decided by which hypothesis came from the induction.' },
        { tac: '| iteFalse hb\' h\' => exact ih h\'', h: 'Matching branches.' },
        { tac: '| loopFalse hb =>', h: 'The loop exited immediately, so the result is <code>s</code> itself and there is no induction hypothesis.' },
        { tac: 'cases h₂ with', h: 'Two loop constructors, two goals.' },
        { tac: '| loopFalse hb\' => rfl', h: 'Both exited; both final states are <code>s</code>.' },
        { tac: '| loopTrue hb\' _ _ => rw [hb] at hb\'; exact absurd hb\' (by simp)', h: 'One exited, one entered the body: guard clash. The two dropped arguments are the body and rest-of-loop derivations, neither needed.' },
        { tac: '| loopTrue hb _ _ ihb ihr =>', h: 'Five arguments: guard, body derivation, rest derivation, then <i>two</i> induction hypotheses. <code>ihr</code> exists precisely because <code>hrest</code> is a recursive premise even though its command is unchanged.' },
        { tac: 'cases h₂ with', h: 'Two goals.' },
        { tac: '| loopFalse hb\' => rw [hb] at hb\'; exact absurd hb\' (by simp)', h: 'Guard clash, fourth and last time.' },
        { tac: '| loopTrue hb\' hbody\' hrest\' => exact ihr (ihb hbody\' ▸ hrest\')', h: 'Structurally identical to <code>seq</code>: <code>ihb hbody\'</code> identifies the states after one iteration, <code>▸</code> transports the remaining derivation, <code>ihr</code> finishes. Sequencing and looping share a proof because <code>loopTrue</code> <i>is</i> a sequencing rule.' }
      ],
      deep: [
        { t: 'trace', title: 'The load case — where the two derivations have to be reconciled',
          start: 'case load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝ : Val\nhl : s✝.heap l✝ = some v✝\ns₂ : State\nh₂ : Exec (Cmd.load x✝ l✝) s✝ s₂\n⊢ { store := s✝.store.set x✝ v✝, heap := s✝.heap } = s₂',
          steps: [
            { tac: 'cases h₂ with | load hl\' =>',
              state: 'case load.load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝¹ : Val\nhl : s✝.heap l✝ = some v✝¹\nv✝ : Val\nhl\' : s✝.heap l✝ = some v✝\n⊢ { store := s✝.store.set x✝ v✝¹, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }',
              h: 'Two loaded values, distinguished only by a superscript dagger: <code>v✝¹</code> from <code>h₁</code>, <code>v✝</code> from <code>h₂</code>. The goal is an equation between two <code>State</code> literals differing in exactly one place.' },
            { tac: 'rw [hl] at hl\'',
              state: 'case load.load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝¹ : Val\nhl : s✝.heap l✝ = some v✝¹\nv✝ : Val\nhl\' : some v✝¹ = some v✝\n⊢ { store := s✝.store.set x✝ v✝¹, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }',
              h: 'The rewrite fires inside <code>hl\'</code>, replacing its left-hand side by <code>some v✝¹</code>. This is the moment the two derivations are forced to agree: they read the same cell of the same heap.' },
            { tac: 'cases hl\'',
              state: 'case load.load.refl\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝ : Val\nhl : s✝.heap l✝ = some v✝\n⊢ { store := s✝.store.set x✝ v✝, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }',
              h: '<code>hl\'</code> is an equation between two applications of the same constructor, so <code>cases</code> applies injectivity: one value variable disappears and the other is used everywhere. The case tag <code>refl</code> is <code>Eq</code>’s only constructor.' },
            { tac: 'rfl', state: 'No goals.', h: '' }
          ],
          done: 'No goals.' },

        { t: 'trace', title: 'The seq case — what <code>generalizing</code> bought you',
          start: 'case seq\nc : Cmd\ns s₁ s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s\'✝ s₂ → s\'\'✝ = s₂\ns₂ : State\nh₂ : Exec (c₁✝ ;; c₂✝) s✝ s₂\n⊢ s\'\'✝ = s₂',
          steps: [
            { tac: 'cases h₂ with | seq h₁\' h₂\' =>',
              state: 'case seq.seq\nc : Cmd\ns s₁ s✝ s\'✝¹ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝¹\nh₂✝ : Exec c₂✝ s\'✝¹ s\'\'✝\nih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝¹ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s\'✝¹ s₂ → s\'\'✝ = s₂\ns₂ s\'✝ : State\nh₁\' : Exec c₁✝ s✝ s\'✝\nh₂\' : Exec c₂✝ s\'✝ s₂\n⊢ s\'\'✝ = s₂',
              h: 'There are now <b>two</b> intermediate states: <code>s\'✝¹</code> from the derivation you inducted on, and the fresh <code>s\'✝</code> that inverting <code>h₂</code> produced. Nothing yet says they are equal. That is the obligation the next line discharges.' },
            { tac: 'exact ih₂ (ih₁ h₁\' ▸ h₂\')',
              state: 'No goals.',
              h: '<code>ih₁ h₁\'</code> is applied at the fresh state — legal only because <code>ih₁</code> is quantified — and proves <code>s\'✝¹ = s\'✝</code>. <code>▸</code> retypes <code>h₂\'</code> along it, which is what <code>ih₂</code> consumes.' }
          ],
          done: 'No goals.' },

        { t: 'cmp',
          left: { t: 'Without <code>generalizing s₂</code>', kind: 'bad',
                  h: [
                    { t: 'p', h: '<code>ih₁</code> is stated <b>only</b> for the one <code>s₂</code> you started with — but the state you must identify is the intermediate one that inverting <code>h₂</code> produced. There is no way to apply <code>ih₁</code>, and the case is unprovable as it stands.' },
                    { t: 'state', src: 'case seq\nc : Cmd\ns s₁ s₂ s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nih₁ : Exec c₁✝ s✝ s₂ → s\'✝ = s₂\nih₂ : Exec c₂✝ s\'✝ s₂ → s\'\'✝ = s₂\nh₂ : Exec (c₁✝ ;; c₂✝) s✝ s₂\n⊢ s\'\'✝ = s₂' }
                  ] },
          right: { t: 'With <code>generalizing s₂</code>', kind: 'good',
                   h: [
                     { t: 'p', h: 'The standard fix whenever an induction hypothesis has to be used at a different instance than the one sitting in the goal.' },
                     { t: 'state', src: 'ih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s\'✝ s₂ → s\'\'✝ = s₂' }
                   ] } },

        { t: 'trace', title: 'A guard clash, in full',
          start: 'case iteTrue.iteFalse\nc : Cmd\ns s₁ s✝ s\'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ : Exec c₁✝ s✝ s\'✝\nih : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝ = s₂\ns₂ : State\nhb\' : BExpr.eval s✝.store b✝ = false\nh\' : Exec c₂✝ s✝ s₂\n⊢ s\'✝ = s₂',
          steps: [
            { tac: 'rw [hb] at hb\'',
              state: 'case iteTrue.iteFalse\nc : Cmd\ns s₁ s✝ s\'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ : Exec c₁✝ s✝ s\'✝\nih : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s\'✝ = s₂\ns₂ : State\nhb\' : true = false\nh\' : Exec c₂✝ s✝ s₂\n⊢ s\'✝ = s₂',
              h: 'The context is now inconsistent and the goal is irrelevant. Note the printer once more: the source says <code>b.eval s.store</code>, the display says <code>BExpr.eval s✝.store b✝</code>.' },
            { tac: 'exact absurd hb\' (by simp)',
              state: 'No goals.',
              h: '<code>by simp</code> proves <code>¬ (true = false)</code>, which holds because <code>true</code> and <code>false</code> are distinct constructors of <code>Bool</code>. This is the line the <code>Bool</code>-not-<code>Prop</code> decision bought.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'What <code>▸</code> actually is', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Transport along an equality — at bottom the eliminator for <code>Eq</code>. Given <code>e : a = b</code> and a term <code>h</code> whose type mentions <code>b</code>, <code>e ▸ h</code> is a term of the type with <code>a</code> in place of <code>b</code>, or the other way round; Lean picks whichever direction makes elaboration succeed, which is why it can feel unpredictable.' },
            { t: 'p', h: 'When <code>▸</code> refuses, name the equation and do it by hand. This is the same step, easier to debug:' },
            { t: 'code', tag: 'sketch',
              cap: 'Not the corpus proof — shown only to say what <code>▸</code> is doing.',
              src: `-- the seq case, written out
| seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' =>
        have heq := ih₁ h₁'      -- s' = s'₂
        subst heq                -- replace s'₂ by s' everywhere
        exact ih₂ h₂'` }
          ] }
      ],
      pitfall: 'Forgetting <code>generalizing s₂</code> and then trying to repair the <code>seq</code> case. It cannot be repaired locally: the hypothesis you were handed is the wrong statement, and no amount of <code>rw</code> turns a fact about one particular <code>s₂</code> into a fact about the intermediate state. The other frequent error is writing <code>| load hl hl\' =&gt; …</code> as if the <code>induction</code> pattern and the inner <code>cases</code> shared one name list. They do not — the outer pattern names only <i>this</i> constructor’s arguments — and Lean answers <i>Too many variable names provided at alternative `load`: 2 provided, but 1 expected</i>. Hence the nested <code>cases h₂ with | load hl\' =&gt; …</code>.',
      variants: 'Delete <code>hb</code> from <code>Exec.iteTrue</code>, letting the <code>ite</code> rules fire regardless of the guard, and the language becomes nondeterministic: <code>if b then skip else free l</code> would have two derivations from one state. Determinism fails at exactly the four cross-cases, which is why those four lines are the ones that mention the guard. Similarly, if <code>Exec.load</code> did not carry <code>hl</code> but said “<code>x</code> gets some value”, the <code>load</code> case would break at <code>rw [hl] at hl\'</code> and the theorem would be false. Every line of this proof that is not <code>rfl</code> points at a place where determinism could have failed.'
    },

    /* ================================================================
       7 — the interpreter
       ================================================================ */

    { t: 'sec', s: 'The refused function, with a counter' },

    { t: 'p', h: 'The relation proves things and computes nothing. You cannot ask it what a program does; you can only offer an answer and ask whether it agrees. So bring back the function Lean refused, with the smallest change that makes it terminate: a <code>Nat</code> in front, decreasing at every recursive call. Nothing about the command needs to shrink any more, because something else does.' },

    { t: 'anat',
      cap: 'Six callouts on the clauses that decide how the two proofs below go.',
      src: `def run : Nat → Cmd → State → Option State
  | 0,     _,            _ => none
  | _ + 1, .skip,        s => some s
  | _ + 1, .assign x e,  s => some ⟨Store.set s.store x (e.eval s.store), s.heap⟩
  | _ + 1, .load x l,    s =>
      match s.heap l with
      | some v => some ⟨Store.set s.store x v, s.heap⟩
      | none   => none
  | _ + 1, .write l e,   s =>
      match s.heap l with
      | some _ => some ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩
      | none   => none
  | _ + 1, .free l,      s =>
      match s.heap l with
      | some _ => some ⟨s.store, Heap.erase s.heap l⟩
      | none   => none
  | n + 1, .seq c₁ c₂,   s =>
      match run n c₁ s with
      | some s' => run n c₂ s'
      | none    => none
  | n + 1, .ite b c₁ c₂, s =>
      match b.eval s.store with
      | true  => run n c₁ s
      | false => run n c₂ s
  | n + 1, .loop b c,   s =>
      match b.eval s.store with
      | true  =>
          match run n c s with
          | some s' => run n (.loop b c) s'
          | none    => none
      | false => some s`,
      parts: [
        { m: '| 0,     _,            _ => none', h: 'Out of fuel. This clause is why <code>run</code> is total, and it is the whole of the <code>zero</code> case of both proofs below: <code>h : run 0 c s = some s\'</code> is refuted by <code>simp [run]</code>, because <code>none = some s\'</code> is false.' },
        { m: '| _ + 1, .skip,        s => some s', h: 'The fuel is matched but not named — atomic commands never recurse. It is still matched as <code>_ + 1</code> rather than a bare <code>n</code>, so that this clause and the <code>0</code> clause split <code>Nat</code> with no overlap. The consequence for the proofs: at fuel <code>n + 1</code> and at fuel <code>n + 2</code> the atomic clauses unfold to <i>the same term</i>, which is why every atomic case of <code>run_mono</code> is one word long.' },
        { m: 'match s.heap l with', h: 'The fault check, mirroring the premise of <code>Exec.load</code>. Failure is a <i>value</i> here, where in the relation it was the absence of a rule. The soundness proof is precisely the translation between the two encodings.' },
        { m: '| n + 1, .seq c₁ c₂,   s =>', h: 'Here the fuel <i>is</i> named, because it is passed on — and both halves get <code>n</code>, not <code>n</code> split between them. Fuel bounds the <b>depth</b> of the recursion, not its total size, which is why the completeness proof can take <code>max n₁ n₂ + 1</code> instead of a sum.' },
        { m: 'match b.eval s.store with', h: 'The guard is a <code>Bool</code>, so this is an ordinary two-way match and not an <code>if</code>. That is what makes the branching cases of <code>run_sound</code> one line each: rewrite the scrutinee to the literal <code>true</code> and the whole <code>match</code> reduces to its first branch <i>definitionally</i>, with no instance anywhere in the chain.' },
        { m: 'run n (.loop b c) s\'', h: 'The same command with one less fuel — the call <code>runBad</code> could not make. Note the asymmetry with <code>Exec.loopTrue</code>: there the recursive premise is at the same command and that is fine, because the derivation tree shrinks. Here nothing shrinks but the number you brought with you.' }
      ] },

    { t: 'p', h: 'The price is that <code>run</code> is not the semantics. <code>run n c s = none</code> means the program faulted, or would diverge, or <code>n</code> was too small, and the three are indistinguishable — the same conflation that disqualified a function from being <i>the</i> semantics, harmless now only because nothing is proved about <code>run</code>. The interpreter establishes nothing negative, and soundness is therefore stated with <code>some s\'</code> as its hypothesis.' },

    { t: 'p', h: 'Both proofs unfold <code>run</code> through the <b>equation lemmas</b> Lean generated from the clauses, one per clause. <code>simp only [run]</code> fires those and nothing else; plain <code>simp [run]</code> adds the default simp set on top, which is what strips a <code>some</code> off both sides of an equation or turns <code>none = some s\'</code> into a closed goal. Both spellings appear below, and in one place the choice is forced.' },

    { t: 'ex',
      id: 'm5-3',
      name: 'run_sound',
      hard: true,
      why: 'Everything the interpreter accepts is a genuine execution: the interpreter never lies. Once this is proved you can <code>#eval</code> a program and know that the state it reports is reachable — so a mistake in <code>Exec</code> shows up as a wrong number on your screen instead of as an afternoon spent proving something false.',
      setup: 'Induct on the fuel, not on the command. The command is destructed inside each case, so the induction hypothesis is available at fuel <code>n</code> for <i>every</i> command — which is what <code>seq</code> and <code>loop</code> need.',
      goal: 'theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s\' : State),\n    run n c s = some s\' → Exec c s s\'',
      hints: [
        'The statement is a <code>∀</code> over four things. Introduce only the fuel, then induct: <code>intro n; induction n with …</code>. Leaving <code>c</code>, <code>s</code>, <code>s\'</code> under the binder is what makes the induction hypothesis usable at other commands and states.',
        '<code>induction n</code>, then <code>cases c</code>. The <code>zero</code> case is one tactic: <code>run 0 c s</code> is <code>none</code>, so the hypothesis is absurd.',
        'For the branching commands use <code>cases hb : b.eval s.store</code> and then <code>rw [hb] at h</code> — the <code>cases … :</code> form records the equation and rewrites the goal, but leaves hypotheses alone, so you must transport it yourself.',
        'After <code>rw [hb] at h</code> the hypothesis <i>displays</i> as <code>(match true with | true =&gt; run n c₁ s | false =&gt; …) = some s\'</code>. Do not try to simplify it. That term is definitionally <code>run n c₁ s = some s\'</code>, so <code>exact .iteTrue hb (ih c₁ s s\' h)</code> typechecks as written.'
      ],
      hint: '<code>induction n</code>, then <code>cases c</code>. For the branching commands use <code>cases hb : b.eval s.store</code> and then <code>rw [hb] at h</code> — the <code>cases … :</code> form records the equation in the goal but not in <code>h</code>, so you must transport it yourself.',
      sol: 'theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\' := by\n  intro n\n  induction n with\n  | zero => intro c s s\' h; simp [run] at h\n  | succ n ih =>\n    intro c s s\' h\n    cases c with\n    | skip => simp [run] at h; rw [← h]; exact .skip\n    | assign x e => simp [run] at h; rw [← h]; exact .assign\n    | load x l =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl\n    | write l e =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl\n    | free l =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl\n    | seq c₁ c₂ =>\n        simp only [run] at h\n        cases hr : run n c₁ s with\n        | none    => rw [hr] at h; simp at h\n        | some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s\' h)\n    | ite b c₁ c₂ =>\n        simp only [run] at h\n        cases hb : b.eval s.store with\n        | true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s\' h)\n        | false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s\' h)\n    | loop b c =>\n        simp only [run] at h\n        cases hb : b.eval s.store with\n        | false =>\n            rw [hb] at h\n            have hs : s = s\' := Option.some.inj h\n            subst hs\n            exact .loopFalse hb\n        | true  =>\n            rw [hb] at h\n            cases hr : run n c s with\n            | none    => rw [hr] at h; simp at h\n            | some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s\' h)',
      expl: 'The one subtlety is definitional reduction. After <code>rw [hb] at h</code> the hypothesis reads <code>(match true with | true =&gt; run n c₁ s | false =&gt; …) = some s\'</code>, which <i>is</i> <code>run n c₁ s = some s\'</code>. <code>exact</code> checks up to definitional equality, so it goes through with no further simplification. Writing <code>run</code>’s branches as a <code>match</code> on <code>Bool</code> rather than an <code>if</code> is what makes that reliable: the iota reduction fires and there is no instance in the chain that could go opaque.',
      walk: [
        { tac: 'intro n', h: 'Introduce only the fuel. The goal becomes <code>∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'</code>, so the induction hypothesis will be that whole statement at <code>n</code> — quantified over command and states, which is what the compound cases need.' },
        { tac: 'induction n with', h: 'Two goals, <code>zero</code> and <code>succ</code>. Induction on a <code>Nat</code>: the recursor is <code>Nat.rec</code>.' },
        { tac: '| zero => intro c s s\' h; simp [run] at h', h: 'With no fuel <code>run 0 c s</code> reduces to <code>none</code>, so <code>h : none = some s\'</code>. <code>simp [run] at h</code> unfolds, then the default set sees that two distinct <code>Option</code> constructors cannot be equal; a hypothesis reduced to <code>False</code> closes whatever goal is open.' },
        { tac: '| succ n ih =>', h: '<code>ih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'</code> — at fuel <code>n</code>, for every command. You will apply it to sub-commands and, in the loop case, to the same command.' },
        { tac: 'intro c s s\' h', h: 'Now the rest. <code>h : run (n + 1) c s = some s\'</code>.' },
        { tac: 'cases c with', h: 'Eight goals, one per constructor of <code>Cmd</code>. This is where the fuel-versus-command choice pays off: <code>c</code> was introduced <i>after</i> the induction, so <code>ih</code> is not tied to it.' },
        { tac: '| skip => simp [run] at h; rw [← h]; exact .skip', h: '<code>simp [run] at h</code> turns <code>h</code> into <code>s = s\'</code>: it unfolds to <code>some s = some s\'</code> and then strips the constructor. <code>rw [← h]</code> rewrites <code>s\'</code> to <code>s</code> in the goal, giving <code>Exec Cmd.skip s s</code>, which is what <code>Exec.skip</code> concludes.' },
        { tac: '| assign x e => simp [run] at h; rw [← h]; exact .assign', h: 'Same three moves. Here <code>h</code> equates <code>s\'</code> with the literal state <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code>, and <code>Exec.assign</code> concludes at precisely that state.' },
        { tac: '| load x l =>', h: 'The first case with a fault check.' },
        { tac: 'simp only [run] at h', h: 'Unfold <code>run</code> and nothing else. <code>h</code> now displays as an unreduced <code>match s.heap l with …</code>: no rewrite reduces a match whose scrutinee is an opaque application, and plain <code>simp [run] at h</code> leaves it in exactly the same shape. So the choice here is hygiene, not necessity — it names the single equation you want to fire, which keeps the hypothesis you are about to <code>rw</code> into predictable.' },
        { tac: 'cases hl : s.heap l with', h: 'Split on whether the cell exists, recording the equation as <code>hl</code>.' },
        { tac: '| none   => rw [hl] at h; simp at h', h: 'Transport the equation into <code>h</code> by hand — the step the <code>cases … :</code> form does not do for you. Then <code>h</code> is <code>none = some s\'</code> and <code>simp at h</code> closes the goal.' },
        { tac: '| some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl', h: 'After the rewrite the match reduces and <code>simp at h</code> strips the <code>some</code>, leaving <code>h : ⟨Store.set s.store x v, s.heap⟩ = s\'</code>. <code>rw [← h]</code> puts that literal state into the goal, and <code>hl</code> is exactly the premise <code>Exec.load</code> demands.' },
        { tac: '| write l e =>\n    simp only [run] at h\n    cases hl : s.heap l with\n    | none   => rw [hl] at h; simp at h\n    | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl', h: 'Character for character the <code>load</code> argument with <code>.write</code> in place of <code>.load</code>. The bound value <code>v</code> only instantiates <code>hl</code>, which is what <code>Exec.write</code>’s <code>old</code> premise wants.' },
        { tac: '| free l =>\n    simp only [run] at h\n    cases hl : s.heap l with\n    | none   => rw [hl] at h; simp at h\n    | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl', h: 'And again. Three commands, one argument — the sign that the fault check belongs in one place. In M7 all three get the same small-footprint precondition.' },
        { tac: '| seq c₁ c₂ =>', h: 'The first compound case.' },
        { tac: 'simp only [run] at h', h: '<code>h</code> becomes <code>(match run n c₁ s with | some s\' =&gt; run n c₂ s\' | none =&gt; none) = some s\'</code>. The scrutinee is a recursive call, not a heap lookup.' },
        { tac: 'cases hr : run n c₁ s with', h: 'Split on whether the first half succeeded, recording <code>hr</code> — which is exactly the shape <code>ih</code> consumes.' },
        { tac: '| none    => rw [hr] at h; simp at h', h: 'If the first half returned <code>none</code> so did the whole thing, contradicting <code>h</code>.' },
        { tac: '| some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s\' h)', h: 'After the rewrite <code>h</code> is definitionally <code>run n c₂ s₁ = some s\'</code>, so <code>ih c₂ s₁ s\' h</code> typechecks with no further tactic; <code>ih c₁ s s₁ hr</code> handles the first half. <code>Exec.seq</code> glues them, choosing <code>s₁</code> as the intermediate state.' },
        { tac: '| ite b c₁ c₂ =>', h: 'The branching case.' },
        { tac: 'simp only [run] at h', h: '<code>h : (match BExpr.eval s.store b with | true =&gt; run n c₁ s | false =&gt; run n c₂ s) = some s\'</code>.' },
        { tac: 'cases hb : b.eval s.store with', h: 'Split on the guard. Two goals, tagged <code>true</code> and <code>false</code> — <code>Bool</code>’s constructors, not <code>pos</code>/<code>neg</code>, because you are casing on a <code>Bool</code> and not on a decidable proposition.' },
        { tac: '| true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s\' h)', h: 'The whole exercise in one line. <code>rw [hb] at h</code> makes the scrutinee the literal <code>true</code>; the match then reduces by iota, so <code>h</code> <i>is</i> <code>run n c₁ s = some s\'</code> even though it does not print that way. <code>hb</code> doubles as the premise of <code>Exec.iteTrue</code>.' },
        { tac: '| false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s\' h)', h: 'Mirror image.' },
        { tac: '| loop b c =>', h: 'The last and only genuinely new case.' },
        { tac: 'simp only [run] at h', h: 'A nested match: guard outside, result of the body inside.' },
        { tac: 'cases hb : b.eval s.store with', h: 'Split on the guard, taking <code>false</code> first because it is the base case of the loop.' },
        { tac: '| false =>\n    rw [hb] at h', h: 'The outer match reduces to <code>some s</code>, so <code>h</code> is definitionally <code>some s = some s\'</code>.' },
        { tac: 'have hs : s = s\' := Option.some.inj h', h: 'Applied to <code>h</code> directly — again no simplification, because <code>h</code>’s type reduces to an equation between two <code>some</code>s.' },
        { tac: 'subst hs', h: 'Replace <code>s\'</code> by <code>s</code> throughout. The goal becomes <code>Exec (Cmd.loop b c) s s</code>.' },
        { tac: 'exact .loopFalse hb', h: 'Exactly the shape of <code>Exec.loopFalse</code>, whose premise is the false guard.' },
        { tac: '| true  =>\n    rw [hb] at h', h: 'The outer match reduces into the inner one, so <code>h</code> is now about the body.' },
        { tac: 'cases hr : run n c s with', h: 'Split on whether the body succeeded, recording <code>hr</code>.' },
        { tac: '| none    => rw [hr] at h; simp at h', h: 'Body failed, so the loop returned <code>none</code>; contradiction.' },
        { tac: '| some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s\' h)', h: '<code>ih c s s₁ hr</code> is the body’s execution; <code>ih _ s₁ s\' h</code> is the rest of the loop, the <code>_</code> being <code>.loop b c</code> inferred from <code>h</code>. This is the one place <code>ih</code> is applied at the <i>same</i> command, and it is legal because the fuel went down.' }
      ],
      deep: [
        { t: 'trace', title: 'The skeleton: what induction on fuel gives you',
          start: '⊢ ∀ (n : Nat) (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'',
          steps: [
            { tac: 'intro n',
              state: 'n : Nat\n⊢ ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'',
              h: 'Only the fuel. Everything else stays under the binder, which is what makes the induction hypothesis general.' },
            { tac: 'induction n with | zero => intro c s s\' h',
              state: 'case zero\nc : Cmd\ns s\' : State\nh : run 0 c s = some s\'\n⊢ Exec c s s\'',
              h: '<code>run 0 c s</code> is <code>none</code> for any <code>c</code> and <code>s</code>, so <code>h</code> is absurd.' },
            { tac: '| succ n ih => intro c s s\' h',
              state: 'case succ\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\nc : Cmd\ns s\' : State\nh : run (n + 1) c s = some s\'\n⊢ Exec c s s\'',
              h: 'There is the hypothesis you wanted: quantified over command and both states. <code>cases c</code> now splits the goal eight ways with <code>ih</code> untouched in every branch.' }
          ],
          done: 'eight goals, one per Cmd constructor' },

        { t: 'trace', title: 'The load case — simp only, then transport the equation by hand',
          start: 'case succ.load\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nx : Var\nl : Loc\nh : run (n + 1) (Cmd.load x l) s = some s\'\n⊢ Exec (Cmd.load x l) s s\'',
          steps: [
            { tac: 'simp only [run] at h',
              state: 'case succ.load\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nx : Var\nl : Loc\nh :\n  (match s.heap l with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s\'\n⊢ Exec (Cmd.load x l) s s\'',
              h: 'The equation lemma for the <code>load</code> clause fired. The fuel has disappeared from <code>h</code> entirely — atomic commands do not use it — and what remains is a stuck <code>match</code>.' },
            { tac: 'cases hl : s.heap l with | some v => (before rw)',
              state: 'case succ.load.some\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nx : Var\nl : Loc\nh :\n  (match s.heap l with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s\'\nv : Val\nhl : s.heap l = some v\n⊢ Exec (Cmd.load x l) s s\'',
              h: '<b>Look at <code>h</code>.</b> It still says <code>match s.heap l</code>. The <code>cases hl :</code> form substituted into the goal and gave you the equation, and left the hypotheses alone. That is why the next tactic exists.' },
            { tac: 'rw [hl] at h',
              state: 'case succ.load.some\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nx : Var\nl : Loc\nv : Val\nh :\n  (match some v with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s\'\nhl : s.heap l = some v\n⊢ Exec (Cmd.load x l) s s\'',
              h: 'The scrutinee is a literal constructor application, so the match is definitionally reduced — though the printer still shows it unreduced.' },
            { tac: 'simp at h',
              state: 'case succ.load.some\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nx : Var\nl : Loc\nv : Val\nhl : s.heap l = some v\nh : { store := s.store.set x v, heap := s.heap } = s\'\n⊢ Exec (Cmd.load x l) s s\'',
              h: '<code>simp</code> performs the iota reduction and strips the outer <code>some</code> from both sides. It also moved <code>h</code> to the end of the context — cosmetic, a consequence of rebuilding the hypothesis, but it surprises people reading diffs.' },
            { tac: 'rw [← h]; exact .load hl', state: 'No goals.', h: '<code>rw [← h]</code> replaces <code>s\'</code> in the goal by the explicit state, which is <code>Exec.load</code>’s conclusion; <code>hl</code> is its premise.' }
          ],
          done: 'No goals.' },

        { t: 'trace', title: 'The ite case — the definitional-equality trick, isolated',
          start: 'case succ.ite\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nb : BExpr\nc₁ c₂ : Cmd\nh :\n  (match BExpr.eval s.store b with\n    | true => run n c₁ s\n    | false => run n c₂ s) =\n    some s\'\n⊢ Exec (Cmd.ite b c₁ c₂) s s\'',
          steps: [
            { tac: 'cases hb : b.eval s.store with | true => rw [hb] at h',
              state: 'case succ.ite.true\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nb : BExpr\nc₁ c₂ : Cmd\nh :\n  (match true with\n    | true => run n c₁ s\n    | false => run n c₂ s) =\n    some s\'\nhb : BExpr.eval s.store b = true\n⊢ Exec (Cmd.ite b c₁ c₂) s s\'',
              h: 'This is the state worth memorising. <code>h</code> <i>prints</i> as a match on the literal <code>true</code>. It <i>is</i> <code>run n c₁ s = some s\'</code>, and Lean’s kernel does not care which of the two you show it.' },
            { tac: 'exact .iteTrue hb (ih c₁ s s\' h)',
              state: 'No goals.',
              h: '<code>ih c₁ s s\' h</code> demands an argument of type <code>run n c₁ s = some s\'</code>. <code>h</code>’s type reduces to that, and <code>exact</code> checks up to definitional equality. No <code>simp</code>, no <code>show</code>, no <code>change</code>.' }
          ],
          done: 'No goals.' },

        { t: 'cmp',
          left: { t: 'If <code>run</code> used <code>if</code>',
                  h: [
                    { t: 'p', h: 'Write the interpreter as <code>if b.eval s.store = true then run n c₁ s else run n c₂ s</code> and this case goes through <b>unchanged</b> — worth knowing, because the <code>if</code> spelling usually gets described as a disaster. Below is the real hypothesis after <code>rw [hb] at h</code>, from a copy of the interpreter named <code>runIf</code>:' },
                    { t: 'state', src: 'h : (if true = true then runIf n c₁ s else runIf n c₂ s) = some s\'\nhb : BExpr.eval s.store b = true\n⊢ Exec (Cmd.ite b c₁ c₂) s s\'' },
                    { t: 'p', h: 'and <code>exact .iteTrue hb (ih c₁ s s\' h)</code> still typechecks: <code>Bool</code>’s decidable-equality instance computes on two literal constructors, so <code>if true = true then A else B</code> reduces to <code>A</code> by itself.' }
                  ] },
          right: { t: 'As written, with <code>match</code>', kind: 'good',
                   h: 'The difference is not whether it works but what it depends on. Reduction through <code>if</code> is only as good as the instance: give the guard a classical one and nothing reduces. <code>example (a b : Nat) : pick True a b = a := rfl</code> with <code>pick φ a b := if φ then a else b</code> and <code>open Classical</code> fails — <i>Type mismatch: <code>rfl</code> has type <code>?m = ?m</code> but is expected to have type <code>(if True then a else b) = a</code></i> — and you are back to <code>if_pos</code>. The <code>match</code> spelling has nothing in it that can go opaque.' } },

        { t: 'detail', title: 'Where <code>simp [run]</code> and <code>simp only [run]</code> actually differ', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'In <code>skip</code> and <code>assign</code> the proof uses <code>simp [run] at h</code> and <i>wants</i> the extra work. <code>simp only [run] at h</code> unfolds and stops, leaving' },
            { t: 'state', src: 'case succ.skip\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → Exec c s s\'\ns s\' : State\nh : some s = some s\'\n⊢ Exec Cmd.skip s s\'' },
            { t: 'p', h: 'and the next line, <code>rw [← h]</code>, then fails with <i>Tactic `rewrite` failed: Did not find an occurrence of the pattern <code>some s\'</code> in the target expression <code>Exec Cmd.skip s s\'</code></i>. Plain <code>simp</code> follows the unfolding with the default set, strips the <code>some</code> from both sides, and hands you <code>h : s = s\'</code> — an equation between states, which is what the goal contains.' },
            { t: 'p', h: 'In the cases with a match the two spellings agree: <code>simp</code> cannot get inside a match on an opaque scrutinee any more than <code>simp only</code> can, and substituting <code>simp [run] at h</code> for every <code>simp only [run] at h</code> in this proof still compiles. So the rule is not “<code>simp only</code> or it breaks”. It is: <code>simp only [run]</code> when the next tactic depends on the exact shape of the hypothesis, plain <code>simp</code> when you are closing a goal or extracting an equation and do not care how.' }
          ] }
      ],
      pitfall: 'Writing <code>cases hb : b.eval s.store</code> and assuming <code>h</code> has been updated. It has not. Every branch begins with <code>rw [hb] at h</code> or <code>rw [hr] at h</code> for exactly that reason; omit it and <code>exact .iteTrue hb (ih c₁ s s\' h)</code> reports <i>Application type mismatch: the argument <code>h</code> has type <code>(match BExpr.eval s.store b with | true =&gt; run n c₁ s | false =&gt; run n c₂ s) = some s\'</code> but is expected to have type <code>run n c₁ s = some s\'</code></i>, which is the two encodings side by side and tells you which rewrite is missing. The other pitfall is at the very top: <code>intro n c s s\' h</code> and only then <code>induction n</code>. It looks equivalent and is not — you get <code>ih : run n c s = some s\' → Exec c s s\'</code>, pinned to the one command and the one pair of states you happen to be holding, and every compound case then needs it at a <i>sub</i>-command. <code>intro n</code> alone is the whole trick.',
      variants: 'Drop the fault check from <code>run</code>’s <code>load</code> clause — return <code>some ⟨Store.set s.store x 0, s.heap⟩</code> when the cell is missing — and soundness becomes <b>false</b>: the interpreter reports a final state for a stuck program, and no derivation justifies it. The failure appears at exactly one place, the <code>none</code> branch of <code>cases hl</code>, which currently closes by contradiction and would then have to produce <code>Exec.load</code> with no premise to give it. Conversely, weakening the statement to <code>run n c s = some s\' → ∃ s\'\', Exec c s s\'\'</code> is provable and useless: it says the program can run, not that the interpreter computed the right answer.'
    },

    /* ================================================================
       8 — completeness
       ================================================================ */

    { t: 'sec', s: 'One number for two premises' },

    { t: 'p', h: 'The other direction is harder, and the difficulty is arithmetic rather than semantic. A derivation for <code>c₁ ;; c₂</code> is built from two sub-derivations; each yields its own fuel bound; <code>run</code> takes one number.' },

    { t: 'steps', title: 'The completeness argument, in three moves',
      items: [
        { k: 'Monotonicity in the fuel', h: '<code>run_mono</code>: one more unit never turns a success into a failure. Induction on the fuel, mirroring <code>run_sound</code> case for case.' },
        { k: 'Monotonicity, transitively', h: '<code>run_le</code>: if <code>n ≤ m</code> then <code>n</code> units sufficing implies <code>m</code> units suffice. Induction on the <i>proof</i> of <code>n ≤ m</code> — <code>Nat.le</code> is itself an inductive relation, with constructors <code>refl</code> and <code>step</code>, and the <code>step</code> case is one application of <code>run_mono</code>.' },
        { k: 'Take a maximum', h: '<code>run_complete</code>: induct on the <code>Exec</code> derivation. Where there are two bounds, use <code>max n₁ n₂ + 1</code> and lift both with <code>run_le</code>. The <code>+ 1</code> pays for the current step.' }
      ] },

    { t: 'ex',
      id: 'm5-4',
      name: 'run_mono, run_le, run_complete',
      hard: true,
      why: 'Completeness needs monotonicity first: to run a sequence you must give both halves enough fuel, so you take the max and need to know extra fuel is harmless. Together with <code>run_sound</code> this says the relation and the interpreter define the same partial function, which is what licenses using <code>#eval</code> as a check on your semantics.',
      setup: 'Three theorems, three different things to induct on: the fuel, the proof of <code>≤</code>, and the <code>Exec</code> derivation. From the standard library you need only <code>Nat.le_max_left</code> and <code>Nat.le_max_right</code>.',
      goal: 'theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s\' : State),\n    run n c s = some s\' → run (n + 1) c s = some s\'\n\ntheorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s\' : State}\n    (h : run n c s = some s\') : run m c s = some s\'\n\ntheorem run_complete {c : Cmd} {s s\' : State} (h : Exec c s s\') :\n    ∃ n, run n c s = some s\'',
      hints: [
        '<code>run_mono</code> is <code>run_sound</code> with a different conclusion. Same skeleton: <code>intro n</code>, induct on the fuel, then <code>cases c</code>. The atomic cases are now one tactic each, because the result does not depend on the fuel at all.',
        'For those atomic cases, <code>simpa [run] using h</code>: both sides unfold to the same thing.',
        '<code>run_le</code> by induction on <code>≤</code>. <code>n ≤ m</code> is <code>Nat.le n m</code>, an inductive relation with <code>refl : Nat.le n n</code> and <code>step : Nat.le n m → Nat.le n (m+1)</code>. So <code>induction hle with | refl =&gt; … | step _ ih =&gt; …</code>, and the <code>step</code> case is a single application of <code>run_mono</code>.',
        '<code>run_complete</code> by induction on the <code>Exec</code> derivation. Atomic cases: <code>⟨1, …⟩</code>. Two-premise cases: <code>obtain</code> both bounds, then <code>refine ⟨max n₁ n₂ + 1, ?_⟩</code>, <code>simp only [run]</code>, and use <code>run_le (Nat.le_max_left n₁ n₂) h₁</code> for the first bound and <code>Nat.le_max_right</code> for the second.'
      ],
      hint: '<code>run_mono</code> by induction on fuel, mirroring <code>run_sound</code>. <code>run_le</code> by induction on <code>≤</code>. <code>run_complete</code> by induction on the <code>Exec</code> derivation, taking <code>max n₁ n₂ + 1</code> in the two-premise cases.',
      sol: 'theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s\' : State),\n    run n c s = some s\' → run (n + 1) c s = some s\' := by\n  intro n\n  induction n with\n  | zero => intro c s s\' h; simp [run] at h\n  | succ n ih =>\n    intro c s s\' h\n    cases c with\n    | skip => simpa [run] using h\n    | assign x e => simpa [run] using h\n    | load x l => simpa [run] using h\n    | write l e => simpa [run] using h\n    | free l => simpa [run] using h\n    | seq c₁ c₂ =>\n        simp only [run] at h ⊢\n        cases hr : run n c₁ s with\n        | none    => rw [hr] at h; simp at h\n        | some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s\' h\n    | ite b c₁ c₂ =>\n        simp only [run] at h ⊢\n        cases hb : b.eval s.store with\n        | true  => rw [hb] at h; exact ih c₁ s s\' h\n        | false => rw [hb] at h; exact ih c₂ s s\' h\n    | loop b c =>\n        simp only [run] at h ⊢\n        cases hb : b.eval s.store with\n        | false => rw [hb] at h; exact h\n        | true  =>\n            rw [hb] at h\n            cases hr : run n c s with\n            | none    => rw [hr] at h; simp at h\n            | some s₁ =>\n                rw [hr] at h\n                have : run (n + 1) c s = some s₁ := ih c s s₁ hr\n                rw [this]\n                exact ih _ s₁ s\' h\n\ntheorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s\' : State}\n    (h : run n c s = some s\') : run m c s = some s\' := by\n  induction hle with\n  | refl => exact h\n  | step _ ih => exact run_mono _ _ _ _ ih\n\ntheorem run_complete {c : Cmd} {s s\' : State} (h : Exec c s s\') :\n    ∃ n, run n c s = some s\' := by\n  induction h with\n  | skip => exact ⟨1, rfl⟩\n  | assign => exact ⟨1, rfl⟩\n  | load hl => exact ⟨1, by simp [run, hl]⟩\n  | write hl => exact ⟨1, by simp [run, hl]⟩\n  | free hl => exact ⟨1, by simp [run, hl]⟩\n  | seq _ _ ih₁ ih₂ =>\n      obtain ⟨n₁, h₁⟩ := ih₁\n      obtain ⟨n₂, h₂⟩ := ih₂\n      refine ⟨max n₁ n₂ + 1, ?_⟩\n      simp only [run]\n      rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n      exact run_le (Nat.le_max_right n₁ n₂) h₂\n  | iteTrue hb _ ih =>\n      obtain ⟨n, hn⟩ := ih\n      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩\n  | iteFalse hb _ ih =>\n      obtain ⟨n, hn⟩ := ih\n      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩\n  | loopFalse hb => exact ⟨1, by simp only [run, hb]⟩\n  | loopTrue hb _ _ ihb ihr =>\n      obtain ⟨n₁, h₁⟩ := ihb\n      obtain ⟨n₂, h₂⟩ := ihr\n      refine ⟨max n₁ n₂ + 1, ?_⟩\n      simp only [run, hb]\n      rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n      exact run_le (Nat.le_max_right n₁ n₂) h₂',
      expl: '<code>run_le</code> is the standard trick: induct on the proof of <code>n ≤ m</code>, whose <code>step</code> case is one application of <code>run_mono</code>. In <code>run_complete</code> the <code>seq</code> and <code>loopTrue</code> cases each produce two bounds, and <code>max</code> plus <code>run_le</code> reconciles them. With <code>run_sound</code>, the relation and the interpreter now define the same partial function.',
      walk: [
        { tac: 'intro n\ninduction n with\n| zero => intro c s s\' h; simp [run] at h\n| succ n ih =>\n  intro c s s\' h\n  cases c with', h: 'Identical opening to <code>run_sound</code>, down to the tactic. Only the conclusion differs: <code>ih : ∀ c s s\', run n c s = some s\' → run (n + 1) c s = some s\'</code>.' },
        { tac: '| skip => simpa [run] using h', h: 'Lean starts you at <code>h : run (n + 1) Cmd.skip s = some s\'</code> with goal <code>run (n + 1 + 1) Cmd.skip s = some s\'</code>. Both sides simplify to <code>s = s\'</code>, the same proposition, so the trailing <code>exact</code> closes it.' },
        { tac: '| assign x e => simpa [run] using h\n| load x l => simpa [run] using h\n| write l e => simpa [run] using h\n| free l => simpa [run] using h', h: 'All four for one reason: the atomic clauses match the fuel as <code>_ + 1</code> and never mention it again, so at fuel <code>n+1</code> and at fuel <code>n+2</code> they unfold to <i>literally the same term</i>. There is nothing to prove beyond unfolding.' },
        { tac: '| seq c₁ c₂ =>', h: 'The first case where extra fuel has to be pushed inwards.' },
        { tac: 'simp only [run] at h ⊢', h: 'Note the <code>⊢</code> in the location list: unfold in the hypothesis <i>and</i> in the goal. <code>h</code> is now a match on <code>run n c₁ s</code>, the goal the same match one fuel level up.' },
        { tac: 'cases hr : run n c₁ s with', h: 'Split on the first half at the <i>lower</i> fuel — the one <code>h</code> knows about.' },
        { tac: '| none    => rw [hr] at h; simp at h', h: 'Contradiction, as before.' },
        { tac: '| some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s\' h', h: 'Three moves in one line. <code>rw [hr] at h</code> reduces <code>h</code> to <code>run n c₂ s₁ = some s\'</code>. <code>ih c₁ s s₁ hr : run (n+1) c₁ s = some s₁</code>, and rewriting the <i>goal</i> with it turns the goal’s scrutinee into <code>some s₁</code>, so the goal reduces to <code>run (n+1) c₂ s₁ = some s\'</code>. That is <code>ih c₂ s₁ s\' h</code>.' },
        { tac: '| ite b c₁ c₂ =>\n    simp only [run] at h ⊢', h: 'Same opening. The guard does not depend on fuel, so the goal’s guard is the same expression as the hypothesis’s.' },
        { tac: 'cases hb : b.eval s.store with', h: 'Because the guard occurs in the goal, <code>cases hb :</code> substitutes <code>true</code> or <code>false</code> there automatically; only <code>h</code> needs the manual rewrite.' },
        { tac: '| true  => rw [hb] at h; exact ih c₁ s s\' h', h: 'Both sides collapse by iota to statements about <code>c₁</code>, and <code>ih</code> is the bridge between them.' },
        { tac: '| false => rw [hb] at h; exact ih c₂ s s\' h', h: 'Mirror image.' },
        { tac: '| loop b c =>\n    simp only [run] at h ⊢', h: 'Here <code>simp only [run]</code> unfolds the goal <i>twice</i>: once for the outer <code>run (n+2) (.loop b c) s</code> and again for the recursive <code>run (n+1) (.loop b c) s\'</code> inside it. The printed goal is correspondingly large; ignore the depth and look at the outermost scrutinee.' },
        { tac: 'cases hb : b.eval s.store with', h: 'Split the guard.' },
        { tac: '| false => rw [hb] at h; exact h', h: 'Guard false: both <code>h</code> and the goal reduce to <code>some s = some s\'</code>, literally the same proposition.' },
        { tac: '| true  =>\n    rw [hb] at h', h: 'Guard true: <code>h</code> is now about the body.' },
        { tac: 'cases hr : run n c s with', h: 'Split on the body’s result at fuel <code>n</code>.' },
        { tac: '| none    => rw [hr] at h; simp at h', h: 'Contradiction.' },
        { tac: '| some s₁ =>\n    rw [hr] at h', h: '<code>h</code> becomes <code>run n (.loop b c) s₁ = some s\'</code>.' },
        { tac: 'have : run (n + 1) c s = some s₁ := ih c s s₁ hr', h: 'Named because it is used as a rewrite rather than as an argument. The body’s execution lifted to the higher fuel — exactly what the goal’s inner scrutinee needs.' },
        { tac: 'rw [this]', h: 'Turns the goal’s scrutinee <code>run (n+1) c s</code> into <code>some s₁</code>, so the goal reduces to <code>run (n+1) (.loop b c) s₁ = some s\'</code>.' },
        { tac: 'exact ih _ s₁ s\' h', h: 'The underscore is <code>.loop b c</code>, inferred from <code>h</code>. <code>ih</code> at the same command again, licensed by the fuel.' },
        { tac: 'theorem run_le {n m : Nat} (hle : n ≤ m) …', h: 'New theorem. <code>hle : n ≤ m</code> is a proof of an inductive proposition, so it can be inducted on just like an <code>Exec</code> derivation.' },
        { tac: 'induction hle with', h: '<code>Nat.le n</code> has two constructors, <code>Nat.le.refl : Nat.le n n</code> and <code>Nat.le.step : Nat.le n m → Nat.le n (m+1)</code>. So this is induction on how many times you stepped up from <code>n</code>.' },
        { tac: '| refl => exact h', h: '<code>m</code> is <code>n</code>, so the goal is the hypothesis.' },
        { tac: '| step _ ih => exact run_mono _ _ _ _ ih', h: '<code>ih : run m✝ c s = some s\'</code>, goal <code>run m✝.succ c s = some s\'</code>. <code>run_mono</code> concludes <code>run (m + 1) …</code>, definitionally <code>m.succ</code>, so all four underscores are inferred and it goes straight through.' },
        { tac: 'theorem run_complete … := by\n  induction h with', h: 'Third theorem, third thing to induct on: the derivation itself. Each case must exhibit a fuel bound. Note that there is no <code>generalizing</code> here and none is needed — <code>generalizing</code> earns its place only when something <i>else</i> in the context is pinned to a particular instance the induction hypothesis will be used at. In determinism that something was the second derivation. Here there is nothing but the goal.' },
        { tac: '| skip => exact ⟨1, rfl⟩', h: '<code>run 1 .skip s</code> reduces to <code>some s</code> definitionally, so the second component is <code>rfl</code>.' },
        { tac: '| assign => exact ⟨1, rfl⟩', h: 'Same: the <code>assign</code> clause of <code>run</code> produces exactly the state <code>Exec.assign</code> concludes with.' },
        { tac: '| load hl => exact ⟨1, by simp [run, hl]⟩', h: 'Not <code>rfl</code>, because <code>run</code> must first check <code>s.heap l</code> and the answer is known only via <code>hl</code>. Putting <code>hl</code> in the simp set lets <code>simp</code> rewrite the scrutinee and reduce the match.' },
        { tac: '| write hl => exact ⟨1, by simp [run, hl]⟩\n| free hl => exact ⟨1, by simp [run, hl]⟩', h: 'Identical. All three heap commands need one unit of fuel and one lookup fact.' },
        { tac: '| seq _ _ ih₁ ih₂ =>', h: 'The interesting case. Two induction hypotheses, each an existential.' },
        { tac: 'obtain ⟨n₁, h₁⟩ := ih₁\nobtain ⟨n₂, h₂⟩ := ih₂', h: 'Two fuel bounds with no relation between them — the problem the next line solves.' },
        { tac: 'refine ⟨max n₁ n₂ + 1, ?_⟩', h: 'Commit to the witness, leave the obligation as a hole. <code>max</code> because either half might be the deeper one; <code>+ 1</code> because the <code>seq</code> clause consumes one unit before recursing.' },
        { tac: 'simp only [run]', h: 'One unfolding step. The goal becomes the match on <code>run (max n₁ n₂) c₁ s</code>.' },
        { tac: 'rw [run_le (Nat.le_max_left n₁ n₂) h₁]', h: '<code>Nat.le_max_left n₁ n₂ : n₁ ≤ max n₁ n₂</code>. Feeding it and <code>h₁</code> to <code>run_le</code> lifts the first bound, and rewriting with the result turns the goal’s scrutinee into a <code>some</code>.' },
        { tac: 'exact run_le (Nat.le_max_right n₁ n₂) h₂', h: 'The goal has reduced to the second half at the same fuel, which is <code>h₂</code> lifted the same way. This is why monotonicity had to come first.' },
        { tac: '| iteTrue hb _ ih =>\n    obtain ⟨n, hn⟩ := ih\n    exact ⟨n + 1, by simp only [run, hb]; exact hn⟩', h: 'One premise, one bound, and <code>n + 1</code> suffices. <code>hb</code> in the <code>simp only</code> set rewrites the guard to <code>true</code> and reduces the match, after which the goal is <code>hn</code> up to definitional equality.' },
        { tac: '| iteFalse hb _ ih =>\n    obtain ⟨n, hn⟩ := ih\n    exact ⟨n + 1, by simp only [run, hb]; exact hn⟩', h: 'Mirror image.' },
        { tac: '| loopFalse hb => exact ⟨1, by simp only [run, hb]⟩', h: 'The loop exits immediately: one unit of fuel, guard rewritten to <code>false</code>, and <code>some s = some s</code> closed by the <code>rfl</code> that <code>simp only</code> finishes with.' },
        { tac: '| loopTrue hb _ _ ihb ihr =>\n    obtain ⟨n₁, h₁⟩ := ihb\n    obtain ⟨n₂, h₂⟩ := ihr\n    refine ⟨max n₁ n₂ + 1, ?_⟩', h: 'The <code>seq</code> pattern exactly: one bound for the body, one for the remainder of the loop, reconciled by <code>max</code>.' },
        { tac: 'simp only [run, hb]', h: 'One extra ingredient compared with <code>seq</code>: <code>hb</code>, to get past the guard before reaching the body’s match.' },
        { tac: 'rw [run_le (Nat.le_max_left n₁ n₂) h₁]\nexact run_le (Nat.le_max_right n₁ n₂) h₂', h: 'Character for character the <code>seq</code> ending. Sequencing and one loop iteration are the same operation, and — as in <code>exec_deterministic</code> — the proofs coincide.' }
      ],
      deep: [
        { t: 'trace', title: 'run_mono, seq case, starting after <code>simp only [run] at h ⊢</code>',
          start: 'case succ.seq\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → run (n + 1) c s = some s\'\ns s\' : State\nc₁ c₂ : Cmd\nh :\n  (match run n c₁ s with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\n⊢ (match run (n + 1) c₁ s with\n    | some s\' => run (n + 1) c₂ s\'\n    | none => none) =\n    some s\'',
          steps: [
            { tac: 'cases hr : run n c₁ s with | some s₁ => rw [hr] at h',
              state: 'case succ.seq.some\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → run (n + 1) c s = some s\'\ns s\' : State\nc₁ c₂ : Cmd\ns₁ : State\nh :\n  (match some s₁ with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\nhr : run n c₁ s = some s₁\n⊢ (match run (n + 1) c₁ s with\n    | some s\' => run (n + 1) c₂ s\'\n    | none => none) =\n    some s\'',
              h: '<code>h</code>’s scrutinee is now literal, so <code>h</code> is definitionally <code>run n c₂ s₁ = some s\'</code>. The goal is untouched: its scrutinee is at fuel <code>n + 1</code>, and <code>hr</code> says nothing about that.' },
            { tac: 'rw [ih c₁ s s₁ hr]',
              state: 'case succ.seq.some\nn : Nat\nih : ∀ (c : Cmd) (s s\' : State), run n c s = some s\' → run (n + 1) c s = some s\'\ns s\' : State\nc₁ c₂ : Cmd\ns₁ : State\nh :\n  (match some s₁ with\n    | some s\' => run n c₂ s\'\n    | none => none) =\n    some s\'\nhr : run n c₁ s = some s₁\n⊢ (match some s₁ with\n    | some s\' => run (n + 1) c₂ s\'\n    | none => none) =\n    some s\'',
              h: 'The induction hypothesis used as a <i>rewrite rule</i> on the goal. Both scrutinees are now <code>some s₁</code>, and the goal is definitionally <code>run (n + 1) c₂ s₁ = some s\'</code>.' },
            { tac: 'exact ih c₂ s₁ s\' h',
              state: 'No goals.',
              h: 'The same hypothesis again, this time as a function. Nothing here is specific to <code>seq</code> except which command goes where.' }
          ],
          done: 'No goals.' },

        { t: 'trace', title: 'run_le — induction on a proof of ≤',
          start: 'n m : Nat\nhle : n ≤ m\nc : Cmd\ns s\' : State\nh : run n c s = some s\'\n⊢ run m c s = some s\'',
          steps: [
            { tac: 'induction hle with | refl =>',
              state: 'case refl\nn m : Nat\nc : Cmd\ns s\' : State\nh : run n c s = some s\'\n⊢ run n c s = some s\'',
              h: 'In the <code>refl</code> case the upper bound <i>is</i> <code>n</code>, so the goal is literally the hypothesis.' },
            { tac: '| step _ ih =>',
              state: 'case step\nn m : Nat\nc : Cmd\ns s\' : State\nh : run n c s = some s\'\nm✝ : Nat\na✝ : n.le m✝\nih : run m✝ c s = some s\'\n⊢ run m✝.succ c s = some s\'',
              h: 'The induction hypothesis is the statement at the smaller bound and the goal is at one more. Note the printing: <code>Nat.le</code> shows as <code>n.le m✝</code>, and <code>m✝ + 1</code> as <code>m✝.succ</code>.' },
            { tac: 'exact run_mono _ _ _ _ ih',
              state: 'No goals.',
              h: '<code>run_mono</code> concludes <code>run (m✝ + 1) c s = some s\'</code>, definitionally the goal, so <code>exact</code> accepts it even though the display differs.' }
          ],
          done: 'No goals.' },

        { t: 'trace', title: 'run_complete, seq case — where the max is spent',
          start: 'case seq\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nih₁ : ∃ n, run n c₁✝ s✝ = some s\'✝\nih₂ : ∃ n, run n c₂✝ s\'✝ = some s\'\'✝\n⊢ ∃ n, run n (c₁✝ ;; c₂✝) s✝ = some s\'\'✝',
          steps: [
            { tac: 'obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂; refine ⟨max n₁ n₂ + 1, ?_⟩',
              state: 'case seq\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nn₁ : Nat\nh₁ : run n₁ c₁✝ s✝ = some s\'✝\nn₂ : Nat\nh₂ : run n₂ c₂✝ s\'✝ = some s\'\'✝\n⊢ run (max n₁ n₂ + 1) (c₁✝ ;; c₂✝) s✝ = some s\'\'✝',
              h: 'The witness is chosen and the existential is gone. Two independent bounds remain, and neither is directly about <code>max n₁ n₂</code>.' },
            { tac: 'simp only [run]',
              state: 'case seq\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nn₁ : Nat\nh₁ : run n₁ c₁✝ s✝ = some s\'✝\nn₂ : Nat\nh₂ : run n₂ c₂✝ s\'✝ = some s\'\'✝\n⊢ (match run (max n₁ n₂) c₁✝ s✝ with\n    | some s\' => run (max n₁ n₂) c₂✝ s\'\n    | none => none) =\n    some s\'\'✝',
              h: 'The <code>+ 1</code> has been consumed and both recursive calls are at <code>max n₁ n₂</code>.' },
            { tac: 'rw [run_le (Nat.le_max_left n₁ n₂) h₁]',
              state: 'case seq\nc : Cmd\ns s\' s✝ s\'✝ s\'\'✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s\'✝\nh₂✝ : Exec c₂✝ s\'✝ s\'\'✝\nn₁ : Nat\nh₁ : run n₁ c₁✝ s✝ = some s\'✝\nn₂ : Nat\nh₂ : run n₂ c₂✝ s\'✝ = some s\'\'✝\n⊢ (match some s\'✝ with\n    | some s\' => run (max n₁ n₂) c₂✝ s\'\n    | none => none) =\n    some s\'\'✝',
              h: 'The first half’s bound lifted from <code>n₁</code> to <code>max n₁ n₂</code> and used to reduce the scrutinee. The goal is now definitionally <code>run (max n₁ n₂) c₂✝ s\'✝ = some s\'\'✝</code>.' },
            { tac: 'exact run_le (Nat.le_max_right n₁ n₂) h₂',
              state: 'No goals.',
              h: 'The second half’s bound, lifted the same way. Both uses of <code>run_le</code> are essential for the same reason: <code>max</code> is an upper bound of both and nothing more.' }
          ],
          done: 'No goals.' },

        { t: 'detail', title: 'Why <code>max n₁ n₂ + 1</code> and not <code>n₁ + n₂</code>', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Both work, and the sum is what you would use if fuel counted <i>steps</i>. It does not: <code>run</code> hands the same <code>n</code> to both halves of a sequence, so the two halves run in parallel as far as the counter is concerned. The maximum is the right combinator; the sum is a wasteful upper bound.' },
            { t: 'p', h: 'This is also why <code>run_le</code> is needed rather than a bare <code>run_mono</code>: both bounds must be lifted to the same number, and neither of them is one step below it.' }
          ] }
      ],
      pitfall: 'In the <code>loop</code> case of <code>run_mono</code>, expecting <code>simp only [run] at h ⊢</code> to unfold the goal once. It unfolds as often as it can, so the goal contains a <i>second</i> copy of the loop clause nested inside the first. Do not try to make the displayed goal small; work on the outermost scrutinee and let the rest reduce definitionally. The other trap is in <code>run_complete</code>: <code>exact ⟨1, rfl⟩</code> for the <code>load</code> case. It fails, because <code>run 1 (.load x l) s</code> cannot reduce until the scrutinee <code>s.heap l</code> is known, and the only thing that knows it is <code>hl</code> — hence <code>by simp [run, hl]</code>.',
      variants: 'Drop <code>run_le</code> and try to finish <code>run_complete</code> with <code>run_mono</code> alone: you can lift a bound by one, but <code>max n₁ n₂</code> is generally many steps above <code>n₁</code>, so you would have to induct — which is precisely what <code>run_le</code> is. Reverse the direction of <code>run_mono</code>, claiming <code>run (n+1) c s = some s\' → run n c s = some s\'</code>, and it is false: take any program needing depth <code>n+1</code>. Finally, note what <code>run_complete</code> does <b>not</b> say. It gives no bound on the fuel in terms of the program, and there is none, since a loop can run arbitrarily long. It is a pure existence statement, which is all the testing use requires.'
    },

    /* ================================================================
       9 — running programs
       ================================================================ */

    { t: 'sec', s: 'Running a program' },

    { t: 'p', h: 'The two directions together say the relation and the interpreter are the same partial function. The corpus does not record that, and it is worth one line:' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus; compiles against the M5 prelude.',
      src: `theorem exec_iff_run {c : Cmd} {s s' : State} :
    Exec c s s' ↔ ∃ n, run n c s = some s' :=
  ⟨run_complete, fun ⟨n, hn⟩ => run_sound n c s s' hn⟩` },

    { t: 'p', h: '<code>Iff</code>’s two fields are <code>mp</code> and <code>mpr</code>, so the anonymous constructor takes the forward implication first — and <code>run_complete</code> already <i>is</i> that implication, since <code>Exec c s s\'</code> is its hypothesis. On the right, <code>fun ⟨n, hn⟩ =&gt; …</code> is a pattern-matching lambda: the argument is a one-constructor inductive, so the pattern splits it into witness and proof on the way in, and Lean elaborates the whole thing to a <code>match</code>.' },

    { t: 'p', h: 'Now you can run something. Location 7 holds 41; the program reads it into variable 0, adds one, writes it back.' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus; compiles against the M5 prelude.',
      src: `def demoStore : Store := fun _ => 0
def demoHeap  : Heap  := Heap.singleton 7 41
def demoState : State := ⟨demoStore, demoHeap⟩

def bump : Cmd :=
  .load 0 7 ;; .write 7 (.plus (.var 0) (.const 1))

#eval (run 5 bump demoState).map (fun s => s.heap 7)   -- enough fuel
#eval (run 1 bump demoState).map (fun s => s.heap 7)   -- not enough fuel
#eval (run 5 (.load 0 99) demoState).map (fun s => s.store 0)  -- unallocated` },

    { t: 'state', cap: 'The three #eval outputs, in order.', src: 'some (some 42)\nnone\nnone' },

    { t: 'p', h: 'The doubled <code>some</code> in the first line is two different <code>Option</code>s. <code>run 5 bump demoState : Option State</code>, and <code>Option.map</code> pushes the projection under it, so the outer <code>some</code> means <i>the interpreter produced a final state</i>. The inner one is that state’s heap answering at location 7, so it means <i>the cell exists</i>. Its content is 42.' },

    { t: 'note', kind: 'warn', title: '<code>none</code> tells you nothing',
      h: 'The second and third outputs are the same value for entirely unrelated reasons: one program ran out of fuel, the other faulted. Only a <code>some</code> carries information, which is exactly why <code>run_sound</code> is stated with <code>some s\'</code> as its hypothesis and why there is no theorem in the other direction about <code>none</code>.' },

    { t: 'p', h: 'Divergence can still be proved, but only negatively: show that no fuel suffices, then appeal to completeness.' },

    { t: 'code', tag: 'illustration',
      cap: 'Not in the corpus; compiles against the M5 prelude. The <code>show</code> is used exactly as M0 recommends — to make an unreadable goal readable so the next tactics can be written by eye.',
      src: `def spin : Cmd := .loop (.not (.equals (.const 0) (.const 1))) .skip

theorem run_spin_none : ∀ (n : Nat) (s : State), run n spin s = none := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      show (match run n Cmd.skip s with
            | some s' => run n spin s'
            | none    => none) = none
      cases n with
      | zero   => rfl
      | succ m => exact ih s

theorem spin_diverges (s s' : State) : ¬ Exec spin s s' := by
  intro hex
  obtain ⟨n, hn⟩ := run_complete hex
  rw [run_spin_none n s] at hn
  exact absurd hn (by simp)` },

    { t: 'p', h: 'The <code>cases n</code> in the middle looks redundant and is not. After the <code>show</code>, the goal scrutinises <code>run n Cmd.skip s</code> with <code>n</code> a variable, and that term is stuck: <code>run</code> matches its fuel against <code>0</code> and <code>_ + 1</code>, and a bare <code>n</code> is neither. Finish with <code>exact ih s</code> and Lean answers:' },

    { t: 'state',
      src: `Type mismatch
  ih s
has type
  run n spin s = none
but is expected to have type
  (match run n Cmd.skip s with
    | some s' => run n spin s'
    | none => none) =
    none` },

    { t: 'p', h: 'Splitting <code>n</code> unblocks the match on both branches: at <code>0</code> the body returns <code>none</code> and the whole thing is <code>rfl</code>; at <code>m + 1</code> the body returns <code>some s</code>, the match reduces to <code>run n spin s</code>, and that is <code>ih s</code>. A specification true of <code>spin</code> therefore has to be vacuous — there is no final state to constrain — which is what M13’s <code>PartialHoare</code> is for.' },

    /* ================================================================
       10 — close
       ================================================================ */

    { t: 'sec', s: 'What you keep' },

    { t: 'tbl',
      cap: 'Two of the four exercises produce lemmas you will never cite again. They are here for the technique.',
      head: ['Name', 'Used again in', 'What for'],
      rows: [
        ['<code>Cmd</code>, <code>Atom</code>, <code>BExpr</code>, <code>State</code>', 'everything', 'the objects every later theorem quantifies over'],
        ['<code>Exec</code>', 'M6–M14', 'a triple is one existential over it; <code>HeapLocal</code> and <code>Preserves</code> are properties of it'],
        ['<code>Store.set</code>', 'M6 onwards', 'the substitution operation of M6 is defined in terms of it'],
        ['<code>exec_deterministic</code>', 'M13, once', '<code>partial_of_total</code>: a total-correctness triple implies the partial one'],
        ['<code>exec_skip_inv</code>', 'never', 'a warm-up; the technique is what you keep, not the lemma'],
        ['<code>run</code>, <code>run_sound</code>, <code>run_complete</code>', 'never', 'testing. <code>#eval</code> your programs before you prove things about them']
      ] },

    { t: 'p', h: 'Every rule of <code>Exec</code> that changes anything changes it in one of three ways: <code>Store.set</code>, <code>Heap.write</code>, <code>Heap.erase</code>. Two of the three are heap operations, and Phase 1 has assertions that describe heaps. The third is not, and Phase 1 has nothing that describes stores — <code>emp</code>, <code>↦</code> and <code>∗</code> carry <code>σ</code> and never read it.' },

    { t: 'p', h: 'So the simplest triple you could want to state is already blocked. <code>Exec.assign</code> takes <code>s</code> to a state whose store is <code>Store.set s.store x (e.eval s.store)</code>; a precondition holds at the old store and a postcondition must hold at the new one; and there is no operation on <code>Assertion</code> that gets you from one to the other. M6 defines the triple, and it needs that operation first.' },

    { t: 'dod', h: 'You have a relational semantics suitable for proofs, an executable interpreter suitable for testing, and a theorem saying they are the same partial function. You can invert an <code>Exec</code> hypothesis without thinking, you know what <code>generalizing</code> is for, and a hypothesis that displays as an unreduced <code>match</code> no longer stops you.' }

  ]
});
