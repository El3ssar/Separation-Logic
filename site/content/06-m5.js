/* M5 — A tiny imperative language
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m5",
  "num": "M5",
  "phase": "Phase 2 · Program logic",
  "title": "A tiny imperative language",
  "blurb": "Syntax, a big-step relational semantics, and an executable interpreter proved to agree with it.",

  "orient": {
    "youWill": [
      "Read an <code>inductive</code> declaration as a grammar, and an <code>inductive … : … → Prop</code> as a set of inference rules — and know which is which by looking at the arrow before <code>Prop</code>.",
      "Use <code>cases h</code> on a <i>derivation</i> to do <b>inversion</b>: read backwards from a conclusion to the only rules that could have produced it.",
      "Run <code>induction</code> over a derivation, and say precisely why the <code>seq</code> case fails without <code>generalizing</code>.",
      "Write a fuel-indexed interpreter that Lean accepts as terminating, and prove it agrees with the relation in both directions.",
      "Read a goal in which a hypothesis <i>displays</i> as an unreduced <code>match</code> but is definitionally the thing you want."
    ],
    "needs": [
      "M0 in your fingers: <code>funext</code>, <code>by_cases</code>, <code>simp [h]</code>, the <code>cases hl : e with …</code> form that records its equation, and the anonymous constructor <code>⟨…⟩</code>.",
      "<code>Heap</code>, <code>Heap.write</code>, <code>Heap.erase</code> from M1. Those are the only heap operations this language can perform.",
      "Nothing at all from M2–M4. This chapter never mentions <code>∗</code>, <code>disjoint</code>, or entailment. Phase 1 and Phase 2 first meet in M6."
    ],
    "payoff": "Every theorem in the rest of the workbook is a statement about <code>Exec</code>: a Hoare triple is one existential quantifier over it, the frame rule is a locality property of it, and a loop invariant is an induction on it."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "Phase 1 was pure resource algebra: no programs anywhere. Now we introduce the smallest language that can get memory wrong, so that we have something worth verifying."
    },
    {
      "t": "p",
      "h": "“Smallest” is a real design constraint, not modesty. Every constructor you add to <code>Cmd</code> is a case in every future proof by <code>cases</code> or <code>induction</code> — including the ones in M8 and M13 that are already long. So the language has exactly four memory operations (read a cell, write a cell, free a cell, and in the optional M14, allocate one), one variable assignment, and the three control constructs. Nothing else."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>Atom</code>, <code>BExpr</code>",
          "h": "Expressions. They are <b>pure</b>: evaluating one reads the store, never the heap, and cannot fault. This is why they are given by an <i>evaluation function</i> and not a relation."
        },
        {
          "k": "<code>Cmd</code>",
          "h": "Commands. These touch the heap, so they can fault. This is the type every later chapter quantifies over."
        },
        {
          "k": "<code>Exec c s s'</code>",
          "h": "An inductive <i>relation</i>: “<code>c</code>, started in <code>s</code>, terminates in <code>s'</code>”. The semantics you prove with."
        },
        {
          "k": "<code>run n c s</code>",
          "h": "A recursive <i>function</i> with a fuel bound, returning <code>Option State</code>. The semantics you test with. Two exercises establish that it computes exactly the relation."
        }
      ]
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "Where this chapter sits",
      "h": "Apart from M0, which is pure Lean technique, this is the only chapter with no separation logic in it. It is scaffolding: you are building the object that M6–M14 talk about. If you read one thing carefully, make it the <code>Exec</code> declaration — you will be inverting and inducting on it for the next eight chapters."
    },

    {
      "t": "sec",
      "s": "Expressions, stores, and states"
    },
    {
      "t": "anat",
      "src": "inductive Atom where\n  | const : Nat → Atom\n  | var   : Var → Atom\n  | plus  : Atom → Atom → Atom\n  | minus : Atom → Atom → Atom\n  deriving Repr\n\ndef Atom.eval (σ : Store) : Atom → Val\n  | .const v  => v\n  | .var x    => σ x\n  | .plus a b => a.eval σ + b.eval σ\n  | .minus a b => a.eval σ - b.eval σ\n\ndef Store.set (σ : Store) (x : Var) (v : Val) : Store :=\n  fun y => if y = x then v else σ y\n\nstructure State where\n  store : Store\n  heap  : Heap",
      "parts": [
        {
          "m": "inductive Atom where",
          "h": "The first <code>inductive</code> declaration in this workbook. Read it as: <code>Atom</code> is the smallest set closed under these four formation rules, and <i>nothing else is an <code>Atom</code></i>. That last clause is not decoration — it is what makes <code>cases</code> and <code>induction</code> exhaustive, and it is what Lean generates a recursor for."
        },
        {
          "m": "| const : Nat → Atom",
          "h": "A constructor. Its full name is <code>Atom.const</code>, and you may write it as <code>.const</code> whenever Lean already knows the expected type is <code>Atom</code>. That leading-dot form is used constantly below; it is not a separate feature, just name resolution against the expected type."
        },
        {
          "m": "deriving Repr",
          "h": "Generates a <code>Repr</code> instance — a printer — so that <code>#eval (Atom.plus (.const 3) (.var 1))</code> answers <code>Atom.plus (Atom.const 3) (Atom.var 1)</code> instead of failing. Nothing logical depends on it. Note that <code>Cmd</code> and <code>State</code> do <i>not</i> derive <code>Repr</code>: <code>#eval bump</code> would report <i>could not synthesize a <code>Repr</code> or <code>ToString</code> instance for type <code>Cmd</code></i>. That is why the <code>#eval</code>s at the end of this chapter project a number out of the final state instead of printing the state."
        },
        {
          "m": "def Atom.eval (σ : Store) : Atom → Val",
          "h": "Note the argument order: the store comes <i>first</i>, and the <code>Atom</code> is the anonymous last argument consumed by the pattern match. This matters for how Lean prints goals — see the note below."
        },
        {
          "m": "| .const v  => v",
          "h": "Definition by pattern matching on the constructor. Lean compiles this to an application of the recursor, and — importantly for later — the equation <code>Atom.eval σ (.const v) = v</code> holds <b>definitionally</b>, so <code>rfl</code> proves it and <code>exact</code> sees through it without any rewriting."
        },
        {
          "m": "a.eval σ + b.eval σ",
          "h": "Structural recursion: the recursive calls are on <code>a</code> and <code>b</code>, which are strict subterms of <code>.plus a b</code>. Lean accepts this without a termination proof. Keep this in mind — <code>run</code> at the end of the chapter is exactly the case where this trick is <i>not</i> available."
        },
        {
          "m": "fun y => if y = x then v else σ y",
          "h": "This is literally M0's <code>update</code>, retyped. <code>Store = Var → Val = Nat → Nat</code>, so <code>@Store.set = @update</code> holds by <code>rfl</code>, and every lemma you proved in M0 — <code>update_same</code>, <code>update_other</code>, <code>update_shadow</code>, <code>update_comm</code> — is a lemma about stores."
        },
        {
          "m": "structure State where",
          "h": "A <code>structure</code> is a one-constructor inductive with named projections. So you may build a state with the anonymous constructor <code>⟨σ, h⟩</code> and take it apart with <code>s.store</code> and <code>s.heap</code>. Two states are equal exactly when both fields are, and Lean will close such goals by <code>rfl</code> when the fields are syntactically equal."
        }
      ]
    },
    {
      "t": "cmp",
      "left": {
        "t": "The store is total",
        "h": "<code>Store = Var → Val</code>. Every variable has a value, always. Reading a variable cannot fail, so <code>Atom.eval</code> is a plain function into <code>Val</code> with no <code>Option</code> anywhere.",
        "kind": "good"
      },
      "right": {
        "t": "The heap is partial",
        "h": "<code>Heap = Loc → Option Val</code>. A cell may not exist. Reading one <i>can</i> fail, so <code>load</code> is a command with a premise, not an expression."
      }
    },
    {
      "t": "p",
      "h": "That asymmetry is the whole design. It is why expressions are given by a total function and commands by a relation, why the interesting Hoare rules are the four heap rules and not the assignment rule, and why separation logic is about the heap and not the store. If you made the store partial too you would have to thread a fault through <code>Atom.eval</code>, every expression would return <code>Option Val</code>, and every rule in M7 would carry a “the variables are defined” side condition that says nothing."
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "The printer will not echo what you wrote",
      "h": "You write <code>e.eval s.store</code>. Lean prints <code>Atom.eval s.store e</code>. Dot notation is only used <i>on output</i> when the receiver is the first explicit argument, and in <code>Atom.eval (σ : Store) : Atom → Val</code> the <code>Atom</code> is second. By contrast <code>Store.set (σ : Store) …</code> does take its receiver first, so the same goal prints <code>s.store.set x v</code> where the source says <code>Store.set s.store x v</code>. Expect both surprises in every goal state in this chapter; they are the same term."
    },
    {
      "t": "note",
      "kind": "info",
      "title": "A two-line extension worth making early",
      "h": "The original syllabus gives <code>Atom</code> only <code>const</code> and <code>var</code>. That is enough for M5–M12, but it makes every loop trivial, because no expression can ever change value. Adding <code>plus</code> and <code>minus</code> costs two lines, breaks nothing (every later proof is generic in <code>e : Atom</code>), and lets M13 verify a loop that actually terminates for a reason. Do it now."
    },
    {
      "t": "detail",
      "title": "Why subtraction on Nat is not a problem here",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "<code>Val = Nat</code>, so <code>.minus</code> is truncated subtraction: <code>3 - 5 = 0</code>. A mathematician's instinct is that this is a bug waiting to happen. It is not, for this workbook, because nothing we prove depends on the arithmetic being a group — the M13 loop counts a variable down to zero and the invariant is stated in terms of the value that is actually there."
        },
        {
          "t": "p",
          "h": "Switching <code>Val</code> to <code>Int</code> would cost you nothing in M5 and would break nothing later, but it also buys nothing, and <code>Nat</code> keeps <code>#eval</code> output readable. This is the kind of decision worth making once and not revisiting."
        }
      ]
    },

    {
      "t": "sec",
      "s": "Booleans and commands"
    },
    {
      "t": "code",
      "src": "inductive BExpr where\n  | equals : Atom → Atom → BExpr\n  | not    : BExpr → BExpr\n\ndef BExpr.eval (σ : Store) : BExpr → Bool\n  | .equals a b => a.eval σ == b.eval σ\n  | .not b      => !(b.eval σ)"
    },
    {
      "t": "p",
      "h": "Two things here are Lean-specific and worth naming. First, <code>==</code> is not <code>=</code>: it is the <code>Bool</code>-valued decidable-equality test, whereas <code>=</code> builds a <code>Prop</code>. Second, <code>BExpr.eval</code> lands in <code>Bool</code>, not <code>Prop</code>. That is a design decision with a rejected alternative."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Rejected: guards are propositions",
        "h": "<code>BExpr.eval : Store → BExpr → Prop</code>. Mathematically cleaner. But then <code>run</code> cannot branch on a guard — it would need a <code>Decidable</code> instance conjured at every use — and the two <code>ite</code> constructors of <code>Exec</code> would have premises <code>φ</code> and <code>¬ φ</code> that no longer contradict each other by computation.",
        "kind": "bad"
      },
      "right": {
        "t": "Chosen: guards are booleans",
        "h": "<code>BExpr.eval : Store → BExpr → Bool</code>. The <code>Exec</code> premises become <code>b.eval s.store = true</code> and <code>= false</code>, so the two branches are killed by <code>rw</code> plus <code>simp</code> — one line each. Every mismatched-branch case in <code>exec_deterministic</code> depends on exactly this.",
        "kind": "good"
      }
    },
    {
      "t": "code",
      "src": "inductive Cmd where\n  | skip\n  | assign : Var → Atom → Cmd\n  | load   : Var → Loc → Cmd\n  | write  : Loc → Atom → Cmd\n  | free   : Loc → Cmd\n  | seq    : Cmd → Cmd → Cmd\n  | ite    : BExpr → Cmd → Cmd → Cmd\n  | loop   : BExpr → Cmd → Cmd\n\ninfixr:60 \" ;; \" => Cmd.seq"
    },
    {
      "t": "txt",
      "src": "  Cmd.skip                    skip\n  Cmd.assign x e              x := e            (store only)\n  Cmd.load   x l              x := [l]          (heap read  — can fault)\n  Cmd.write  l e              [l] := e          (heap write — can fault)\n  Cmd.free   l                free l            (deallocate — can fault)\n  Cmd.seq    c₁ c₂            c₁ ;; c₂\n  Cmd.ite    b c₁ c₂          if b then c₁ else c₂\n  Cmd.loop   b c              while b do c",
      "cap": "The eight constructors and the concrete syntax they stand for."
    },
    {
      "t": "p",
      "h": "<code>infixr:60 \" ;; \" => Cmd.seq</code> declares notation. <code>infixr</code> makes it right-associative, so <code>a ;; b ;; c</code> parses as <code>a ;; (b ;; c)</code>; <code>60</code> is the precedence. The notation is purely surface syntax — <code>c₁ ;; c₂</code> <i>is</i> <code>Cmd.seq c₁ c₂</code>, and Lean will print it back to you with the <code>;;</code>."
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "Why the semicolon is doubled",
      "h": "A single <code>;</code> is the tactic sequencer, and declaring <code>infixr:60 \" ; \" => Cmd.seq</code> really does break proofs — though not in the way you would guess. The declaration itself is accepted, and <code>def eg : Cmd := .skip ; .skip</code> elaborates fine. What breaks is every later tactic block: <code>;</code> is now also a <i>term</i>-level infix, so in <code>cases h; rfl</code> Lean parses the argument of <code>cases</code> as the term <code>Cmd.seq h rfl</code> and reports <i>Application type mismatch: the argument <code>h</code> has type <code>Exec Cmd.skip s s'</code> of sort <code>Prop</code> but is expected to have type <code>Cmd</code> of sort <code>Type</code></i>, followed by unsolved goals where the <code>rfl</code> should have gone. Doubling the token costs nothing and avoids all of it."
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Naming",
      "h": "<code>while</code> is a reserved keyword in Lean 4, so the constructor is <code>loop</code>. You <i>can</i> force it with French quotes — <code>| «while» : BExpr → Cmd → Cmd</code> — and it works, but then every <code>cases</code> alternative needs the quotes too. Not worth it."
    },
    {
      "t": "note",
      "kind": "key",
      "title": "Why the loop constructors are here already",
      "h": "The syllabus builds the loop-free language first and extends it in M13. Resist that. Extending an inductive type means redoing every proof about it. Declare <code>ite</code> and <code>loop</code> now, ignore them until M13, and you will never rework anything. This is ordinary engineering judgement, and it matters more in a proof assistant than in a compiler."
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "The limitation you are accepting",
      "h": "<code>load : Var → Loc → Cmd</code> takes a <i>literal</i> location, not an expression. So you can write <code>x := [7]</code> but not <code>x := [y]</code>: the language cannot compute an address. That is deliberate — making the address an <code>Atom</code> would force every heap rule in M7 to quantify over the value of that expression, doubling the bookkeeping. The price is that M10's linked-list predicates describe structures no program in this language can walk — following a next-pointer means loading from an address held in a variable, and there is no constructor for that. M10 is consistent with the limitation rather than fighting it: its whole corpus is assertions and entailments, with no <code>Cmd</code>, no <code>Exec</code> and no triple in it."
    },

    {
      "t": "sec",
      "s": "Big-step semantics as an inductive relation"
    },
    {
      "t": "p",
      "h": "<code>Exec c s s'</code> means: <i>starting from <code>s</code>, the command <code>c</code> terminates and ends in <code>s'</code></i>. Because it is an inductive relation, the absence of a derivation carries meaning:"
    },
    {
      "t": "ul",
      "items": [
        "<b>Stuck</b> — <code>load x l</code> with <code>l</code> unallocated has no derivation at all. That is how memory faults are modelled: not by an error value, but by the impossibility of running.",
        "<b>Diverging</b> — a non-terminating loop also has no derivation. Big-step semantics cannot tell “crashed” from “ran forever”; M13 is where that distinction is made explicit, via partial versus total correctness."
      ]
    },
    {
      "t": "cmp",
      "left": {
        "t": "Rejected: a function <code>Cmd → State → Option State</code>",
        "h": "The obvious mathematician's move: the semantics <i>is</i> a partial function, so define it as one. Lean will not accept it: the <code>loop</code> clause recurses on the same command, so there is no structural decrease and no obvious well-founded order. You would have to build the least fixed point by hand — which is what <code>inductive</code> does for you.",
        "kind": "bad"
      },
      "right": {
        "t": "Chosen: a relation <code>Cmd → State → State → Prop</code>",
        "h": "An inductive family is the least relation closed under the rules, and Lean builds it for free. It is total in the sense that it is <i>defined</i> for every command; it just may be inhabited by nothing. “Stuck” and “diverging” both come out as “no derivation”, which is exactly the disjunction a Hoare triple wants to rule out in one stroke.",
        "kind": "good"
      }
    },
    {
      "t": "anat",
      "src": "inductive Exec : Cmd → State → State → Prop where\n  | skip {s} : Exec .skip s s\n  | assign {s x e} :\n      Exec (.assign x e) s ⟨Store.set s.store x (e.eval s.store), s.heap⟩\n  | load {s x l v} (hl : s.heap l = some v) :\n      Exec (.load x l) s ⟨Store.set s.store x v, s.heap⟩\n  | write {s l e old} (hl : s.heap l = some old) :\n      Exec (.write l e) s ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩\n  | free {s l v} (hl : s.heap l = some v) :\n      Exec (.free l) s ⟨s.store, Heap.erase s.heap l⟩\n  | seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') :\n      Exec (c₁ ;; c₂) s s''\n  | iteTrue {s s' b c₁ c₂} (hb : b.eval s.store = true) (h : Exec c₁ s s') :\n      Exec (.ite b c₁ c₂) s s'\n  | iteFalse {s s' b c₁ c₂} (hb : b.eval s.store = false) (h : Exec c₂ s s') :\n      Exec (.ite b c₁ c₂) s s'\n  | loopFalse {s b c} (hb : b.eval s.store = false) :\n      Exec (.loop b c) s s\n  | loopTrue {s s' s'' b c} (hb : b.eval s.store = true)\n      (hbody : Exec c s s') (hrest : Exec (.loop b c) s' s'') :\n      Exec (.loop b c) s s''",
      "cap": "The ten rules of the language. Eight callouts, covering every feature of the declaration you will meet again.",
      "parts": [
        {
          "m": "inductive Exec : Cmd → State → State → Prop where",
          "h": "All three arguments appear <i>after</i> the colon, so they are <b>indices</b>, not parameters. That distinction is the entire reason <code>cases</code> can do inversion: when you case on <code>h : Exec .skip s s'</code>, Lean is allowed to unify the indices of the hypothesis with those of each constructor, and discard the constructors that cannot match. Parameters are fixed across all constructors and are never unified away; indices are. If <code>Cmd</code> were a parameter, written <code>inductive Exec (c : Cmd) : …</code>, that unification would not happen and every case would survive — and in fact you could not declare <i>this</i> relation that way at all, because each rule concludes at a different command. Those are two sides of the same observation."
        },
        {
          "m": "| skip {s} : Exec .skip s s",
          "h": "Braces make <code>s</code> implicit: Lean infers it from the indices when you write <code>Exec.skip</code>. Note that the same <code>s</code> occurs in both state positions. That single repetition is the whole content of <code>exec_skip_inv</code> — inversion reads it back out as an equation."
        },
        {
          "m": "(hl : s.heap l = some v)",
          "h": "A <b>premise</b>, in round brackets, therefore explicit: to build this derivation you must hand over a proof that the cell exists. There is no rule for <code>load</code> from an unallocated location, so there is no derivation, so the program is <i>stuck</i>. This one hypothesis is the entire fault model of the language."
        },
        {
          "m": "⟨Store.set s.store x v, s.heap⟩",
          "h": "The resulting state, built with the anonymous constructor: new store, unchanged heap. Note that the value <code>v</code> written into the store is the same <code>v</code> that <code>hl</code> found in the heap — the rule is what ties them together, and <code>exec_deterministic</code>'s <code>load</code> case is nothing but pulling that tie back apart."
        },
        {
          "m": "{s l e old}",
          "h": "<code>old</code> is bound here and used only in the premise <code>s.heap l = some old</code>; it does not appear in the conclusion. So the rule says “the cell must exist, and I do not care what was in it”. That is the small-footprint shape M7 will formalise as <code>l ↦ _</code>. It is also why the <code>write</code> case of <code>exec_deterministic</code> is a bare <code>rfl</code> while <code>load</code> needs real work."
        },
        {
          "m": "(h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'')",
          "h": "Two recursive premises sharing an intermediate state <code>s'</code>, which is implicit and therefore <i>existentially</i> quantified from the outside: to prove <code>Exec (c₁ ;; c₂) s s''</code> you must produce some <code>s'</code>. When you invert such a hypothesis, <code>cases</code> hands the intermediate state back to you as a fresh variable."
        },
        {
          "m": "Exec (c₁ ;; c₂) s s''",
          "h": "The conclusion uses the <code>;;</code> notation, and so will every goal Lean prints — see the traces below, where the pretty-printer writes <code>c₁✝ ;; c₂✝</code>."
        },
        {
          "m": "(hrest : Exec (.loop b c) s' s'')",
          "h": "The recursive premise is at the <i>same</i> command. This is legal for an inductive <i>relation</i> — the derivation tree still gets smaller — and it is exactly the clause that makes a structurally recursive interpreter impossible. Hold on to it until the fuel discussion."
        }
      ]
    },
    {
      "t": "txt",
      "src": "  Read each constructor as an inference rule:\n\n      s.heap l = some v                      Exec c₁ s s'      Exec c₂ s' s''\n    ─────────────────────────────────      ──────────────────────────────────\n     Exec (load x l) s ⟨σ[x:=v], h⟩              Exec (c₁ ;; c₂) s s''\n\n\n     b.eval s.store = true    Exec c s s'    Exec (loop b c) s' s''\n    ──────────────────────────────────────────────────────────────\n                       Exec (loop b c) s s''\n\n  A proof of `Exec c s s'` IS a finite tree built from these rules.\n  `induction` walks such a tree; `cases` looks at its last step only.",
      "cap": "The constructors, drawn the way you would write them on a blackboard."
    },
    {
      "t": "p",
      "h": "The two tactics you will use on <code>Exec</code> hypotheses do different things and it is worth fixing the difference now. <code>cases h</code> asks <i>which rule was applied last</i>, and gives you one goal per constructor that could possibly have that conclusion — no induction hypotheses. <code>induction h</code> asks the same question but additionally hands you, in each recursive case, the statement you are proving, already established for the sub-derivations. Inversion is a special case of induction where you throw the hypotheses away."
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "Read <code>Exec</code> as the definition of <b>safety</b>. A Hoare triple in M6 will say “there <i>exists</i> a final state”, and that single existential quantifier is simultaneously asserting termination <i>and</i> the absence of memory faults. Getting that in one stroke is a real advantage of the big-step presentation."
    },
    {
      "t": "code",
      "src": "-- \"stuck\" is a theorem, not a convention: with the cell absent,\n-- no final state exists at all.\ntheorem load_stuck (x : Var) (l : Loc) (s : State) (hl : s.heap l = none) :\n    ¬ ∃ s', Exec (.load x l) s s' := by\n  intro ⟨s', hex⟩\n  cases hex with\n  | load hl' => rw [hl] at hl'; exact absurd hl' (by simp)",
      "tag": "illustration",
      "cap": "Not in the corpus; compiles against the M5 prelude. Two lines, and the second is the whole fault model."
    },
    {
      "t": "p",
      "h": "That proof is the shape of every inversion argument in this chapter: <code>cases hex</code> leaves only the <code>load</code> constructor, whose premise <code>hl' : s.heap l = some v</code> is then rewritten by <code>hl</code> into <code>none = some v</code>, which <code>simp</code> refutes. Keep it in view while reading <code>exec_deterministic</code>, where <i>rewrite one premise with the other, then refute</i> is the whole content of four of the ten cases."
    },
    {
      "t": "p",
      "h": "Two Lean details in that first line, since both recur. <code>¬ φ</code> is by definition <code>φ → False</code>, so a goal <code>¬ ∃ s', …</code> is a function goal and <code>intro</code> applies to it — which is why the proof of a negation starts by <i>assuming</i> the thing. And <code>intro ⟨s', hex⟩</code> introduces <i>and immediately destructs</i>: the hypothesis would be an <code>∃ s', Exec …</code>, a one-constructor inductive with two fields, so the pattern names the witness <code>s'</code> and the proof <code>hex</code> in one step. Writing <code>intro hex</code> and then <code>obtain ⟨s', hex⟩ := hex</code> is the same proof spelled out."
    },

    {
      "t": "sec",
      "s": "Exercises · inversion and determinism"
    },
    {
      "t": "p",
      "h": "Two exercises. The first is a warm-up whose only job is to show you what <code>cases</code> does to a relation hypothesis; you will not use the resulting lemma again. The second is used exactly once in the whole workbook — in M13, to derive partial correctness from total correctness — but it is the standard drill for the technique that <i>every</i> later chapter needs."
    },
    {
      "t": "ex",
      "id": "m5-1",
      "name": "exec_skip_inv",
      "hard": false,
      "why": "Your first inversion. <code>cases h</code> on an <code>Exec</code> hypothesis looks at which constructors could possibly have produced it; for <code>.skip</code> there is exactly one, and it forces <code>s' = s</code>. The habit you are building: when a hypothesis is a derivation, you take it apart rather than reasoning about it.",
      "setup": "Everything in the chapter so far is in scope. You need no lemmas — just <code>cases</code> and <code>rfl</code>.",
      "goal": "theorem exec_skip_inv {s s' : State} (h : Exec .skip s s') : s' = s",
      "hints": [
        "You are given a proof that something is in an inductively defined relation. What can you do with a proof of an inductive proposition? The same thing you do with a proof of <code>A ∨ B</code>: split on how it was built.",
        "<code>cases h</code>. There are ten constructors of <code>Exec</code>, but nine of them conclude with a command that is not <code>.skip</code>, and Lean discards those by unifying the indices. You are left with one goal.",
        "After <code>cases h</code> the goal is <code>s = s</code> — note it is <i>not</i> <code>s' = s</code> any more, because the constructor's own equation replaced <code>s'</code>. So: <code>cases h; rfl</code>."
      ],
      "hint": "<code>cases h; rfl</code>.",
      "sol": "theorem exec_skip_inv {s s' : State} (h : Exec .skip s s') : s' = s := by\n  cases h; rfl",
      "expl": "<code>cases</code> unifies the indices of the relation with the constructor’s. The <code>skip</code> constructor has both states equal, so after <code>cases</code> the goal is <code>s = s</code>.",
      "walk": [
        {
          "tac": "cases h",
          "h": "Lean tries to unify the indices of <code>h : Exec .skip s s'</code> against the conclusion of each of the ten constructors. Only <code>Exec.skip : Exec .skip s s</code> matches on the command index. Unifying its state indices with <code>s</code> and <code>s'</code> forces <code>s'</code> to <i>be</i> <code>s</code>, so Lean substitutes it away everywhere, including in the goal."
        },
        {
          "tac": "rfl",
          "h": "The goal is now <code>s = s</code>. <code>rfl</code> is the constructor of <code>Eq</code>; it closes any goal whose two sides are definitionally equal. Here they are literally the same variable."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "exec_skip_inv, tactic by tactic",
          "start": "s s' : State\nh : Exec Cmd.skip s s'\n⊢ s' = s",
          "steps": [
            {
              "tac": "cases h",
              "state": "case skip\ns : State\n⊢ s = s",
              "h": "Everything changed at once. <code>s'</code> is gone from the context — not renamed, <i>eliminated</i>, because the <code>skip</code> rule can only conclude with the two states equal. The <code>case skip</code> line names the surviving constructor; there is no <code>case assign</code>, no <code>case load</code>, because none of those can conclude <code>Exec Cmd.skip _ _</code>."
            },
            {
              "tac": "rfl",
              "state": "No goals.",
              "h": "Done."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "Notice what the goal display tells you that the source does not. You wrote <code>.skip</code>; Lean prints <code>Cmd.skip</code>. The leading dot is elaboration-time sugar and does not survive into the term."
        },
        {
          "t": "detail",
          "title": "Why the goal is not <code>s' = s'</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "When <code>cases</code> unifies <code>Exec .skip s s'</code> with <code>Exec .skip ?s ?s</code>, it gets <code>?s = s</code> from the first index and <code>?s = s'</code> from the second, hence <code>s = s'</code>. It then substitutes one for the other and keeps the one that was introduced <i>earlier</i>, which is <code>s</code>. That is why you see <code>s = s</code> rather than <code>s' = s'</code>. It never matters, but it does explain why the variable that vanishes is sometimes not the one you expected."
            }
          ]
        }
      ],
      "pitfall": "Reaching for <code>rw [h]</code> or <code>exact h.symm</code>. <code>h</code> is not an equation — it is a derivation, an element of an inductively defined family. The equation you want is <i>extracted</i> from it by case analysis; it is not sitting there to be used.",
      "variants": "Try the same statement for <code>load</code>: <code>(h : Exec (.load x l) s s') : ∃ v, s.heap l = some v ∧ s' = ⟨Store.set s.store x v, s.heap⟩</code>. Now <code>cases h with | load hl => …</code> hands you both the premise <code>hl</code> and the shape of <code>s'</code>, and you finish with <code>exact ⟨_, hl, rfl⟩</code>. The pattern generalises: inversion on a constructor with <i>k</i> premises gives you those <i>k</i> premises plus the equations forced by its indices. For <code>skip</code>, <i>k</i> = 0 and there is exactly one equation, which is why this exercise is one line."
    },
    {
      "t": "p",
      "h": "The next proof is long, but it has only three ideas in it, repeated. Before you start: it is the first proof in this workbook that uses <code>induction</code> at all. You have seen the <code>with | name => …</code> case syntax before — M2's <code>union_eq_none</code> writes <code>cases hl : h₁ l with | none => … | some v => …</code> — but there the names were <code>Option</code>'s two constructors and neither carried anything you had to bind. Here the names are constructors of a relation <i>you</i> declared, each with its own premises, and the binders after the name matter. Read the two blocks below first."
    },
    {
      "t": "steps",
      "title": "How “induct on one derivation, invert the other” goes",
      "items": [
        {
          "k": "Choose which derivation to induct on",
          "h": "You have two, <code>h₁ : Exec c s s₁</code> and <code>h₂ : Exec c s s₂</code>. Induct on <code>h₁</code>. This gives you one goal per rule that <code>h₁</code> could have ended with, plus induction hypotheses for its sub-derivations."
        },
        {
          "k": "Generalise the other final state",
          "h": "<code>generalizing s₂</code> re-quantifies <code>s₂</code> before running the induction, so each induction hypothesis reads <code>∀ {s₂}, Exec c₁ s s₂ → s' = s₂</code> rather than being pinned to the one <code>s₂</code> you started with. In the <code>seq</code> case you need the hypothesis at the <i>intermediate</i> state, which is not that one."
        },
        {
          "k": "Invert the second derivation in each case",
          "h": "Inside case <code>skip</code>, <code>h₂ : Exec .skip s s₂</code>, so <code>cases h₂</code> leaves one branch. Inside case <code>iteTrue</code>, <code>h₂ : Exec (.ite b c₁ c₂) s s₂</code>, so <code>cases h₂</code> leaves <i>two</i> branches — and the mismatched one is refuted by the guards."
        },
        {
          "k": "Close each branch by one of four moves",
          "h": [
            {
              "t": "ul",
              "items": [
                "<b>Deterministic by construction</b> (<code>skip</code>, <code>assign</code>, <code>write</code>, <code>free</code>) — both sides are the same expression; <code>rfl</code>.",
                "<b>Value-carrying</b> (<code>load</code>) — two lookups of the same cell; <code>rw</code> then <code>cases</code> on <code>some v = some v'</code>.",
                "<b>Compositional</b> (<code>seq</code>, <code>loopTrue</code>) — first induction hypothesis identifies the intermediate states, second finishes.",
                "<b>Guard clash</b> (the four <code>ite</code>/<code>loop</code> cross-cases) — <code>rw [hb] at hb'</code> turns <code>hb'</code> into <code>true = false</code>."
              ]
            }
          ]
        }
      ]
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Reading <code>induction … with | name args =&gt; …</code>",
      "h": "The names after <code>|</code> are constructor names of <code>Exec</code>, and the identifiers after each name bind that constructor's arguments <i>in order</i>, with the induction hypotheses appended at the end. So <code>| seq _ _ ih₁ ih₂ =&gt;</code> means: ignore the two premises <code>h₁ h₂</code>, name their induction hypotheses <code>ih₁</code> and <code>ih₂</code>. And <code>| loopTrue hb _ _ ihb ihr =&gt;</code> means: keep the guard <code>hb</code>, drop <code>hbody</code> and <code>hrest</code>, name their hypotheses. Any argument you write <code>_</code> for is still in the context — it just gets an inaccessible name like <code>h₁✝</code>, which is why the goal states below are full of daggers."
    },
    {
      "t": "ex",
      "id": "m5-2",
      "name": "exec_deterministic",
      "hard": true,
      "why": "The language has no nondeterminism, so at most one final state exists. You will need this in M13 to derive partial correctness from total correctness. It is also the standard drill for “induction on one derivation, inversion on the other”.",
      "setup": "You need no lemmas from earlier chapters. Everything is <code>induction</code>, <code>cases</code>, <code>rw</code>, <code>rfl</code>, <code>absurd</code>, and two uses of <code>▸</code> — one in <code>seq</code>, one in <code>loopTrue</code>, and they are the same move.",
      "goal": "theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂",
      "hints": [
        "There are two derivations and one goal. You cannot induct on both. Induct on one and take the other apart, case by case.",
        "<code>induction h₁ generalizing s₂</code>, then in each case <code>cases h₂</code>. The <code>generalizing</code> is essential: without it, the induction hypothesis is stated only for the fixed <code>s₂</code> you started with, and the <code>seq</code> case fails.",
        "In the <code>seq</code> case you get <code>ih₁ : ∀ {s₂}, Exec c₁ s s₂ → s' = s₂</code> and <code>ih₂</code> likewise, plus <code>h₁'</code>, <code>h₂'</code> from inverting <code>h₂</code>. So <code>ih₁ h₁' : s' = s'₂</code> — an equation between intermediate states. Transport <code>h₂'</code> along it with <code>▸</code> and feed the result to <code>ih₂</code>.",
        "The four cross-cases (<code>iteTrue</code> met with <code>iteFalse</code>, and so on) have <code>hb : b.eval s.store = true</code> and <code>hb' : b.eval s.store = false</code> in scope. <code>rw [hb] at hb'</code> makes <code>hb' : true = false</code>; then <code>exact absurd hb' (by simp)</code>."
      ],
      "hint": "<code>induction h₁ generalizing s₂</code>, then in each case <code>cases h₂</code>. The <code>generalizing</code> is essential: without it, the induction hypothesis is stated only for the fixed <code>s₂</code> you started with, and the <code>seq</code> case fails.",
      "sol": "theorem exec_deterministic {c : Cmd} {s s₁ s₂ : State}\n    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by\n  induction h₁ generalizing s₂ with\n  | skip => cases h₂; rfl\n  | assign => cases h₂; rfl\n  | load hl => cases h₂ with | load hl' => rw [hl] at hl'; cases hl'; rfl\n  | write hl => cases h₂ with | write hl' => rfl\n  | free hl => cases h₂ with | free hl' => rfl\n  | seq _ _ ih₁ ih₂ =>\n      cases h₂ with\n      | seq h₁' h₂' => exact ih₂ (ih₁ h₁' ▸ h₂')\n  | iteTrue hb _ ih =>\n      cases h₂ with\n      | iteTrue hb' h' => exact ih h'\n      | iteFalse hb' h' => rw [hb] at hb'; exact absurd hb' (by simp)\n  | iteFalse hb _ ih =>\n      cases h₂ with\n      | iteTrue hb' h' => rw [hb] at hb'; exact absurd hb' (by simp)\n      | iteFalse hb' h' => exact ih h'\n  | loopFalse hb =>\n      cases h₂ with\n      | loopFalse hb' => rfl\n      | loopTrue hb' _ _ => rw [hb] at hb'; exact absurd hb' (by simp)\n  | loopTrue hb _ _ ihb ihr =>\n      cases h₂ with\n      | loopFalse hb' => rw [hb] at hb'; exact absurd hb' (by simp)\n      | loopTrue hb' hbody' hrest' => exact ihr (ihb hbody' ▸ hrest')",
      "expl": "Three shapes of case. (i) <b>Deterministic-by-construction</b> (<code>skip</code>, <code>assign</code>, <code>write</code>, <code>free</code>): inversion pins down the result, <code>rfl</code> closes it. (ii) <b>Value-carrying</b> (<code>load</code>): both derivations read the same location, so <code>rw [hl] at hl'</code> then <code>cases hl'</code> forces the two loaded values equal. (iii) <b>Compositional</b> (<code>seq</code>, <code>loopTrue</code>): use the first induction hypothesis to identify the intermediate states, rewrite with <code>▸</code>, and apply the second. The <code>ite</code>/<code>loop</code> mismatch cases are killed by <code>rw [hb] at hb'</code> — the guard cannot be both <code>true</code> and <code>false</code>.",
      "walk": [
        {
          "tac": "induction h₁ generalizing s₂ with",
          "h": "Ten goals, one per constructor of <code>Exec</code>. <code>generalizing s₂</code> reverts <code>s₂</code> (and <code>h₂</code>, which mentions it) into the goal before the induction runs, then re-introduces them in each case. Consequence: every induction hypothesis is universally quantified over its own final state."
        },
        {
          "tac": "| skip => cases h₂; rfl",
          "h": "In this case <code>h₂ : Exec .skip s s₂</code>, so inversion forces <code>s₂ = s</code> and the goal collapses to <code>s = s</code>. Exactly <code>exec_skip_inv</code>, inlined."
        },
        {
          "tac": "| assign => cases h₂; rfl",
          "h": "Same shape. The <code>assign</code> rule has no premises and a fully determined result state, so after inversion both sides of the goal are the literal expression <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code>."
        },
        {
          "tac": "| load hl => cases h₂ with | load hl' => rw [hl] at hl'; cases hl'; rfl",
          "h": "The only case with content among the atomic commands. <code>hl : s.heap l = some v</code> came from <code>h₁</code>; <code>hl' : s.heap l = some v'</code> from <code>h₂</code>. <code>rw [hl] at hl'</code> replaces the left-hand side of <code>hl'</code>, leaving <code>hl' : some v = some v'</code>; <code>cases hl'</code> uses injectivity of <code>some</code> to identify <code>v'</code> with <code>v</code>; <code>rfl</code> finishes."
        },
        {
          "tac": "| write hl => cases h₂ with | write hl' => rfl",
          "h": "No <code>rw</code> here, and that is the point: the <code>write</code> rule's premise binds <code>old</code>, which does not appear in the result. The two derivations may have found different old values; the resulting heaps are the same expression regardless, so <code>rfl</code> closes it. <code>hl'</code> is never used — <code>cases h₂ with | write =&gt; rfl</code>, with no binder at all, compiles just as well. The name is there for symmetry with the <code>load</code> line above."
        },
        {
          "tac": "| free hl => cases h₂ with | free hl' => rfl",
          "h": "Identical reasoning: <code>Heap.erase s.heap l</code> does not mention the value that was there."
        },
        {
          "tac": "| seq _ _ ih₁ ih₂ =>",
          "h": "The two underscores drop the sub-derivations themselves; you only need their induction hypotheses. Both are quantified over their own final state, courtesy of <code>generalizing</code>."
        },
        {
          "tac": "cases h₂ with",
          "h": "Invert the second derivation. Only <code>Exec.seq</code> can conclude <code>Exec (c₁ ;; c₂) s s₂</code>, so this produces one branch — but it also introduces a <i>fresh</i> intermediate state, which is the crux."
        },
        {
          "tac": "| seq h₁' h₂' => exact ih₂ (ih₁ h₁' ▸ h₂')",
          "h": "Read it inside-out. <code>ih₁ h₁' : s' = s'₂</code> equates the two intermediate states. <code>e ▸ h</code> rewrites the type of <code>h</code> along the equation <code>e</code>; so <code>ih₁ h₁' ▸ h₂'</code> takes <code>h₂' : Exec c₂ s'₂ s₂</code> and retypes it as <code>Exec c₂ s' s₂</code>. Now <code>ih₂</code> applies and gives <code>s'' = s₂</code>."
        },
        {
          "tac": "| iteTrue hb _ ih =>",
          "h": "Keep the guard evaluation <code>hb : b.eval s.store = true</code>; you need it to refute the mismatched branch."
        },
        {
          "tac": "cases h₂ with",
          "h": "Two constructors conclude <code>Exec (.ite b c₁ c₂) s s₂</code>, so this time you get two goals."
        },
        {
          "tac": "| iteTrue hb' h' => exact ih h'",
          "h": "Both derivations took the same branch. The induction hypothesis for that branch applies directly. <code>hb'</code> is unused."
        },
        {
          "tac": "| iteFalse hb' h' => rw [hb] at hb'; exact absurd hb' (by simp)",
          "h": "The impossible branch. <code>hb'</code> says the guard is <code>false</code>, <code>hb</code> says it is <code>true</code>. <code>rw [hb] at hb'</code> rewrites the occurrence of <code>b.eval s.store</code> inside <code>hb'</code>, producing <code>hb' : true = false</code>. <code>absurd hb' (by simp)</code> takes a proof and a proof of its negation and returns anything; <code>by simp</code> supplies <code>¬ (true = false)</code>."
        },
        {
          "tac": "| iteFalse hb _ ih =>",
          "h": "The mirror image. Same two branches, roles swapped."
        },
        {
          "tac": "cases h₂ with",
          "h": "Again two goals."
        },
        {
          "tac": "| iteTrue hb' h' => rw [hb] at hb'; exact absurd hb' (by simp)",
          "h": "Now <code>hb : … = false</code> and <code>hb' : … = true</code>, so the rewrite yields <code>false = true</code>. Note that <code>rw [hb] at hb'</code> is written the same way in both branches; the direction is decided by which hypothesis came from the induction."
        },
        {
          "tac": "| iteFalse hb' h' => exact ih h'",
          "h": "Matching branches; induction hypothesis applies."
        },
        {
          "tac": "| loopFalse hb =>",
          "h": "The loop exited immediately, so the result state is <code>s</code> itself and there is no induction hypothesis."
        },
        {
          "tac": "cases h₂ with",
          "h": "Two loop constructors, two goals."
        },
        {
          "tac": "| loopFalse hb' => rfl",
          "h": "Both exited. Both final states are <code>s</code>."
        },
        {
          "tac": "| loopTrue hb' _ _ => rw [hb] at hb'; exact absurd hb' (by simp)",
          "h": "One exited and one entered the body: guard clash again. The two dropped arguments are the body derivation and the rest-of-loop derivation, neither of which is needed."
        },
        {
          "tac": "| loopTrue hb _ _ ihb ihr =>",
          "h": "Five arguments: guard, body derivation, rest derivation, then <i>two</i> induction hypotheses — <code>ihb</code> for the body and <code>ihr</code> for the remainder of the loop. Note that <code>ihr</code> exists precisely because <code>hrest</code> is a recursive premise even though its command is unchanged."
        },
        {
          "tac": "cases h₂ with",
          "h": "Two goals again."
        },
        {
          "tac": "| loopFalse hb' => rw [hb] at hb'; exact absurd hb' (by simp)",
          "h": "Guard clash, fourth and last time."
        },
        {
          "tac": "| loopTrue hb' hbody' hrest' => exact ihr (ihb hbody' ▸ hrest')",
          "h": "Structurally identical to the <code>seq</code> case: <code>ihb hbody'</code> identifies the states after one iteration, <code>▸</code> transports the remaining derivation along that equation, and <code>ihr</code> finishes. Sequencing and looping have the same proof because <code>loopTrue</code> <i>is</i> a sequencing rule."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "The load case — where the two derivations actually have to be reconciled",
          "start": "case load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝ : Val\nhl : s✝.heap l✝ = some v✝\ns₂ : State\nh₂ : Exec (Cmd.load x✝ l✝) s✝ s₂\n⊢ { store := s✝.store.set x✝ v✝, heap := s✝.heap } = s₂",
          "steps": [
            {
              "tac": "cases h₂ with | load hl' =>",
              "state": "case load.load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝¹ : Val\nhl : s✝.heap l✝ = some v✝¹\nv✝ : Val\nhl' : s✝.heap l✝ = some v✝\n⊢ { store := s✝.store.set x✝ v✝¹, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }",
              "h": "Two loaded values now, distinguished only by the superscript dagger: <code>v✝¹</code> from <code>h₁</code> and <code>v✝</code> from <code>h₂</code>. The goal is an equation between two <code>State</code> literals that differ in exactly one place. Note that Lean prints <code>s✝.store.set x✝ v✝¹</code> where the declaration says <code>Store.set s.store x v</code>."
            },
            {
              "tac": "rw [hl] at hl'",
              "state": "case load.load\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝¹ : Val\nhl : s✝.heap l✝ = some v✝¹\nv✝ : Val\nhl' : some v✝¹ = some v✝\n⊢ { store := s✝.store.set x✝ v✝¹, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }",
              "h": "The rewrite fires inside <code>hl'</code>, replacing its left-hand side <code>s✝.heap l✝</code> by <code>some v✝¹</code>. This is the moment the two derivations are forced to agree: they read the same cell of the same heap."
            },
            {
              "tac": "cases hl'",
              "state": "case load.load.refl\nc : Cmd\ns s₁ s✝ : State\nx✝ : Var\nl✝ : Loc\nv✝ : Val\nhl : s✝.heap l✝ = some v✝\n⊢ { store := s✝.store.set x✝ v✝, heap := s✝.heap } = { store := s✝.store.set x✝ v✝, heap := s✝.heap }",
              "h": "<code>hl'</code> is an equation between two applications of the same constructor, so <code>cases</code> applies injectivity: one value variable disappears and the other is used everywhere. Both sides of the goal are now the same expression. (The case tag <code>refl</code> is <code>Eq</code>'s only constructor.)"
            },
            {
              "tac": "rfl",
              "state": "No goals.",
              "h": ""
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "The seq case — what <code>generalizing</code> bought you",
          "start": "case seq\nc : Cmd\ns s₁ s✝ s'✝ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝\nh₂✝ : Exec c₂✝ s'✝ s''✝\nih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s'✝ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s'✝ s₂ → s''✝ = s₂\ns₂ : State\nh₂ : Exec (c₁✝ ;; c₂✝) s✝ s₂\n⊢ s''✝ = s₂",
          "steps": [
            {
              "tac": "cases h₂ with | seq h₁' h₂' =>",
              "state": "case seq.seq\nc : Cmd\ns s₁ s✝ s'✝¹ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝¹\nh₂✝ : Exec c₂✝ s'✝¹ s''✝\nih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s'✝¹ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s'✝¹ s₂ → s''✝ = s₂\ns₂ s'✝ : State\nh₁' : Exec c₁✝ s✝ s'✝\nh₂' : Exec c₂✝ s'✝ s₂\n⊢ s''✝ = s₂",
              "h": "There are now <b>two</b> intermediate states in the context: <code>s'✝¹</code> from the derivation you inducted on, and the fresh <code>s'✝</code> that inversion of <code>h₂</code> produced. Nothing yet says they are equal. That is exactly the obligation the proof discharges next."
            },
            {
              "tac": "exact ih₂ (ih₁ h₁' ▸ h₂')",
              "state": "No goals.",
              "h": "<code>ih₁ h₁'</code> is applied at the fresh state — legal only because <code>ih₁</code> is quantified — and proves <code>s'✝¹ = s'✝</code>. <code>▸</code> rewrites <code>h₂' : Exec c₂✝ s'✝ s₂</code> backwards along it to <code>Exec c₂✝ s'✝¹ s₂</code>, which is what <code>ih₂</code> consumes."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "Without <code>generalizing s₂</code>",
            "kind": "bad",
            "h": [
              {
                "t": "p",
                "h": "The <code>seq</code> case looks like this. <code>ih₁</code> is stated <b>only</b> for the one <code>s₂</code> you started with — but the state you need to identify is the intermediate one produced by inverting <code>h₂</code>. There is no way to apply <code>ih₁</code>, and the case is unprovable as it stands."
              },
              {
                "t": "state",
                "src": "case seq\nc : Cmd\ns s₁ s₂ s✝ s'✝ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝\nh₂✝ : Exec c₂✝ s'✝ s''✝\nih₁ : Exec c₁✝ s✝ s₂ → s'✝ = s₂\nih₂ : Exec c₂✝ s'✝ s₂ → s''✝ = s₂\nh₂ : Exec (c₁✝ ;; c₂✝) s✝ s₂\n⊢ s''✝ = s₂"
              }
            ]
          },
          "right": {
            "t": "With <code>generalizing s₂</code>",
            "kind": "good",
            "h": [
              {
                "t": "p",
                "h": "<code>s₂</code> is reverted into the goal before the induction and re-introduced afterwards, so the hypotheses quantify over it. This is the standard fix whenever an induction hypothesis has to be used at a different instance than the one sitting in the goal."
              },
              {
                "t": "state",
                "src": "ih₁ : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s'✝ = s₂\nih₂ : ∀ {s₂ : State}, Exec c₂✝ s'✝ s₂ → s''✝ = s₂"
              }
            ]
          }
        },
        {
          "t": "trace",
          "title": "A guard clash, in full",
          "start": "case iteTrue.iteFalse\nc : Cmd\ns s₁ s✝ s'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ : Exec c₁✝ s✝ s'✝\nih : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s'✝ = s₂\ns₂ : State\nhb' : BExpr.eval s✝.store b✝ = false\nh' : Exec c₂✝ s✝ s₂\n⊢ s'✝ = s₂",
          "steps": [
            {
              "tac": "rw [hb] at hb'",
              "state": "case iteTrue.iteFalse\nc : Cmd\ns s₁ s✝ s'✝ : State\nb✝ : BExpr\nc₁✝ c₂✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nh✝ : Exec c₁✝ s✝ s'✝\nih : ∀ {s₂ : State}, Exec c₁✝ s✝ s₂ → s'✝ = s₂\ns₂ : State\nhb' : true = false\nh' : Exec c₂✝ s✝ s₂\n⊢ s'✝ = s₂",
              "h": "The context is now inconsistent and the goal is irrelevant. Note the printer again: the source says <code>b.eval s.store</code>, the display says <code>BExpr.eval s✝.store b✝</code>."
            },
            {
              "tac": "exact absurd hb' (by simp)",
              "state": "No goals.",
              "h": "<code>absurd : a → ¬a → b</code>. The <code>by simp</code> proves <code>¬ (true = false)</code>, which holds because <code>true</code> and <code>false</code> are distinct constructors of <code>Bool</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "What <code>▸</code> actually is",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "<code>▸</code> is notation for transport along an equality — at bottom, <code>Eq.mpr</code> together with the eliminator for <code>Eq</code>. Given <code>e : a = b</code> and a term <code>h</code> whose type mentions <code>b</code>, <code>e ▸ h</code> is a term of the type with <code>a</code> in place of <code>b</code> (or the other way round; Lean picks the direction that makes the elaboration succeed, which is why it can feel unpredictable)."
            },
            {
              "t": "p",
              "h": "If <code>▸</code> refuses to elaborate, the mechanical alternative is to name the equation and rewrite explicitly. The following is equivalent to the <code>seq</code> line and sometimes easier to debug:"
            },
            {
              "t": "code",
              "src": "-- the seq case, written out\n| seq _ _ ih₁ ih₂ =>\n    cases h₂ with\n    | seq h₁' h₂' =>\n        have heq := ih₁ h₁'      -- s' = s'₂\n        subst heq                -- replace s'₂ by s' everywhere\n        exact ih₂ h₂'",
              "tag": "sketch",
              "cap": "A more verbose form of the same step. Not the corpus proof — shown only to say what <code>▸</code> is doing."
            }
          ]
        }
      ],
      "pitfall": "Forgetting <code>generalizing s₂</code> and then trying to repair the <code>seq</code> case. It cannot be repaired locally: the induction hypothesis you were handed is simply the wrong statement, and no amount of <code>rw</code> will turn a hypothesis about one particular <code>s₂</code> into one about the intermediate state. The other frequent error is writing <code>| load hl hl' => …</code> as if <code>cases h₂</code> and the constructor pattern shared a name list. They do not: the outer <code>induction</code> pattern names only <i>this</i> constructor's arguments, so Lean answers <i>Too many variable names provided at alternative `load`: 2 provided, but 1 expected</i>. That is why the solution writes <code>cases h₂ with | load hl' => …</code> as its own nested block.",
      "variants": "Delete <code>hb</code> from <code>Exec.iteTrue</code> — i.e. let the <code>ite</code> rules fire regardless of the guard — and the language becomes nondeterministic: <code>if b then skip else free l</code> would have two derivations from the same state. Determinism fails at exactly the four cross-cases, which is why those four lines are the ones that mention the guard. Similarly, if <code>Exec.load</code> did not carry <code>hl</code> but instead said “<code>x</code> gets some value”, the <code>load</code> case would break at <code>rw [hl] at hl'</code> and the theorem would be false. Every line of this proof that is not <code>rfl</code> is pointing at a place where determinism could have failed."
    },

    {
      "t": "sec",
      "s": "Exercises · an executable interpreter"
    },
    {
      "t": "p",
      "h": "A relational semantics is good for proofs and useless for testing. Write an interpreter and prove the two agree. Because the language has loops, the interpreter must be structurally terminating, which means <b>fuel</b>: a natural number bounding the recursion depth."
    },
    {
      "t": "p",
      "h": "It is worth seeing the failure before the fix. Here is the naive interpreter, and here is exactly what Lean says about it."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Rejected: recurse on the command",
        "h": "Every clause but one is structural. The <code>loop</code> clause is not: <code>runBad (.loop b c) s'</code> calls itself at the <i>same</i> command. Lean tries structural recursion on each argument in turn, fails, falls back to well-founded recursion, and leaves you a goal of <code>False</code>.",
        "kind": "bad",
        "tag": "sketch",
        "src": "def runBad : Cmd → State → Option State\n  | .skip, s => some s\n  | .loop b c, s =>\n      match b.eval s.store with\n      | true  =>\n          match runBad c s with\n          | some s' => runBad (.loop b c) s'\n          | none    => none\n      | false => some s\n  | _, _ => none\n\n-- error: fail to show termination for runBad\n-- failed to infer structural recursion:\n-- Cannot use parameter #1:\n--   failed to eliminate recursive application\n--     runBad (Cmd.loop b c) s'\n-- Cannot use parameter #2:\n--   the type State does not have a `.brecOn` recursor"
      },
      "right": {
        "t": "Chosen: recurse on a fuel counter",
        "h": "Add a <code>Nat</code> in front and hand every recursive call <code>n</code> where the caller had <code>n + 1</code>. Now the first argument strictly decreases in every recursive call, whatever the command does, and Lean accepts the definition without any termination proof at all.",
        "kind": "good",
        "tag": "sketch",
        "src": "def run : Nat → Cmd → State → Option State\n  | 0, _, _ => none\n  | n + 1, .loop b c, s => -- every recursive call gets n\n      ..."
      }
    },
    {
      "t": "p",
      "h": "The price is that <code>run</code> is not the semantics: <code>run n c s = none</code> can mean the program faulted, or that it would diverge, or merely that <code>n</code> was too small. The interpreter therefore proves nothing negative, and the soundness theorem below is one-directional for that reason. Completeness — for every real execution <i>some</i> fuel suffices — is the other exercise."
    },
    {
      "t": "anat",
      "src": "def run : Nat → Cmd → State → Option State\n  | 0,     _,            _ => none\n  | _ + 1, .skip,        s => some s\n  | _ + 1, .assign x e,  s => some ⟨Store.set s.store x (e.eval s.store), s.heap⟩\n  | _ + 1, .load x l,    s =>\n      match s.heap l with\n      | some v => some ⟨Store.set s.store x v, s.heap⟩\n      | none   => none\n  | _ + 1, .write l e,   s =>\n      match s.heap l with\n      | some _ => some ⟨s.store, Heap.write s.heap l (e.eval s.store)⟩\n      | none   => none\n  | _ + 1, .free l,      s =>\n      match s.heap l with\n      | some _ => some ⟨s.store, Heap.erase s.heap l⟩\n      | none   => none\n  | n + 1, .seq c₁ c₂,   s =>\n      match run n c₁ s with\n      | some s' => run n c₂ s'\n      | none    => none\n  | n + 1, .ite b c₁ c₂, s =>\n      match b.eval s.store with\n      | true  => run n c₁ s\n      | false => run n c₂ s\n  | n + 1, .loop b c,   s =>\n      match b.eval s.store with\n      | true  =>\n          match run n c s with\n          | some s' => run n (.loop b c) s'\n          | none    => none\n      | false => some s",
      "cap": "Six callouts on the clauses that decide how the two proofs below go.",
      "parts": [
        {
          "m": "| 0,     _,            _ => none",
          "h": "Out of fuel. This clause is why <code>run</code> is total, and it is also the entire content of the <code>zero</code> case of both soundness and monotonicity: <code>h : run 0 c s = some s'</code> is refuted by <code>simp [run]</code>, because <code>none = some s'</code> is false."
        },
        {
          "m": "| _ + 1, .skip,        s => some s",
          "h": "The fuel is matched but not named — the atomic commands never recurse, so the remaining fuel is irrelevant. It is still matched as <code>_ + 1</code> and not as a bare <code>n</code>, so that this clause and the <code>0</code> clause split <code>Nat</code> between them with no overlap; the equation lemma that <code>simp [run]</code> then uses for this clause applies at any successor. Note the consequence for the proofs: at fuel <code>n + 1</code> and at fuel <code>n + 2</code> the atomic clauses unfold to <i>the same term</i>, which is why every atomic case of <code>run_mono</code> is one word long."
        },
        {
          "m": "match s.heap l with",
          "h": "The fault check, mirroring the premise <code>hl</code> of <code>Exec.load</code>. Because the result is an <code>Option</code>, the failure is a value here, whereas in the relation it was the absence of a rule. The soundness proof is precisely the translation between those two encodings."
        },
        {
          "m": "| n + 1, .seq c₁ c₂,   s =>",
          "h": "Here the fuel <i>is</i> named, because it is passed on. Both halves get <code>n</code> — not <code>n</code> split between them. Fuel is a depth bound, not a step count, which is why <code>run_complete</code> can take <code>max n₁ n₂ + 1</code> instead of a sum."
        },
        {
          "m": "match b.eval s.store with",
          "h": "The guard is a <code>Bool</code>, so this is an ordinary two-way match, not an <code>if</code>. This is what makes the branching cases of <code>run_sound</code> one line each: after you rewrite the scrutinee to the literal <code>true</code>, the whole <code>match</code> reduces by iota to its first branch <i>definitionally</i>, so <code>exact</code> accepts it with no further tactic and nothing to look up. Writing it with <code>if b.eval s.store = true then …</code> would also work here — see the comparison in <code>run_sound</code>'s <i>Why it works</i> panel — but only because <code>Bool</code>'s decidable equality happens to compute. The <code>match</code> depends on no instance at all."
        },
        {
          "m": "run n (.loop b c) s'",
          "h": "The same command with one less fuel — the call that <code>runBad</code> could not make. Note the asymmetry with <code>Exec.loopTrue</code>: there the recursive premise is at the same command <i>and</i> that is fine, because the derivation tree is what shrinks. Here nothing shrinks except the number you brought with you."
        }
      ]
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Adding <code>run</code> to a simp set",
      "h": "<code>simp [run]</code> and <code>simp only [run]</code> use the <b>equation lemmas</b> Lean generated from the clauses above — one per clause, each of the form <code>run (n+1) (.seq c₁ c₂) s = match run n c₁ s with …</code>. <code>simp only [run]</code> rewrites with those and nothing else, which is what you want when the goal is delicate; plain <code>simp [run]</code> adds the whole default simp set on top, which is what you want when you are trying to derive a contradiction from <code>none = some s'</code> or to strip a <code>some</code> off both sides. Both appear in the proofs below. In one place the choice is forced — see the aside inside <code>run_sound</code> — and elsewhere it is a matter of keeping the hypothesis you are about to rewrite into predictable."
    },
    {
      "t": "ex",
      "id": "m5-3",
      "name": "run_sound",
      "hard": true,
      "why": "Everything the interpreter accepts is a genuine execution. In other words the interpreter never lies. Concretely: once this is proved you can <code>#eval</code> a program, and if it produces a state you know that state is reachable — so a bad definition of <code>Exec</code> shows up as a wrong number on your screen instead of as an afternoon spent proving something false.",
      "setup": "Induct on the fuel, not on the command. The command is then destructed inside each case, and the induction hypothesis <code>ih</code> is available at fuel <code>n</code> for <i>every</i> command — which is what the <code>seq</code> and <code>loop</code> cases need.",
      "goal": "theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s' : State),\n    run n c s = some s' → Exec c s s'",
      "hints": [
        "The statement is a <code>∀</code> over four things. Introduce only the fuel, then induct: <code>intro n; induction n with …</code>. Leaving <code>c</code>, <code>s</code>, <code>s'</code> inside the goal is what makes the induction hypothesis usable at other commands and states.",
        "<code>induction n</code>, then <code>cases c</code>. The <code>zero</code> case is one tactic: <code>run 0 c s</code> is <code>none</code>, so the hypothesis is absurd.",
        "For the branching commands use <code>cases hb : b.eval s.store</code> and then <code>rw [hb] at h</code> — the <code>cases … :</code> form records the equation in the goal but not in <code>h</code>, so you must transport it yourself.",
        "After <code>rw [hb] at h</code> the hypothesis <i>displays</i> as <code>(match true with | true => run n c₁ s | false => …) = some s'</code>. Do not try to simplify it. That term is definitionally <code>run n c₁ s = some s'</code>, so <code>exact .iteTrue hb (ih c₁ s s' h)</code> typechecks as written."
      ],
      "hint": "<code>induction n</code>, then <code>cases c</code>. For the branching commands use <code>cases hb : b.eval s.store</code> and then <code>rw [hb] at h</code> — the <code>cases … :</code> form records the equation in the goal but not in <code>h</code>, so you must transport it yourself.",
      "sol": "theorem run_sound : ∀ (n : Nat) (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s' := by\n  intro n\n  induction n with\n  | zero => intro c s s' h; simp [run] at h\n  | succ n ih =>\n    intro c s s' h\n    cases c with\n    | skip => simp [run] at h; rw [← h]; exact .skip\n    | assign x e => simp [run] at h; rw [← h]; exact .assign\n    | load x l =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl\n    | write l e =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl\n    | free l =>\n        simp only [run] at h\n        cases hl : s.heap l with\n        | none   => rw [hl] at h; simp at h\n        | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl\n    | seq c₁ c₂ =>\n        simp only [run] at h\n        cases hr : run n c₁ s with\n        | none    => rw [hr] at h; simp at h\n        | some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s' h)\n    | ite b c₁ c₂ =>\n        simp only [run] at h\n        cases hb : b.eval s.store with\n        | true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s' h)\n        | false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s' h)\n    | loop b c =>\n        simp only [run] at h\n        cases hb : b.eval s.store with\n        | false =>\n            rw [hb] at h\n            have hs : s = s' := Option.some.inj h\n            subst hs\n            exact .loopFalse hb\n        | true  =>\n            rw [hb] at h\n            cases hr : run n c s with\n            | none    => rw [hr] at h; simp at h\n            | some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s' h)",
      "expl": "The one subtlety is definitional reduction. After <code>rw [hb] at h</code> the hypothesis reads <code>(match true with | true => run n c₁ s | false => …) = some s'</code>, which is <i>definitionally</i> <code>run n c₁ s = some s'</code>. <code>exact</code> checks up to definitional equality, so it goes through without further simplification. Defining <code>run</code>’s branches with <code>match … with | true | false</code> rather than <code>if</code> is what makes this pleasant — the iota reduction fires immediately. (The <code>if</code> spelling reduces here too, as it happens, because <code>Bool</code>'s decidable equality computes; what <code>match</code> buys you is that nothing in the chain <i>can</i> fail to reduce. The comparison is spelled out below.)",
      "walk": [
        {
          "tac": "intro n",
          "h": "Introduce only the fuel. The goal becomes <code>∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'</code>, so the induction hypothesis will be that whole statement at <code>n</code> — universally quantified over command and states, which is what the compound cases need."
        },
        {
          "tac": "induction n with",
          "h": "Two goals, <code>zero</code> and <code>succ</code>. This is induction on a <code>Nat</code>, not on a derivation; the recursor is <code>Nat.rec</code>."
        },
        {
          "tac": "| zero => intro c s s' h; simp [run] at h",
          "h": "With no fuel, <code>run 0 c s</code> reduces to <code>none</code> by the first clause. So <code>h : none = some s'</code>. <code>simp [run] at h</code> unfolds and then uses the default simp set to see that two distinct <code>Option</code> constructors cannot be equal; when <code>simp … at h</code> reduces a hypothesis to <code>False</code> it closes the goal outright."
        },
        {
          "tac": "| succ n ih =>",
          "h": "<code>ih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'</code>. Note that it is stated at fuel <code>n</code> for every command — you will apply it to sub-commands and, in the loop case, to the same command."
        },
        {
          "tac": "intro c s s' h",
          "h": "Now introduce the rest. <code>h : run (n + 1) c s = some s'</code>."
        },
        {
          "tac": "cases c with",
          "h": "Eight goals, one per constructor of <code>Cmd</code>. This is where the fuel-vs-command split pays off: because <code>c</code> was introduced <i>after</i> the induction, <code>ih</code> is not tied to it."
        },
        {
          "tac": "| skip => simp [run] at h; rw [← h]; exact .skip",
          "h": "<code>simp [run] at h</code> turns <code>h : run (n+1) .skip s = some s'</code> into <code>h : s = s'</code> — it unfolds to <code>some s = some s'</code> and then strips the constructor. <code>rw [← h]</code> rewrites <code>s'</code> to <code>s</code> in the goal, giving <code>Exec Cmd.skip s s</code>, which is exactly what <code>Exec.skip</code> concludes. The leading dot in <code>.skip</code> resolves against the expected type <code>Exec …</code>."
        },
        {
          "tac": "| assign x e => simp [run] at h; rw [← h]; exact .assign",
          "h": "Same three moves. Here <code>h</code> becomes an equation between <code>s'</code> and the literal state <code>⟨Store.set s.store x (e.eval s.store), s.heap⟩</code>, and <code>Exec.assign</code> concludes at precisely that state."
        },
        {
          "tac": "| load x l =>",
          "h": "The first case with a fault check."
        },
        {
          "tac": "simp only [run] at h",
          "h": "Unfold <code>run</code> and nothing else. <code>h</code> now displays as the unreduced <code>match s.heap l with …</code>: no rewrite can reduce a match whose scrutinee is an opaque application, and the default simp set has no lemma about this one either — plain <code>simp [run] at h</code> leaves <code>h</code> in exactly the same shape. So the choice of <code>simp only</code> here is hygiene, not necessity: it names the single equation you want to fire, which is what keeps the hypothesis you are about to <code>rw</code> into predictable."
        },
        {
          "tac": "cases hl : s.heap l with",
          "h": "Split on whether the cell exists, <i>recording</i> the equation as <code>hl</code>. This form was introduced in M0; the thing to remember is that it substitutes into the goal but not into hypotheses."
        },
        {
          "tac": "| none   => rw [hl] at h; simp at h",
          "h": "Transport the equation into <code>h</code> by hand — that is the step the <code>cases … :</code> form does not do for you. Then <code>h</code> is <code>none = some s'</code> and <code>simp at h</code> closes the goal."
        },
        {
          "tac": "| some v => rw [hl] at h; simp at h; rw [← h]; exact .load hl",
          "h": "After the rewrite the match reduces, and <code>simp at h</code> strips the <code>some</code>, leaving <code>h : ⟨Store.set s.store x v, s.heap⟩ = s'</code>. <code>rw [← h]</code> puts that literal state into the goal and <code>Exec.load hl</code> supplies the derivation — <code>hl</code> is exactly the premise the constructor demands."
        },
        {
          "tac": "| write l e =>\n    simp only [run] at h\n    cases hl : s.heap l with\n    | none   => rw [hl] at h; simp at h\n    | some v => rw [hl] at h; simp at h; rw [← h]; exact .write hl",
          "h": "Character-for-character the <code>load</code> argument with <code>.write</code> in place of <code>.load</code>. The bound value <code>v</code> is used only to instantiate <code>hl</code>, which is what <code>Exec.write</code>'s <code>old</code> premise wants."
        },
        {
          "tac": "| free l =>\n    simp only [run] at h\n    cases hl : s.heap l with\n    | none   => rw [hl] at h; simp at h\n    | some v => rw [hl] at h; simp at h; rw [← h]; exact .free hl",
          "h": "And again. Three commands, one argument — which is the sign that the fault check belongs in one place. It does: in M7 all three get the same small-footprint precondition."
        },
        {
          "tac": "| seq c₁ c₂ =>",
          "h": "The first compound case."
        },
        {
          "tac": "simp only [run] at h",
          "h": "<code>h</code> becomes <code>(match run n c₁ s with | some s' => run n c₂ s' | none => none) = some s'</code>. The scrutinee is now a recursive call, not a heap lookup."
        },
        {
          "tac": "cases hr : run n c₁ s with",
          "h": "Split on whether the first half succeeded, recording the equation as <code>hr</code>. Note that <code>hr</code> is exactly the shape <code>ih</code> consumes."
        },
        {
          "tac": "| none    => rw [hr] at h; simp at h",
          "h": "If the first half returned <code>none</code> the whole thing did, contradicting <code>h</code>."
        },
        {
          "tac": "| some s₁ => rw [hr] at h; exact .seq (ih c₁ s s₁ hr) (ih c₂ s₁ s' h)",
          "h": "After <code>rw [hr] at h</code>, <code>h</code> displays as <code>(match some s₁ with …) = some s'</code>, which is <i>definitionally</i> <code>run n c₂ s₁ = some s'</code>. So <code>ih c₂ s₁ s' h</code> typechecks with no further tactic, and <code>ih c₁ s s₁ hr</code> handles the first half. <code>Exec.seq</code> glues them, choosing <code>s₁</code> as the intermediate state."
        },
        {
          "tac": "| ite b c₁ c₂ =>",
          "h": "The branching case."
        },
        {
          "tac": "simp only [run] at h",
          "h": "<code>h : (match BExpr.eval s.store b with | true => run n c₁ s | false => run n c₂ s) = some s'</code>."
        },
        {
          "tac": "cases hb : b.eval s.store with",
          "h": "Split on the guard. Two goals, tagged <code>true</code> and <code>false</code> — these are <code>Bool</code>'s constructors, not <code>pos</code>/<code>neg</code>, because you are casing on a <code>Bool</code> rather than on a decidable proposition."
        },
        {
          "tac": "| true  => rw [hb] at h; exact .iteTrue hb (ih c₁ s s' h)",
          "h": "The whole exercise in one line. <code>rw [hb] at h</code> makes the scrutinee the literal <code>true</code>; the match then reduces by iota, definitionally, so <code>h</code> <i>is</i> <code>run n c₁ s = some s'</code> even though it does not print that way. <code>hb</code> doubles as the premise of <code>Exec.iteTrue</code>."
        },
        {
          "tac": "| false => rw [hb] at h; exact .iteFalse hb (ih c₂ s s' h)",
          "h": "Mirror image."
        },
        {
          "tac": "| loop b c =>",
          "h": "The last and only genuinely new case."
        },
        {
          "tac": "simp only [run] at h",
          "h": "A nested match: guard on the outside, result of the body on the inside."
        },
        {
          "tac": "cases hb : b.eval s.store with",
          "h": "Split on the guard. The solution takes <code>false</code> first because it is the base case of the loop."
        },
        {
          "tac": "| false =>\n    rw [hb] at h",
          "h": "The outer match reduces to <code>some s</code>, so <code>h</code> is definitionally <code>some s = some s'</code>."
        },
        {
          "tac": "have hs : s = s' := Option.some.inj h",
          "h": "<code>Option.some.inj</code> is the injectivity lemma Lean generates for the constructor <code>some</code>; its type is <code>some a = some b → a = b</code>. It is applied to <code>h</code> directly — again, no simplification needed, because <code>h</code>'s type reduces to <code>some s = some s'</code>. You met it in M1 and used it in M3's <code>pointsTo_value_unique</code>."
        },
        {
          "tac": "subst hs",
          "h": "Replace <code>s'</code> by <code>s</code> throughout. The goal becomes <code>Exec (Cmd.loop b c) s s</code>."
        },
        {
          "tac": "exact .loopFalse hb",
          "h": "Exactly the shape of <code>Exec.loopFalse</code>, whose premise is the false guard."
        },
        {
          "tac": "| true  =>\n    rw [hb] at h",
          "h": "The outer match reduces into the inner one, so <code>h</code> is now about <code>run n c s</code> — the body."
        },
        {
          "tac": "cases hr : run n c s with",
          "h": "Split on whether the body succeeded, recording <code>hr</code>."
        },
        {
          "tac": "| none    => rw [hr] at h; simp at h",
          "h": "Body failed, so the loop returned <code>none</code>; contradiction."
        },
        {
          "tac": "| some s₁ => rw [hr] at h; exact .loopTrue hb (ih c s s₁ hr) (ih _ s₁ s' h)",
          "h": "<code>ih c s s₁ hr</code> is the body's execution. <code>ih _ s₁ s' h</code> is the rest of the loop — note the <code>_</code>: the command is <code>.loop b c</code>, and Lean infers it from <code>h</code>. This is the one place where <code>ih</code> is applied at the <i>same</i> command it was called with, and it is legal because the fuel went down."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "The skeleton: what induction on fuel gives you",
          "start": "⊢ ∀ (n : Nat) (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'",
          "steps": [
            {
              "tac": "intro n",
              "state": "n : Nat\n⊢ ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'",
              "h": "Only the fuel is introduced. Everything else stays under the binder, which is what makes the induction hypothesis general."
            },
            {
              "tac": "induction n with | zero => intro c s s' h",
              "state": "case zero\nc : Cmd\ns s' : State\nh : run 0 c s = some s'\n⊢ Exec c s s'",
              "h": "<code>run 0 c s</code> is <code>none</code> by the first clause, for any <code>c</code> and <code>s</code>. So <code>h</code> is absurd and <code>simp [run] at h</code> ends the case."
            },
            {
              "tac": "| succ n ih => intro c s s' h",
              "state": "case succ\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\nc : Cmd\ns s' : State\nh : run (n + 1) c s = some s'\n⊢ Exec c s s'",
              "h": "There is the hypothesis you wanted: quantified over command and both states. <code>cases c</code> now splits the goal eight ways with <code>ih</code> untouched in every branch."
            }
          ],
          "done": "eight goals, one per Cmd constructor"
        },
        {
          "t": "trace",
          "title": "The load case — simp only, then transport the equation by hand",
          "start": "case succ.load\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nx : Var\nl : Loc\nh : run (n + 1) (Cmd.load x l) s = some s'\n⊢ Exec (Cmd.load x l) s s'",
          "steps": [
            {
              "tac": "simp only [run] at h",
              "state": "case succ.load\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nx : Var\nl : Loc\nh :\n  (match s.heap l with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s'\n⊢ Exec (Cmd.load x l) s s'",
              "h": "The equation lemma for the <code>load</code> clause fired. The fuel has disappeared from <code>h</code> entirely — atomic commands do not use it — and what remains is a stuck <code>match</code>."
            },
            {
              "tac": "cases hl : s.heap l with | some v => (before rw)",
              "state": "case succ.load.some\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nx : Var\nl : Loc\nh :\n  (match s.heap l with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s'\nv : Val\nhl : s.heap l = some v\n⊢ Exec (Cmd.load x l) s s'",
              "h": "<b>Look at <code>h</code>.</b> It still says <code>match s.heap l</code>. The <code>cases hl :</code> form substituted into the goal and gave you the equation <code>hl</code>, but it left the hypotheses alone. That is why the next tactic exists."
            },
            {
              "tac": "rw [hl] at h",
              "state": "case succ.load.some\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nx : Var\nl : Loc\nv : Val\nh :\n  (match some v with\n    | some v => some { store := s.store.set x v, heap := s.heap }\n    | none => none) =\n    some s'\nhl : s.heap l = some v\n⊢ Exec (Cmd.load x l) s s'",
              "h": "Now the scrutinee is a literal constructor application. The match is definitionally reduced, though the printer still shows it unreduced."
            },
            {
              "tac": "simp at h",
              "state": "case succ.load.some\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nx : Var\nl : Loc\nv : Val\nhl : s.heap l = some v\nh : { store := s.store.set x v, heap := s.heap } = s'\n⊢ Exec (Cmd.load x l) s s'",
              "h": "<code>simp</code> performs the iota reduction and strips the outer <code>some</code> from both sides. Note that <code>simp</code> also moved <code>h</code> to the end of the context — a cosmetic effect of rebuilding the hypothesis, but one that surprises people reading diffs."
            },
            {
              "tac": "rw [← h]; exact .load hl",
              "state": "No goals.",
              "h": "<code>rw [← h]</code> replaces <code>s'</code> in the goal by the explicit state, which is exactly <code>Exec.load</code>'s conclusion; <code>hl</code> is its premise."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "The ite case — the definitional-equality trick, isolated",
          "start": "case succ.ite\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nb : BExpr\nc₁ c₂ : Cmd\nh :\n  (match BExpr.eval s.store b with\n    | true => run n c₁ s\n    | false => run n c₂ s) =\n    some s'\n⊢ Exec (Cmd.ite b c₁ c₂) s s'",
          "steps": [
            {
              "tac": "cases hb : b.eval s.store with | true => rw [hb] at h",
              "state": "case succ.ite.true\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nb : BExpr\nc₁ c₂ : Cmd\nh :\n  (match true with\n    | true => run n c₁ s\n    | false => run n c₂ s) =\n    some s'\nhb : BExpr.eval s.store b = true\n⊢ Exec (Cmd.ite b c₁ c₂) s s'",
              "h": "This is the state worth memorising. <code>h</code> <i>prints</i> as a match on the literal <code>true</code>. It <i>is</i> <code>run n c₁ s = some s'</code> — the two terms are definitionally equal by iota reduction, and Lean's kernel does not care which one you show it."
            },
            {
              "tac": "exact .iteTrue hb (ih c₁ s s' h)",
              "state": "No goals.",
              "h": "<code>ih c₁ s s' h</code> demands an argument of type <code>run n c₁ s = some s'</code>. <code>h</code> has a type that <i>reduces</i> to that, and <code>exact</code> checks up to definitional equality, so it is accepted. No <code>simp</code>, no <code>show</code>, no <code>change</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "If <code>run</code> used <code>if</code>",
            "h": [
              {
                "t": "p",
                "h": "<code>if b.eval s.store = true then run n c₁ s else run n c₂ s</code>. Write the interpreter that way and this case of the proof goes through <b>unchanged</b> — worth knowing, because the <code>if</code> form usually gets described as a disaster. Below is the real hypothesis after <code>rw [hb] at h</code>, from a copy of the interpreter named <code>runIf</code> (the name <code>run</code> is taken; nothing else differs):"
              },
              {
                "t": "state",
                "src": "h : (if true = true then runIf n c₁ s else runIf n c₂ s) = some s'\nhb : BExpr.eval s.store b = true\n⊢ Exec (Cmd.ite b c₁ c₂) s s'"
              },
              {
                "t": "p",
                "h": "and <code>exact .iteTrue hb (ih c₁ s s' h)</code> still typechecks: <code>Bool</code>'s decidable-equality instance computes on two literal constructors, so <code>if true = true then A else B</code> reduces to <code>A</code> on its own."
              }
            ]
          },
          "right": {
            "t": "As written, with <code>match</code>",
            "h": "<code>match b.eval s.store with | true => … | false => …</code>. Rewriting the scrutinee to a literal constructor makes the match reduce by <i>iota</i> — a recursor applied to a constructor — with no instance anywhere in the chain. The difference from the left column is not whether it works but what it depends on. Reduction through <code>if</code> is only as good as the instance: give the guard a classical one and nothing reduces at all. <code>example (a b : Nat) : pick True a b = a := rfl</code> with <code>pick φ a b := if φ then a else b</code> and <code>open Classical</code> fails — <i>Type mismatch: <code>rfl</code> has type <code>?m = ?m</code> but is expected to have type <code>(if True then a else b) = a</code></i> — and you are back to <code>if_pos</code>. The <code>match</code> spelling has nothing that can go opaque on you.",
            "kind": "good"
          }
        },
        {
          "t": "detail",
          "title": "Where <code>simp [run]</code> and <code>simp only [run]</code> actually differ",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "In the <code>skip</code> and <code>assign</code> cases the proof uses <code>simp [run] at h</code>, and there the difference is load-bearing: it <i>wants</i> the extra work. <code>simp only [run] at h</code> unfolds and stops, leaving"
            },
            {
              "t": "state",
              "src": "case succ.skip\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → Exec c s s'\ns s' : State\nh : some s = some s'\n⊢ Exec Cmd.skip s s'"
            },
            {
              "t": "p",
              "h": "and the next line, <code>rw [← h]</code>, then fails with <i>Tactic `rewrite` failed: Did not find an occurrence of the pattern <code>some s'</code> in the target expression <code>Exec Cmd.skip s s'</code></i>. Plain <code>simp</code> follows the unfolding with the default simp set, which strips the <code>some</code> from both sides and hands you <code>h : s = s'</code> — an equation between states, which is what the goal contains."
            },
            {
              "t": "p",
              "h": "In the cases with a match, the two spellings agree. <code>simp</code> cannot get inside a match on an opaque scrutinee any more than <code>simp only</code> can, and substituting <code>simp [run] at h</code> for every <code>simp only [run] at h</code> in <code>run_sound</code> still compiles. So the rule of thumb is not “<code>simp only</code> or the proof breaks”; it is: use <code>simp only [run]</code> when the next tactic depends on the exact shape of the hypothesis, because then you want to have named every rewrite that fired, and use <code>simp</code> when you are trying to close a goal or extract an equation and do not care how."
            }
          ]
        }
      ],
      "pitfall": "Writing <code>cases hb : b.eval s.store</code> and then assuming <code>h</code> has been updated. It has not — the <code>cases … :</code> form rewrites the goal and gives you the equation as a named hypothesis, and that is all. Every branch in this proof begins with <code>rw [hb] at h</code> or <code>rw [hr] at h</code> for exactly that reason. Omit it and <code>exact .iteTrue hb (ih c₁ s s' h)</code> reports <i>Application type mismatch: the argument <code>h</code> has type <code>(match BExpr.eval s.store b with | true =&gt; run n c₁ s | false =&gt; run n c₂ s) = some s'</code> but is expected to have type <code>run n c₁ s = some s'</code></i> — which is the two encodings side by side, and tells you exactly which rewrite is missing. The other pitfall is at the very top: writing <code>intro n c s s' h</code> and only then <code>induction n</code>. It looks equivalent and is not. You get <code>ih : run n c s = some s' → Exec c s s'</code> — no quantifiers, pinned to the one command and the one pair of states you happen to be holding — and every compound case is then unprovable, because it needs the hypothesis at a <i>sub</i>-command. <code>intro n</code> alone is the whole trick.",
      "variants": "Drop the fault check from <code>run</code>'s <code>load</code> clause — say it returns <code>some ⟨Store.set s.store x 0, s.heap⟩</code> when the cell is missing — and soundness becomes <b>false</b>: the interpreter would report a final state for a program that is stuck, and no <code>Exec</code> derivation exists to justify it. The failure appears at exactly one place: the <code>none</code> branch of <code>cases hl</code>, which currently closes by contradiction and would then have to produce <code>Exec.load</code> without a premise to give it. Conversely, weakening the theorem to <code>run n c s = some s' → ∃ s'', Exec c s s''</code> is provable but useless: it says the program can run, not that the interpreter computed the right answer."
    },
    {
      "t": "p",
      "h": "Soundness gives you one direction. The other is harder for a reason that has nothing to do with semantics and everything to do with fuel: a derivation for <code>c₁ ;; c₂</code> is built from two sub-derivations, each of which comes with its <i>own</i> fuel bound, and you must hand a single number to <code>run</code>."
    },
    {
      "t": "steps",
      "title": "The completeness argument, in three moves",
      "items": [
        {
          "k": "Monotonicity in the fuel",
          "h": "<code>run_mono</code>: one more unit of fuel never turns a success into a failure. Proved by induction on the fuel, mirroring <code>run_sound</code> case for case."
        },
        {
          "k": "Monotonicity, transitively",
          "h": "<code>run_le</code>: if <code>n ≤ m</code> then <code>n</code> units suffice implies <code>m</code> units suffice. Proved by induction on the <i>proof</i> of <code>n ≤ m</code> — <code>Nat.le</code> is itself an inductive relation, with constructors <code>refl</code> and <code>step</code>, and the <code>step</code> case is one application of <code>run_mono</code>."
        },
        {
          "k": "Take a maximum",
          "h": "<code>run_complete</code>: induct on the <code>Exec</code> derivation. Each premise yields a fuel bound; where there are two, take <code>max n₁ n₂ + 1</code> and use <code>run_le</code> twice to lift both bounds to it. The <code>+ 1</code> pays for the current step."
        }
      ]
    },
    {
      "t": "ex",
      "id": "m5-4",
      "name": "run_mono, run_le, run_complete",
      "hard": true,
      "why": "Completeness needs monotonicity first: to run a sequence you must give both halves enough fuel, so you take the max and need to know that extra fuel is harmless. Together with <code>run_sound</code> this says the relation and the interpreter define the same partial function, which is what licenses using <code>#eval</code> as a check on your semantics.",
      "setup": "Three theorems, three different things to induct on: the fuel, the proof of <code>≤</code>, and the <code>Exec</code> derivation. From the standard library you need only <code>Nat.le_max_left</code> and <code>Nat.le_max_right</code>.",
      "goal": "theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s' : State),\n    run n c s = some s' → run (n + 1) c s = some s'\n\ntheorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s' : State}\n    (h : run n c s = some s') : run m c s = some s'\n\ntheorem run_complete {c : Cmd} {s s' : State} (h : Exec c s s') :\n    ∃ n, run n c s = some s'",
      "hints": [
        "<code>run_mono</code> is <code>run_sound</code> with a different conclusion. Same skeleton: <code>intro n</code>, induct on the fuel, then <code>cases c</code>. The atomic cases are now one tactic each, because the result does not depend on the fuel at all.",
        "For those atomic cases, <code>simpa [run] using h</code>. Read it as: simplify the goal with <code>run</code>, simplify <code>h</code> with <code>run</code>, then <code>exact</code>. Both sides unfold to the same thing.",
        "<code>run_le</code> by induction on <code>≤</code>. <code>n ≤ m</code> in Lean is <code>Nat.le n m</code>, an inductive relation with <code>refl : Nat.le n n</code> and <code>step : Nat.le n m → Nat.le n (m+1)</code>. So <code>induction hle with | refl => … | step _ ih => …</code>, and the <code>step</code> case is a single application of <code>run_mono</code>.",
        "<code>run_complete</code> by induction on the <code>Exec</code> derivation. Atomic cases: <code>⟨1, …⟩</code>. Two-premise cases: <code>obtain</code> both fuel bounds, then <code>refine ⟨max n₁ n₂ + 1, ?_⟩</code>, <code>simp only [run]</code>, and use <code>run_le (Nat.le_max_left n₁ n₂) h₁</code> to lift the first bound and <code>Nat.le_max_right</code> for the second."
      ],
      "hint": "<code>run_mono</code> by induction on fuel, mirroring <code>run_sound</code>. <code>run_le</code> by induction on <code>≤</code>. <code>run_complete</code> by induction on the <code>Exec</code> derivation, taking <code>max n₁ n₂ + 1</code> in the two-premise cases.",
      "sol": "theorem run_mono : ∀ (n : Nat) (c : Cmd) (s s' : State),\n    run n c s = some s' → run (n + 1) c s = some s' := by\n  intro n\n  induction n with\n  | zero => intro c s s' h; simp [run] at h\n  | succ n ih =>\n    intro c s s' h\n    cases c with\n    | skip => simpa [run] using h\n    | assign x e => simpa [run] using h\n    | load x l => simpa [run] using h\n    | write l e => simpa [run] using h\n    | free l => simpa [run] using h\n    | seq c₁ c₂ =>\n        simp only [run] at h ⊢\n        cases hr : run n c₁ s with\n        | none    => rw [hr] at h; simp at h\n        | some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s' h\n    | ite b c₁ c₂ =>\n        simp only [run] at h ⊢\n        cases hb : b.eval s.store with\n        | true  => rw [hb] at h; exact ih c₁ s s' h\n        | false => rw [hb] at h; exact ih c₂ s s' h\n    | loop b c =>\n        simp only [run] at h ⊢\n        cases hb : b.eval s.store with\n        | false => rw [hb] at h; exact h\n        | true  =>\n            rw [hb] at h\n            cases hr : run n c s with\n            | none    => rw [hr] at h; simp at h\n            | some s₁ =>\n                rw [hr] at h\n                have : run (n + 1) c s = some s₁ := ih c s s₁ hr\n                rw [this]\n                exact ih _ s₁ s' h\n\ntheorem run_le {n m : Nat} (hle : n ≤ m) {c : Cmd} {s s' : State}\n    (h : run n c s = some s') : run m c s = some s' := by\n  induction hle with\n  | refl => exact h\n  | step _ ih => exact run_mono _ _ _ _ ih\n\ntheorem run_complete {c : Cmd} {s s' : State} (h : Exec c s s') :\n    ∃ n, run n c s = some s' := by\n  induction h with\n  | skip => exact ⟨1, rfl⟩\n  | assign => exact ⟨1, rfl⟩\n  | load hl => exact ⟨1, by simp [run, hl]⟩\n  | write hl => exact ⟨1, by simp [run, hl]⟩\n  | free hl => exact ⟨1, by simp [run, hl]⟩\n  | seq _ _ ih₁ ih₂ =>\n      obtain ⟨n₁, h₁⟩ := ih₁\n      obtain ⟨n₂, h₂⟩ := ih₂\n      refine ⟨max n₁ n₂ + 1, ?_⟩\n      simp only [run]\n      rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n      exact run_le (Nat.le_max_right n₁ n₂) h₂\n  | iteTrue hb _ ih =>\n      obtain ⟨n, hn⟩ := ih\n      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩\n  | iteFalse hb _ ih =>\n      obtain ⟨n, hn⟩ := ih\n      exact ⟨n + 1, by simp only [run, hb]; exact hn⟩\n  | loopFalse hb => exact ⟨1, by simp only [run, hb]⟩\n  | loopTrue hb _ _ ihb ihr =>\n      obtain ⟨n₁, h₁⟩ := ihb\n      obtain ⟨n₂, h₂⟩ := ihr\n      refine ⟨max n₁ n₂ + 1, ?_⟩\n      simp only [run, hb]\n      rw [run_le (Nat.le_max_left n₁ n₂) h₁]\n      exact run_le (Nat.le_max_right n₁ n₂) h₂",
      "expl": "<code>run_le</code> is the standard trick: induct on the proof of <code>n ≤ m</code>, whose <code>step</code> case is exactly one application of <code>run_mono</code>. In <code>run_complete</code>, the <code>seq</code> and <code>loopTrue</code> cases each produce two fuel bounds; <code>max</code> plus <code>run_le</code> reconciles them. Together, <code>run_sound</code> and <code>run_complete</code> say the relation and the interpreter define the same partial function — you can now test your semantics by evaluating programs with <code>#eval</code>.",
      "walk": [
        {
          "tac": "intro n\ninduction n with\n| zero => intro c s s' h; simp [run] at h\n| succ n ih =>\n  intro c s s' h\n  cases c with",
          "h": "Identical opening to <code>run_sound</code>, down to the tactic. Only the conclusion differs: <code>ih : ∀ c s s', run n c s = some s' → run (n + 1) c s = some s'</code>. In the <code>zero</code> case <code>h : run 0 c s = some s'</code> is again absurd."
        },
        {
          "tac": "| skip => simpa [run] using h",
          "h": "<code>simpa [X] using h</code> means: simplify the goal with <code>X</code>, simplify <code>h</code> with <code>X</code>, then close with <code>exact</code>. Here Lean starts you at <code>h : run (n + 1) Cmd.skip s = some s'</code> with goal <code>run (n + 1 + 1) Cmd.skip s = some s'</code>; both sides simplify to <code>s = s'</code>, and the two <code>s = s'</code> are the same proposition, so <code>exact</code> closes it. Reach for <code>simpa … using h</code> exactly when <code>simp at h ⊢; exact h</code> would work — it is that, in one word, and it errors if the two do not meet."
        },
        {
          "tac": "| assign x e => simpa [run] using h\n| load x l => simpa [run] using h\n| write l e => simpa [run] using h\n| free l => simpa [run] using h",
          "h": "All four for the same reason: the atomic clauses of <code>run</code> match the fuel as <code>_ + 1</code> and never mention it again, so at fuel <code>n+1</code> and at fuel <code>n+2</code> they unfold to <i>literally the same term</i>. There is nothing to prove beyond unfolding."
        },
        {
          "tac": "| seq c₁ c₂ =>",
          "h": "The first case where extra fuel has to be pushed inwards."
        },
        {
          "tac": "simp only [run] at h ⊢",
          "h": "Note the <code>⊢</code>: unfold in the hypothesis <i>and</i> in the goal. Now <code>h</code> is a match on <code>run n c₁ s</code> and the goal is the same match one fuel level up, on <code>run (n+1) c₁ s</code>."
        },
        {
          "tac": "cases hr : run n c₁ s with",
          "h": "Split on the first half, at the <i>lower</i> fuel — that is the one <code>h</code> knows about."
        },
        {
          "tac": "| none    => rw [hr] at h; simp at h",
          "h": "Contradiction, as before."
        },
        {
          "tac": "| some s₁ => rw [hr] at h; rw [ih c₁ s s₁ hr]; exact ih c₂ s₁ s' h",
          "h": "Three moves in one line. <code>rw [hr] at h</code> reduces <code>h</code> to (definitionally) <code>run n c₂ s₁ = some s'</code>. <code>ih c₁ s s₁ hr : run (n+1) c₁ s = some s₁</code>, and rewriting the <i>goal</i> with it replaces the goal's scrutinee by <code>some s₁</code>, so the goal reduces to <code>run (n+1) c₂ s₁ = some s'</code>. That is exactly <code>ih c₂ s₁ s' h</code>."
        },
        {
          "tac": "| ite b c₁ c₂ =>\n    simp only [run] at h ⊢",
          "h": "Same opening. The goal's guard is the same expression as the hypothesis's guard — the guard does not depend on fuel."
        },
        {
          "tac": "cases hb : b.eval s.store with",
          "h": "Because the guard occurs in the goal, <code>cases hb :</code> substitutes <code>true</code> or <code>false</code> there automatically; only <code>h</code> needs the manual rewrite."
        },
        {
          "tac": "| true  => rw [hb] at h; exact ih c₁ s s' h",
          "h": "Both sides collapse by iota to statements about <code>c₁</code>, and <code>ih</code> is precisely the bridge between them."
        },
        {
          "tac": "| false => rw [hb] at h; exact ih c₂ s s' h",
          "h": "Mirror image."
        },
        {
          "tac": "| loop b c =>\n    simp only [run] at h ⊢",
          "h": "Here <code>simp only [run]</code> unfolds the goal <i>twice</i>: once for the outer <code>run (n+2) (.loop b c) s</code> and again for the recursive <code>run (n+1) (.loop b c) s'</code> that appears inside it. The printed goal is correspondingly large; ignore the depth and look at the outermost scrutinee."
        },
        {
          "tac": "cases hb : b.eval s.store with",
          "h": "Split the guard."
        },
        {
          "tac": "| false => rw [hb] at h; exact h",
          "h": "Guard false: both <code>h</code> and the goal reduce to <code>some s = some s'</code>. Literally the same proposition, so <code>exact h</code>."
        },
        {
          "tac": "| true  =>\n    rw [hb] at h",
          "h": "Guard true: <code>h</code> is now about the body."
        },
        {
          "tac": "cases hr : run n c s with",
          "h": "Split on the body's result at fuel <code>n</code>."
        },
        {
          "tac": "| none    => rw [hr] at h; simp at h",
          "h": "Contradiction."
        },
        {
          "tac": "| some s₁ =>\n    rw [hr] at h",
          "h": "<code>h</code> becomes (definitionally) <code>run n (.loop b c) s₁ = some s'</code>."
        },
        {
          "tac": "have : run (n + 1) c s = some s₁ := ih c s s₁ hr",
          "h": "Named because it is used as a rewrite rather than as an argument. This is the body's execution lifted to the higher fuel — exactly what the goal's inner scrutinee needs."
        },
        {
          "tac": "rw [this]",
          "h": "Rewrites the goal's scrutinee <code>run (n+1) c s</code> to <code>some s₁</code>, so the goal reduces to <code>run (n+1) (.loop b c) s₁ = some s'</code>."
        },
        {
          "tac": "exact ih _ s₁ s' h",
          "h": "The underscore is the command <code>.loop b c</code>, inferred from <code>h</code>. Note again: <code>ih</code> applied at the same command, licensed by the fuel."
        },
        {
          "tac": "theorem run_le {n m : Nat} (hle : n ≤ m) …",
          "h": "New theorem. The hypothesis <code>hle : n ≤ m</code> is a proof of an inductive proposition, so it can be inducted on just like an <code>Exec</code> derivation."
        },
        {
          "tac": "induction hle with",
          "h": "<code>Nat.le n</code> is defined with two constructors: <code>Nat.le.refl : Nat.le n n</code> and <code>Nat.le.step : Nat.le n m → Nat.le n (m+1)</code>. So this is induction on “how many times you stepped up from <code>n</code>”."
        },
        {
          "tac": "| refl => exact h",
          "h": "<code>m</code> is <code>n</code>, so the goal is the hypothesis."
        },
        {
          "tac": "| step _ ih => exact run_mono _ _ _ _ ih",
          "h": "<code>ih : run m✝ c s = some s'</code> and the goal is <code>run m✝.succ c s = some s'</code>. <code>run_mono</code> concludes <code>run (m + 1) …</code>, which is definitionally <code>m.succ</code>, so the four underscores (fuel, command, both states) are all inferred and it goes straight through."
        },
        {
          "tac": "theorem run_complete … := by\n  induction h with",
          "h": "Third theorem, third thing to induct on: the <code>Exec</code> derivation itself. Each case must exhibit a fuel bound. Note that there is no <code>generalizing</code> here, and none is needed: <code>generalizing</code> earns its place only when something <i>else</i> in the context is pinned to a particular instance that the induction hypothesis will have to be used at. In <code>exec_deterministic</code> that something was the second derivation <code>h₂</code>. Here there is nothing but the goal, and the goal is already the statement being proved about each sub-derivation."
        },
        {
          "tac": "| skip => exact ⟨1, rfl⟩",
          "h": "<code>run 1 .skip s</code> reduces to <code>some s</code> definitionally, so the second component of the pair is <code>rfl</code>. The anonymous constructor supplies witness and proof, as in M0."
        },
        {
          "tac": "| assign => exact ⟨1, rfl⟩",
          "h": "Same: the assign clause of <code>run</code> produces exactly the state that <code>Exec.assign</code> concludes with."
        },
        {
          "tac": "| load hl => exact ⟨1, by simp [run, hl]⟩",
          "h": "Not <code>rfl</code> this time, because <code>run</code> must first check <code>s.heap l</code> and the answer is only known via <code>hl</code>. Putting <code>hl</code> in the simp set lets <code>simp</code> rewrite the scrutinee and reduce the match."
        },
        {
          "tac": "| write hl => exact ⟨1, by simp [run, hl]⟩\n| free hl => exact ⟨1, by simp [run, hl]⟩",
          "h": "Identical. All three heap commands need one unit of fuel and one lookup fact."
        },
        {
          "tac": "| seq _ _ ih₁ ih₂ =>",
          "h": "The interesting case. Two induction hypotheses, each an existential."
        },
        {
          "tac": "obtain ⟨n₁, h₁⟩ := ih₁\nobtain ⟨n₂, h₂⟩ := ih₂",
          "h": "Take both pairs apart. You now have two fuel bounds with no relation between them — that is the problem the next line solves."
        },
        {
          "tac": "refine ⟨max n₁ n₂ + 1, ?_⟩",
          "h": "Commit to the witness and leave the proof obligation as a hole. <code>max</code> because either half might be the deeper one; <code>+ 1</code> because the <code>seq</code> clause of <code>run</code> consumes one unit before recursing."
        },
        {
          "tac": "simp only [run]",
          "h": "Unfold one step. The goal becomes the match on <code>run (max n₁ n₂) c₁ s</code>."
        },
        {
          "tac": "rw [run_le (Nat.le_max_left n₁ n₂) h₁]",
          "h": "<code>Nat.le_max_left n₁ n₂ : n₁ ≤ max n₁ n₂</code>. Feeding it and <code>h₁</code> to <code>run_le</code> gives <code>run (max n₁ n₂) c₁ s = some s'</code>, and rewriting with it turns the goal's scrutinee into <code>some s'</code>."
        },
        {
          "tac": "exact run_le (Nat.le_max_right n₁ n₂) h₂",
          "h": "The goal has now reduced to <code>run (max n₁ n₂) c₂ s' = some s''</code>, which is <code>h₂</code> lifted the same way. This is why monotonicity had to come first."
        },
        {
          "tac": "| iteTrue hb _ ih =>\n    obtain ⟨n, hn⟩ := ih\n    exact ⟨n + 1, by simp only [run, hb]; exact hn⟩",
          "h": "One premise, so one bound, and <code>n + 1</code> suffices. Putting <code>hb</code> in the <code>simp only</code> set rewrites the guard to <code>true</code> and reduces the match, after which the goal is <code>hn</code> up to definitional equality."
        },
        {
          "tac": "| iteFalse hb _ ih =>\n    obtain ⟨n, hn⟩ := ih\n    exact ⟨n + 1, by simp only [run, hb]; exact hn⟩",
          "h": "Mirror image."
        },
        {
          "tac": "| loopFalse hb => exact ⟨1, by simp only [run, hb]⟩",
          "h": "The loop exits immediately: one unit of fuel, guard rewritten to <code>false</code>, and the goal <code>some s = some s</code> is closed by the <code>rfl</code> that <code>simp only</code> finishes with."
        },
        {
          "tac": "| loopTrue hb _ _ ihb ihr =>\n    obtain ⟨n₁, h₁⟩ := ihb\n    obtain ⟨n₂, h₂⟩ := ihr\n    refine ⟨max n₁ n₂ + 1, ?_⟩",
          "h": "Exactly the <code>seq</code> pattern: one bound for the body, one for the remainder of the loop, reconciled by <code>max</code>."
        },
        {
          "tac": "simp only [run, hb]",
          "h": "One extra ingredient compared with <code>seq</code>: <code>hb</code>, to get past the guard before reaching the body's match."
        },
        {
          "tac": "rw [run_le (Nat.le_max_left n₁ n₂) h₁]\nexact run_le (Nat.le_max_right n₁ n₂) h₂",
          "h": "Character for character the <code>seq</code> ending. Sequencing and one loop iteration are the same operation, and here — as in <code>exec_deterministic</code> — the proofs coincide."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "run_mono, seq case, starting after <code>simp only [run] at h ⊢</code>",
          "start": "case succ.seq\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → run (n + 1) c s = some s'\ns s' : State\nc₁ c₂ : Cmd\nh :\n  (match run n c₁ s with\n    | some s' => run n c₂ s'\n    | none => none) =\n    some s'\n⊢ (match run (n + 1) c₁ s with\n    | some s' => run (n + 1) c₂ s'\n    | none => none) =\n    some s'",
          "steps": [
            {
              "tac": "cases hr : run n c₁ s with | some s₁ => rw [hr] at h",
              "state": "case succ.seq.some\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → run (n + 1) c s = some s'\ns s' : State\nc₁ c₂ : Cmd\ns₁ : State\nh :\n  (match some s₁ with\n    | some s' => run n c₂ s'\n    | none => none) =\n    some s'\nhr : run n c₁ s = some s₁\n⊢ (match run (n + 1) c₁ s with\n    | some s' => run (n + 1) c₂ s'\n    | none => none) =\n    some s'",
              "h": "<code>h</code>'s scrutinee is now literal, so <code>h</code> is definitionally <code>run n c₂ s₁ = some s'</code>. The goal is untouched — the goal's scrutinee is at fuel <code>n + 1</code>, and <code>hr</code> says nothing about it."
            },
            {
              "tac": "rw [ih c₁ s s₁ hr]",
              "state": "case succ.seq.some\nn : Nat\nih : ∀ (c : Cmd) (s s' : State), run n c s = some s' → run (n + 1) c s = some s'\ns s' : State\nc₁ c₂ : Cmd\ns₁ : State\nh :\n  (match some s₁ with\n    | some s' => run n c₂ s'\n    | none => none) =\n    some s'\nhr : run n c₁ s = some s₁\n⊢ (match some s₁ with\n    | some s' => run (n + 1) c₂ s'\n    | none => none) =\n    some s'",
              "h": "<code>ih c₁ s s₁ hr : run (n + 1) c₁ s = some s₁</code> — the induction hypothesis used as a rewrite rule on the goal. Now both scrutinees are <code>some s₁</code> and the goal is definitionally <code>run (n + 1) c₂ s₁ = some s'</code>."
            },
            {
              "tac": "exact ih c₂ s₁ s' h",
              "state": "No goals.",
              "h": "One more application of the same hypothesis, this time as a function. Nothing here is specific to <code>seq</code> except which command goes where."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "run_le — induction on a proof of ≤",
          "start": "n m : Nat\nhle : n ≤ m\nc : Cmd\ns s' : State\nh : run n c s = some s'\n⊢ run m c s = some s'",
          "steps": [
            {
              "tac": "induction hle with | refl =>",
              "state": "case refl\nn m : Nat\nc : Cmd\ns s' : State\nh : run n c s = some s'\n⊢ run n c s = some s'",
              "h": "In the <code>refl</code> case the upper bound <i>is</i> <code>n</code>, so the goal is literally the hypothesis. <code>exact h</code>."
            },
            {
              "tac": "| step _ ih =>",
              "state": "case step\nn m : Nat\nc : Cmd\ns s' : State\nh : run n c s = some s'\nm✝ : Nat\na✝ : n.le m✝\nih : run m✝ c s = some s'\n⊢ run m✝.succ c s = some s'",
              "h": "The induction hypothesis is the statement at the smaller bound, and the goal is at one more. Note the printing: <code>Nat.le</code> shows as <code>n.le m✝</code> and <code>m✝ + 1</code> shows as <code>m✝.succ</code>."
            },
            {
              "tac": "exact run_mono _ _ _ _ ih",
              "state": "No goals.",
              "h": "<code>run_mono</code> concludes <code>run (m✝ + 1) c s = some s'</code>. That is definitionally <code>run m✝.succ c s = some s'</code>, so <code>exact</code> accepts it even though the display differs. All four arguments are inferred from <code>ih</code> and the goal."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "run_complete, seq case — where the max is spent",
          "start": "case seq\nc : Cmd\ns s' s✝ s'✝ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝\nh₂✝ : Exec c₂✝ s'✝ s''✝\nih₁ : ∃ n, run n c₁✝ s✝ = some s'✝\nih₂ : ∃ n, run n c₂✝ s'✝ = some s''✝\n⊢ ∃ n, run n (c₁✝ ;; c₂✝) s✝ = some s''✝",
          "steps": [
            {
              "tac": "obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂; refine ⟨max n₁ n₂ + 1, ?_⟩",
              "state": "case seq\nc : Cmd\ns s' s✝ s'✝ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝\nh₂✝ : Exec c₂✝ s'✝ s''✝\nn₁ : Nat\nh₁ : run n₁ c₁✝ s✝ = some s'✝\nn₂ : Nat\nh₂ : run n₂ c₂✝ s'✝ = some s''✝\n⊢ run (max n₁ n₂ + 1) (c₁✝ ;; c₂✝) s✝ = some s''✝",
              "h": "The witness is chosen; the existential is gone. Two independent bounds remain, and neither is directly about <code>max n₁ n₂</code>."
            },
            {
              "tac": "simp only [run]",
              "state": "case seq\nc : Cmd\ns s' s✝ s'✝ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝\nh₂✝ : Exec c₂✝ s'✝ s''✝\nn₁ : Nat\nh₁ : run n₁ c₁✝ s✝ = some s'✝\nn₂ : Nat\nh₂ : run n₂ c₂✝ s'✝ = some s''✝\n⊢ (match run (max n₁ n₂) c₁✝ s✝ with\n    | some s' => run (max n₁ n₂) c₂✝ s'\n    | none => none) =\n    some s''✝",
              "h": "One unfolding step. The <code>+ 1</code> has been consumed, and both recursive calls are at <code>max n₁ n₂</code>."
            },
            {
              "tac": "rw [run_le (Nat.le_max_left n₁ n₂) h₁]",
              "state": "case seq\nc : Cmd\ns s' s✝ s'✝ s''✝ : State\nc₁✝ c₂✝ : Cmd\nh₁✝ : Exec c₁✝ s✝ s'✝\nh₂✝ : Exec c₂✝ s'✝ s''✝\nn₁ : Nat\nh₁ : run n₁ c₁✝ s✝ = some s'✝\nn₂ : Nat\nh₂ : run n₂ c₂✝ s'✝ = some s''✝\n⊢ (match some s'✝ with\n    | some s' => run (max n₁ n₂) c₂✝ s'\n    | none => none) =\n    some s''✝",
              "h": "The first half's bound has been lifted from <code>n₁</code> to <code>max n₁ n₂</code> and used to reduce the scrutinee. The goal is now definitionally <code>run (max n₁ n₂) c₂✝ s'✝ = some s''✝</code>."
            },
            {
              "tac": "exact run_le (Nat.le_max_right n₁ n₂) h₂",
              "state": "No goals.",
              "h": "The second half's bound, lifted the same way. Both uses of <code>run_le</code> are essential and they are essential for the same reason: <code>max</code> is an upper bound of both, and nothing more."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why <code>max n₁ n₂ + 1</code> and not <code>n₁ + n₂</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Both work, and the sum is what you would use if fuel counted <i>steps</i>. It does not: <code>run</code> hands the same <code>n</code> to both halves of a sequence, so fuel is a bound on the <b>depth</b> of the recursion, not on its total size. The two halves of a <code>seq</code> run in parallel as far as the counter is concerned, so the maximum is the right combinator and the sum is merely a wasteful upper bound."
            },
            {
              "t": "p",
              "h": "This also explains why <code>run_le</code> is needed at all rather than a bare <code>run_mono</code>: you must lift <i>both</i> bounds to the same number, and neither of them is one step below it."
            }
          ]
        }
      ],
      "pitfall": "In the <code>loop</code> case of <code>run_mono</code>, expecting <code>simp only [run] at h ⊢</code> to unfold the goal once. It unfolds it as often as it can, so the goal you see contains a <i>second</i> copy of the loop clause nested inside the first. Do not try to make the displayed goal small; work on the outermost scrutinee and let the rest reduce definitionally. The other trap is in <code>run_complete</code>: writing <code>exact ⟨1, rfl⟩</code> for the <code>load</code> case. It fails, because <code>run 1 (.load x l) s</code> cannot reduce until the scrutinee <code>s.heap l</code> is known, and the only thing that knows it is <code>hl</code> — hence <code>by simp [run, hl]</code>.",
      "variants": "Drop <code>run_le</code> and try to finish <code>run_complete</code> with <code>run_mono</code> alone: you can lift a bound by one, but <code>max n₁ n₂</code> is generally many steps above <code>n₁</code>, so you would have to induct — which is precisely what <code>run_le</code> is. Reverse the direction of <code>run_mono</code> — claim <code>run (n+1) c s = some s' → run n c s = some s'</code> — and it is false: take any program needing depth <code>n+1</code> and evaluate it with <code>n</code>. Finally, note what <code>run_complete</code> does <b>not</b> say: it gives no bound on the fuel in terms of the program. There is none, since the loop can run arbitrarily long; the theorem is a pure existence statement, and that is all the testing use requires."
    },
    {
      "t": "p",
      "h": "With both directions in hand the two semantics are interchangeable, and it is worth writing that down once even though the corpus does not:"
    },
    {
      "t": "code",
      "src": "theorem exec_iff_run {c : Cmd} {s s' : State} :\n    Exec c s s' ↔ ∃ n, run n c s = some s' :=\n  ⟨run_complete, fun ⟨n, hn⟩ => run_sound n c s s' hn⟩",
      "tag": "illustration",
      "cap": "Not in the corpus; compiles against the M5 prelude."
    },
    {
      "t": "p",
      "h": "Three pieces of Lean notation are compressed into that one-line proof term. <code>Iff</code> is a structure with two fields, <code>mp : a → b</code> and <code>mpr : b → a</code>, so its anonymous constructor takes exactly two arguments — the forward implication first. <code>run_complete</code> already <i>is</i> the forward implication, because <code>Exec c s s'</code> is its hypothesis; no <code>fun</code> needed. And <code>fun ⟨n, hn⟩ => …</code> is a pattern-matching lambda: the argument has type <code>∃ n, run n c s = some s'</code>, a one-constructor inductive, so the pattern splits it into witness and proof on the way in. Lean elaborates it to a <code>match</code>; you could equally write <code>fun hex => hex.elim (fun n hn => run_sound n c s s' hn)</code> and get the same term."
    },
    {
      "t": "p",
      "h": "And now you can actually run a program. Location 7 holds 41; the program reads it into variable 0, adds one, and writes it back."
    },
    {
      "t": "code",
      "src": "def demoStore : Store := fun _ => 0\ndef demoHeap  : Heap  := Heap.singleton 7 41\ndef demoState : State := ⟨demoStore, demoHeap⟩\n\ndef bump : Cmd :=\n  .load 0 7 ;; .write 7 (.plus (.var 0) (.const 1))\n\n#eval (run 5 bump demoState).map (fun s => s.heap 7)   -- enough fuel\n#eval (run 1 bump demoState).map (fun s => s.heap 7)   -- not enough fuel\n#eval (run 5 (.load 0 99) demoState).map (fun s => s.store 0)  -- unallocated",
      "tag": "illustration",
      "cap": "Not in the corpus; compiles against the M5 prelude."
    },
    {
      "t": "state",
      "src": "some (some 42)\nnone\nnone",
      "cap": "The three #eval outputs, in order."
    },
    {
      "t": "p",
      "h": "The doubled <code>some</code> in the first line is two different <code>Option</code>s. <code>run 5 bump demoState : Option State</code>, and <code>Option.map</code> pushes the projection under it, so the outer <code>some</code> means <i>the interpreter produced a final state</i>. The inner one is that state's heap answering at location 7, and <code>Heap = Loc → Option Val</code>, so it means <i>the cell exists</i>. Its content is 42. The projection is there because <code>State</code> has no <code>Repr</code> instance and could not be printed directly."
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "<code>none</code> tells you nothing",
      "h": "The second and third outputs are the same value for entirely different reasons: one program ran out of fuel, the other faulted. <code>run</code> cannot distinguish them and neither can <code>Exec</code> — that is the same conflation of “stuck” and “diverging” noted at the top of the chapter, seen from the computational side. Only a <code>some</code> is informative, which is exactly why <code>run_sound</code> is stated with <code>some s'</code> as its hypothesis."
    },
    {
      "t": "p",
      "h": "The interpreter also lets you <i>prove</i> that a program diverges, by proving that no fuel suffices and appealing to completeness. This is the promised counterexample: a loop whose guard is constantly true has no <code>Exec</code> derivation at all."
    },
    {
      "t": "code",
      "src": "def spin : Cmd := .loop (.not (.equals (.const 0) (.const 1))) .skip\n\ntheorem run_spin_none : ∀ (n : Nat) (s : State), run n spin s = none := by\n  intro n\n  induction n with\n  | zero => intro s; rfl\n  | succ n ih =>\n      intro s\n      show (match run n Cmd.skip s with\n            | some s' => run n spin s'\n            | none    => none) = none\n      cases n with\n      | zero   => rfl\n      | succ m => exact ih s\n\ntheorem spin_diverges (s s' : State) : ¬ Exec spin s s' := by\n  intro hex\n  obtain ⟨n, hn⟩ := run_complete hex\n  rw [run_spin_none n s] at hn\n  exact absurd hn (by simp)",
      "tag": "illustration",
      "cap": "Not in the corpus; compiles against the M5 prelude. Note the <code>show</code>, used exactly as M0 recommends: to make an unreadable goal readable so the following tactics can be written by eye."
    },
    {
      "t": "p",
      "h": "The <code>cases n</code> in the middle of <code>run_spin_none</code> looks redundant and is not. After the <code>show</code>, the goal scrutinises <code>run n Cmd.skip s</code> with <code>n</code> a variable, and that term is stuck: <code>run</code> matches its fuel against <code>0</code> and <code>_ + 1</code>, and a bare <code>n</code> is neither. Try to finish with <code>exact ih s</code> and Lean answers <i>Type mismatch: <code>ih s</code> has type <code>run n spin s = none</code> but is expected to have type <code>(match run n Cmd.skip s with | some s' => run n spin s' | none => none) = none</code></i>. Splitting <code>n</code> unblocks the match in both branches: at <code>0</code> the body returns <code>none</code> and the whole thing is <code>rfl</code>; at <code>m + 1</code> the body returns <code>some s</code>, the match reduces to <code>run n spin s</code>, and that is exactly <code>ih s</code>."
    },
    {
      "t": "p",
      "h": "Read <code>spin_diverges</code> as the formal content of the second bullet at the top of this chapter. Divergence is not represented; it is the <i>absence</i> of a derivation, and the only way to establish it is negatively. M13 introduces <code>PartialHoare</code> precisely so that a specification can be true of a program like <code>spin</code> — vacuously, because there is no final state to constrain."
    },

    {
      "t": "sec",
      "s": "What you keep"
    },
    {
      "t": "tbl",
      "head": ["Name", "Used again in", "What for"],
      "rows": [
        ["<code>Cmd</code>, <code>Atom</code>, <code>BExpr</code>, <code>State</code>", "everything", "the objects every later theorem quantifies over"],
        ["<code>Exec</code>", "M6–M14", "<code>Hoare</code> is one existential over it; <code>Local</code> in M8 is a property of it"],
        ["<code>Store.set</code>", "M6 onwards", "the semantic <code>subst</code> of M6 is defined in terms of it"],
        ["<code>exec_deterministic</code>", "M13, once", "<code>partial_of_total</code>: a total-correctness triple implies the partial one"],
        ["<code>exec_skip_inv</code>", "never", "a warm-up; the technique is what you keep, not the lemma"],
        ["<code>run</code>, <code>run_sound</code>, <code>run_complete</code>", "never", "testing. <code>#eval</code> your programs before you prove things about them"]
      ],
      "cap": "Being honest about what earns its place. Two of the four exercises produce lemmas you will not cite again — they are here for the technique."
    },
    {
      "t": "dod",
      "h": "You have a relational semantics suitable for proofs, an executable interpreter suitable for testing, and a theorem saying they are the same thing. You can invert an <code>Exec</code> hypothesis without thinking, you know why <code>generalizing</code> is needed, and you can read a goal in which a hypothesis displays as an unreduced <code>match</code>."
    }
  ]
});
