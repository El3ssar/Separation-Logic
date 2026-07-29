/* M7 — The small-footprint rules
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m7",
  "num": "M7",
  "phase": "Phase 2 · Program logic",
  "title": "The small-footprint rules",
  "blurb": "Load, write, and free — each specified using only the memory it actually touches.",

  "orient": {
    "youWill": [
      "Read <code>Hoare P c Q</code> as the nested existential it really is, and fill the whole thing with one <code>refine</code>.",
      "Prove the load, write and free rules straight from <code>Exec</code> — six lines, five lines, five lines.",
      "Say which heap each side of a <code>∗</code> in a postcondition owns, and watch Lean reject the other choice with two false goals.",
      "Exhibit a concrete heap on which the free rule fails if <code>↦</code> is not exact.",
      "Compose two triples without the frame rule, and feel precisely where it is missing."
    ],
    "needs": [
      "<code>Hoare</code> from M6, and the <code>intro</code> / <code>refine</code> / anonymous-constructor style used in <code>assign_constant</code>.",
      "The exact reading of <code>↦</code>, plus <code>emp</code>, <code>fact</code> and <code>pure</code> from M3; <code>∗</code> and its six-component unfolding from M4.",
      "<code>singleton_same</code>, <code>write_singleton</code>, <code>erase_singleton</code> from M1 and <code>disjoint_empty_left</code>, <code>union_empty_left</code> from M2. All five appear verbatim in the solutions below.",
      "The <code>Exec</code> constructors from M5 — in particular that <code>load</code>, <code>write</code> and <code>free</code> each carry a side condition of the form <code>s.heap l = some v</code>."
    ],
    "payoff": "These three triples are the last time you build an <code>Exec</code> derivation in order to <i>verify a program</i>. M8 opens the semantics once more — to prove each command local — and then lifts these three rules to arbitrary heaps for good. From M9 on, a program proof is assembled out of <code>hoare_seq</code>, <code>hoare_frame</code> and <code>hoare_consequence</code>, and <code>Exec</code> turning up in one means a lemma is missing."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "Here is the design principle that separates separation logic from everything before it:"
    },
    {
      "t": "quote",
      "h": "A primitive specification mentions <b>only the cells the command touches</b>. Nothing else. Larger heaps are the frame rule’s problem, not the rule’s."
    },
    {
      "t": "p",
      "h": "So the write rule owns exactly one cell, not “a heap containing that cell”:"
    },
    {
      "t": "txt",
      "src": "  { l ↦ old }        [l] := e        { l ↦ e }\n  { l ↦ v }          x := [l]        { ⌜x = v⌝ ∗ l ↦ v }\n  { l ↦ v }          free l          { emp }"
    },
    {
      "t": "cmp",
      "left": {
        "t": "The rule you would write first",
        "kind": "bad",
        "h": "Talk about the heap the program actually runs in. The precondition says “<code>h</code> has <code>l</code> in it, and whatever else”; the postcondition must then describe that whole heap again, updated. Every rule now quantifies over an unknown <i>rest</i>, so every rule has to say something about it — and every proof that uses the rule has to re-derive facts about it.",
        "src": "  { fun _ h => h l = some old  ∧  REST h }\n      [l] := e\n  { fun σ h => h l = some (e.eval σ)  ∧  REST' h }"
      },
      "right": {
        "t": "The small-footprint rule",
        "kind": "good",
        "h": "The precondition is <code>l ↦ old</code>, and in this development that is an <i>equation</i>: the heap <b>is</b> the one-cell heap <code>Heap.singleton l old</code>. There is no <i>rest</i> to mention, so there is nothing to carry, and nothing to re-derive. The frame rule of M8 puts the rest back — once, for every rule at the same time.",
        "src": "  { l ↦ old }   [l] := e   { l ↦ e }"
      }
    },
    {
      "t": "p",
      "h": "That <code>REST</code> on the left is the entire problem. It is not just ugly: it is the reason classical Hoare logic does not scale to pointers. Each rule has to state how it acts on the unknown remainder, and the statements are all different. Separation logic replaces <i>n</i> such statements with one theorem — the frame rule — and pays for that by insisting the primitive rules mention nothing but their own footprint."
    },
    {
      "t": "note",
      "h": "This is where the exactness of <code>↦</code> from M3 pays for itself. If <code>l ↦ v</code> merely meant <code>h l = some v</code>, the free rule would say “freeing one cell of any heap leaves the heap empty”, which is nonsense. Exact ownership makes the small rule <i>literally true</i>, and the frame rule then lifts it to arbitrary heaps without weakening anything.",
      "title": "The one thing to remember",
      "kind": "key"
    },
    {
      "t": "detail",
      "title": "Break it: the free rule under a loose ↦",
      "tag": "counterexample",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "“Nonsense” is a claim, so here it is as a refutation Lean accepts. Replace the exact <code>↦</code> by the “at least this cell” reading and the free rule becomes false:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "def pointsToLoose (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v\n\ntheorem loose_free_unsound :\n    ¬ Hoare (pointsToLoose 0 0) (.free 0) emp := by\n  intro hbad\n  obtain ⟨s', hex, hemp⟩ := hbad (fun _ => 0) (fun _ => some 0) rfl\n  cases hex with\n  | free hl =>\n      have he : Heap.erase (fun _ => some 0) 0 = Heap.empty := hemp\n      have h1 : Heap.erase (fun _ => some 0) 0 1 = Heap.empty 1 := by rw [he]\n      rw [erase_other _ 0 1 (by simp)] at h1\n      exact absurd h1 (by simp [Heap.empty])"
        },
        {
          "t": "p",
          "h": "The witness heap is <code>fun _ => some 0</code>: every location holds <code>0</code>. It satisfies the loose precondition at location <code>0</code>. Running <code>free 0</code> erases location <code>0</code> and nothing else, so location <code>1</code> still holds <code>some 0</code> — and the postcondition <code>emp</code> is false. Name the moving part: exactness is what makes “the heap afterwards” a <i>function of</i> “the heap beforehand”. Under the loose reading, <code>free</code> would have to be told what the rest of the heap was, and the rule would have to mention it."
        },
        {
          "t": "p",
          "h": "Two Lean details in that proof, since they recur. <code>obtain ⟨s', hex, hemp⟩ := hbad σ h hp</code> applies the assumed triple to a concrete state and immediately takes the resulting <code>∃ s', _ ∧ _</code> apart. And <code>have he : Heap.erase (fun _ => some 0) 0 = Heap.empty := hemp</code> is a <i>restatement</i>: <code>hemp</code>’s type is <code>emp {…}.store {…}.heap</code>, which is definitionally the equation but not syntactically, and <code>rw</code> matches syntax. Ascribing a type to a <code>have</code> is the standard way to force a hypothesis into the shape a later tactic can see."
        }
      ]
    },
    {
      "t": "p",
      "h": "Note also what the load rule does <i>not</i> do: it does not consume the cell. Reading is not destructive, so <code>l ↦ v</code> reappears in the postcondition, now next to a pure fact about the store. The pure fact is spatially empty — it owns nothing — which is exactly why <code>pure</code> rather than <code>fact</code> is the right choice on the left of that <code>∗</code>."
    },
    {
      "t": "detail",
      "title": "Why pure and not fact on the left of that ∗",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "Recall the two from M3: <code>fact φ = fun σ _ => φ σ</code> ignores the heap and therefore holds of <i>any</i> heap, while <code>pure φ = aAnd (fact φ) emp</code> additionally pins the heap to <code>Heap.empty</code>. On the left of a <code>∗</code> that difference is not cosmetic. With <code>fact</code>, the left conjunct is free to swallow memory:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "-- `fact φ ∗ P` lets the left conjunct silently own a cell.\nexample (l : Loc) (v : Val) (σ : Store) :\n    (fact (fun _ => True) ∗ emp) σ (Heap.singleton l v) :=\n  ⟨Heap.singleton l v, Heap.empty, disjoint_empty_right _,\n   (union_empty_right _).symm, trivial, rfl⟩\n\n-- `pure φ ∗ P` does not: the left heap is forced to be empty.\ntheorem star_emp_forces_empty (φ : Store → Prop) (σ : Store) (h : Heap)\n    (hh : (pure φ ∗ emp) σ h) : h = Heap.empty := by\n  obtain ⟨h₁, h₂, _, hu, ⟨_, he₁⟩, he₂⟩ := hh\n  subst he₁; subst he₂\n  rw [hu, union_empty_left]"
        },
        {
          "t": "p",
          "h": "The first example says <code>fact True ∗ emp</code> holds of a one-cell heap: the split was <code>Heap.singleton l v</code> on the left and <code>Heap.empty</code> on the right. So a postcondition <code>fact φ ∗ (l ↦ v)</code> would no longer say “the final heap is exactly that one cell” — it would say “the final heap contains that cell somewhere”, which is the loose reading again, smuggled in through the wrong conjunct. <code>pure</code> is what keeps the load rule exact."
        }
      ]
    },
    {
      "t": "h3",
      "s": "Reading a Hoare goal from the inside"
    },
    {
      "t": "p",
      "h": "Every proof in this chapter begins by unfolding one definition. Here it is again, from M6:"
    },
    {
      "t": "code",
      "src": "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap"
    },
    {
      "t": "anat",
      "src": "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap",
      "parts": [
        {
          "m": "∀ σ h",
          "h": "A triple is a statement about <i>every</i> initial store and heap. <code>intro σ h hp</code> is the first line of four of the five solutions below, and it takes these two plus the precondition."
        },
        {
          "m": "P σ h →",
          "h": "The precondition arrives as a hypothesis. This is the step where the small-footprint discipline pays: when <code>P</code> is <code>l ↦ v</code>, the hypothesis is an <i>equation</i> <code>h = Heap.singleton l v</code>, so it can be eliminated rather than reasoned with. That is what <code>subst hp</code> does on line two."
        },
        {
          "m": "∃ s'",
          "h": "You must <b>produce</b> the final state. Lean will not compute it for you — there is no evaluator in the definition. Writing down <code>⟨store-after, heap-after⟩</code> is the one creative step in each of these proofs."
        },
        {
          "m": "Exec c ⟨σ, h⟩ s'",
          "h": "Simultaneously: the command does not fault, does not diverge, and lands in <code>s'</code>. Read <code>⟨σ, h⟩</code> as the <code>State</code> structure built from the store and the heap; Lean prints it back as <code>{ store := σ, heap := h }</code>."
        },
        {
          "m": "Q s'.store s'.heap",
          "h": "Note the projections. <code>s'</code> is a <code>State</code>, and an <code>Assertion</code> takes a store and a heap separately, so the postcondition is applied to the two fields. When you supply <code>s'</code> as a literal <code>⟨a, b⟩</code>, these projections reduce to <code>a</code> and <code>b</code> — silently, which is why the goals below look noisier than they are."
        }
      ]
    },
    {
      "t": "p",
      "h": "So the first two lines are always the same. Here is what Lean actually shows after each of them, taking the free rule as the example. After <code>intro σ h hp</code>:"
    },
    {
      "t": "state",
      "src": "l : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := h } s' ∧ emp s'.store s'.heap",
      "cap": "Note that Lean prints the precondition as `(l ↦ v) σ h`, not as the equation. The notation is preserved; the definition is not unfolded on screen."
    },
    {
      "t": "p",
      "h": "and after <code>subst hp</code>:"
    },
    {
      "t": "state",
      "src": "l : Loc\nv : Val\nσ : Store\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } s' ∧ emp s'.store s'.heap",
      "cap": "`h` and `hp` are gone; every heap in the goal is now a literal `Heap.singleton l v`. That is the whole benefit of an exact precondition."
    },
    {
      "t": "detail",
      "title": "What subst hp actually did, and why not rw [hp]",
      "tag": "tactic",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "<code>hp : (l ↦ v) σ h</code> is not syntactically an equation. It becomes one after unfolding <code>pointsTo</code> and applying the resulting lambda — a δ-step and two β-steps. <code>subst</code> looks through that reduction, finds an equation with a bare local variable on one side (<code>h</code>), and then <i>eliminates the variable</i>: every occurrence of <code>h</code> in the goal and in every hypothesis is replaced, and both <code>h</code> and <code>hp</code> are removed from the context."
        },
        {
          "t": "p",
          "h": "<code>rw [hp]</code> also compiles here, but it only rewrites the goal. Lean leaves the corpses behind:"
        },
        {
          "t": "state",
          "src": "l : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } s' ∧ emp s'.store s'.heap",
          "cap": "After `rw [hp]`. Same goal, two dead hypotheses."
        },
        {
          "t": "p",
          "h": "Nothing later needs <code>h</code>, so <code>subst</code> is the right tactic. The general rule: use <code>subst</code> when the equation defines a variable you want to stop thinking about; use <code>rw</code> when you want to keep the variable and change one occurrence."
        },
        {
          "t": "p",
          "h": "One restriction worth knowing now, because it will bite later: <code>subst</code> refuses if the variable occurs on <i>both</i> sides of the equation, or if the side to be eliminated is not a bare local variable but a compound term. In those cases you fall back to <code>rw</code>, or to <code>cases hp</code>, which matches on the <code>Eq.refl</code> constructor and achieves the same substitution — it leaves the goal in a <code>case refl</code>, which is harmless."
        }
      ]
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "singleton_same",
          "h": "<code>Heap.singleton l v l = some v</code>. Every one of the three memory constructors of <code>Exec</code> carries a side condition <code>s.heap l = some v</code> — “the cell exists”. Once the precondition has been <code>subst</code>ed, that side condition <b>is</b> this lemma, verbatim, in all three proofs."
        },
        {
          "k": "write_singleton",
          "h": "<code>Heap.write (Heap.singleton l v) l w = Heap.singleton l w</code>. The entire mathematical content of the write rule. Proved in M1 by <code>funext</code> and a case split; used here as a one-word citation."
        },
        {
          "k": "erase_singleton",
          "h": "<code>Heap.erase (Heap.singleton l v) l = Heap.empty</code>. The entire mathematical content of the free rule, and the statement that is false under an inexact <code>↦</code>."
        },
        {
          "k": "disjoint_empty_left, union_empty_left",
          "h": "<code>Heap.disjoint Heap.empty h</code> and <code>Heap.union Heap.empty h = h</code>. These are the two obligations you owe whenever you cut a heap as <code>Heap.empty</code> against everything else — which is exactly what a <code>pure</code> conjunct forces you to do. You will use them in the load rule and nowhere else in this chapter."
        },
        {
          "k": "Store.set",
          "h": "Not a lemma but a definition, <code>fun y => if y = x then v else σ y</code>. There is no <code>Store.set_same</code> in this development, so the way to prove <code>Store.set σ x v x = v</code> is <code>simp [Store.set]</code>, which unfolds it and discharges the <code>if</code>."
        }
      ]
    },
    {
      "t": "steps",
      "title": "The shape of every proof in this chapter",
      "items": [
        {
          "k": "Open the definition",
          "h": "<code>intro σ h hp</code>. You now owe an existential, not a triple."
        },
        {
          "k": "Eliminate the heap variable",
          "h": "<code>subst hp</code>. The precondition was an equation, so afterwards there is no <code>h</code> — only <code>Heap.singleton l v</code>."
        },
        {
          "k": "Name the final state",
          "h": "The only creative step. Read it off the <code>Exec</code> constructor you are going to use: <code>load</code> sets the store and keeps the heap, <code>write</code> keeps the store and writes the heap, <code>free</code> keeps the store and erases from the heap."
        },
        {
          "k": "Discharge the execution",
          "h": "<code>Exec.load</code>, <code>Exec.write</code> or <code>Exec.free</code> applied to <code>singleton_same l v</code>. Every time."
        },
        {
          "k": "Discharge the postcondition",
          "h": "One M1 lemma for <code>write</code> and <code>free</code>. For <code>load</code>, a heap cut plus a single <code>simp</code>, because the postcondition has a <code>∗</code> in it."
        }
      ]
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "Why Exec.load (singleton_same l v) typechecks at all",
      "h": "The constructor wants <code>hl : s.heap l = some v</code>, where <code>s</code> is the initial state <code>⟨σ, Heap.singleton l v⟩</code>. What you hand it has type <code>Heap.singleton l v l = some v</code>. Those are different expressions — but <code>{ store := σ, heap := Heap.singleton l v }.heap</code> reduces to <code>Heap.singleton l v</code> by projecting a literal structure, and application checks types up to reduction. <code>rw</code> does <b>not</b>: it matches syntactically. The error below is what that looks like."
    },
    {
      "t": "state",
      "src": "error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  Heap.singleton ?l ?v ?l\nin the target expression\n  { store := σ, heap := Heap.singleton l v }.heap l = some v\n\nσ : Store\nl : Loc\nv : Val\n⊢ { store := σ, heap := Heap.singleton l v }.heap l = some v",
      "cap": "`rw [singleton_same]` on a goal that `exact singleton_same l v` closes without complaint. The pattern `Heap.singleton ?l ?v ?l` is there up to reduction and nowhere in the syntax, and `rw` only reads the syntax."
    },
    {
      "t": "p",
      "h": "That asymmetry is worth internalising now, because it decides which tactic to reach for all through M8. Rule of thumb: if you are <i>supplying</i> a proof, mismatches up to unfolding are free, so <code>exact</code> and plain application will take it; if you are <i>transforming</i> a goal or hypothesis, you are back to syntax and must make the two sides look alike first. In M8 you will meet the standard way to do that, <code>have hl' : h l = _ := hl</code>, which re-typechecks a projected hypothesis against a reduced statement — the <code>_</code> is filled in by unification — so that <code>rw</code> can then see it."
    },
    {
      "t": "sec",
      "s": "Exercises · the three primitive rules"
    },
    {
      "t": "ex",
      "id": "m7-1",
      "name": "hoare_load",
      "hard": false,
      "why": "The load rule is the only one of the three whose postcondition has structure, and building it teaches the thing this chapter exists to teach: in a <code>∗</code>-goal <i>you</i> supply the cut, and the cut is not a matter of taste. Reading is not destructive, so the cell must come back; the fact you learned lives in the store, not the heap, so it must be attached by a conjunct that owns nothing. Exactly one split satisfies both, and Lean will show you two false goals if you pick the other.",
      "setup": "In scope: <code>Hoare</code>, the <code>Exec</code> constructors, <code>pointsTo</code> (<code>↦</code>), <code>pure</code>, <code>star</code> (<code>∗</code>), <code>Store.set</code>, and every heap lemma from M1 and M2. You will need <code>singleton_same</code>, <code>disjoint_empty_left</code> and <code>union_empty_left</code>.",
      "goal": "theorem hoare_load (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (.load x l)\n      (pure (fun σ => σ x = v) ∗ (l ↦ v))",
      "hints": [
        "<code>Hoare</code> is a definition, not a primitive. Start with <code>intro σ h hp</code> and look at what is left: one existential, then a conjunction.",
        "<code>hp : (l ↦ v) σ h</code> unfolds to the equation <code>h = Heap.singleton l v</code>, and <code>h</code> is a local variable. So <code>subst hp</code> removes <code>h</code> from the problem altogether, and every heap in the goal becomes a literal singleton.",
        "The witness for <code>∃ s'</code> is a <code>State</code>, that is a pair <code>⟨store, heap⟩</code>. A load writes the store and leaves the heap alone, so the pair is <code>⟨Store.set σ x v, Heap.singleton l v⟩</code>. <code>Exec.load</code> then wants the side condition <code>singleton_same l v</code>, on the nose.",
        "Now the <code>∗</code>. Unfolded, a star goal is <code>∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code> — six components inside one <code>⟨…⟩</code>. Ask what <code>h₁</code> is allowed to be: the left conjunct is <code>pure φ</code>, which is <code>aAnd (fact φ) emp</code>, and <code>emp</code> pins its heap to <code>Heap.empty</code>. So <code>h₁ := Heap.empty</code> and <code>h₂ := Heap.singleton l v</code>, and the choice was never yours.",
        "<code>refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩</code>. That leaves one goal, about the store. It displays with <code>fact</code> at the head; use <code>show Store.set σ x v x = v</code> to force it into readable form, then <code>simp [Store.set]</code>."
      ],
      "sol": "theorem hoare_load (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((.load x l)) (pure (fun σ => σ x = v) ∗ (l ↦ v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩\n  refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩\n  show Store.set σ x v x = v\n  simp [Store.set]",
      "expl": "The whole proof is choosing the cut. The <code>pure</code> conjunct must own the empty heap, so the split is forced: <code>⟨Heap.empty, Heap.singleton l v, …⟩</code>. Then <code>disjoint_empty_left</code> and <code>(union_empty_left _).symm</code> discharge the two heap obligations, and <code>Store.set σ x v x = v</code> is one <code>simp</code>. Everything else is bookkeeping that the anonymous constructor does for you.",
      "walk": [
        {
          "tac": "intro σ h hp",
          "h": "Unfolds <code>Hoare</code> — silently, because it is a plain <code>def</code> and <code>intro</code> works up to reduction — and takes the universally quantified store, heap, and the precondition. The goal becomes an existential."
        },
        {
          "tac": "subst hp",
          "h": "<code>hp</code> is the equation <code>h = Heap.singleton l v</code>. This eliminates <code>h</code> everywhere and deletes both <code>h</code> and <code>hp</code>. From here on there is one concrete heap in the problem."
        },
        {
          "tac": "refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩",
          "h": "Three things at once. The inner <code>⟨…⟩</code> is the final <code>State</code>: <code>x</code> now holds <code>v</code>, the heap is untouched. The second component is the execution derivation, whose side condition “the cell exists” is exactly <code>singleton_same l v</code>. The <code>?_</code> defers the postcondition."
        },
        {
          "tac": "refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩",
          "h": "The cut. Six components: left heap, right heap, their disjointness, the equation saying they reassemble to the actual heap, the left conjunct, the right conjunct. The <code>.symm</code> is needed because <code>union_empty_left</code> reads <code>Heap.union Heap.empty h = h</code> while the goal wants it the other way round. The nested <code>⟨?_, rfl⟩</code> is the <code>pure</code> conjunct split into its <code>fact</code> part (deferred) and its <code>emp</code> part (<code>rfl</code>, since the left heap literally <i>is</i> <code>Heap.empty</code>). The final <code>rfl</code> is <code>l ↦ v</code> at the right heap, for the same reason."
        },
        {
          "tac": "show Store.set σ x v x = v",
          "h": "The remaining goal is <code>fact (fun σ => σ x = v) {…}.store Heap.empty</code>, which is definitionally the stated equation but does not look like it. <code>show</code> replaces the goal with any definitionally equal one, and here that is the whole point: it makes the goal something <code>simp</code> can attack."
        },
        {
          "tac": "simp [Store.set]",
          "h": "Unfolds <code>Store.set</code> to <code>if x = x then v else σ x</code> and discharges the <code>if</code>. There is no <code>Store.set_same</code> lemma to cite, so this is the idiom."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_load, tactic by tactic",
          "start": "x : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.load x l) ((_root_.pure fun σ => σ x = v) ∗ l ↦ v)",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "x : Var\nl : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.load x l) { store := σ, heap := h } s' ∧ ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) s'.store s'.heap",
              "h": "<code>_root_.pure</code> is Lean disambiguating our <code>pure</code> from the monadic <code>Pure.pure</code> in the core library. It is the same function; ignore the prefix."
            },
            {
              "tac": "subst hp",
              "state": "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.load x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) s'.store s'.heap",
              "h": "<code>h</code> and <code>hp</code> are gone. Compare the two states: this is what an exact precondition buys."
            },
            {
              "tac": "refine ⟨⟨Store.set σ x v, Heap.singleton l v⟩, Exec.load (singleton_same l v), ?_⟩",
              "state": "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store\n    { store := σ.set x v, heap := Heap.singleton l v }.heap",
              "h": "Lean prints <code>Store.set σ x v</code> back as <code>σ.set x v</code> — dot notation on the type of the first explicit argument. The projections <code>{…}.store</code> and <code>{…}.heap</code> are left unreduced in the display; they reduce whenever anything needs them to."
            },
            {
              "tac": "refine ⟨Heap.empty, Heap.singleton l v, disjoint_empty_left _, (union_empty_left _).symm, ⟨?_, rfl⟩, rfl⟩",
              "state": "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store Heap.empty",
              "h": "Five of the six components were supplied outright; only the <code>fact</code> part is left. Notice its heap argument is <code>Heap.empty</code> — the cut has already been committed to."
            },
            {
              "tac": "show Store.set σ x v x = v",
              "state": "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ σ.set x v x = v",
              "h": "<code>fact φ σ h</code> is <code>φ σ</code> by definition, and the store projection reduces. <code>show</code> performs both reductions in the display, which is all that was blocking <code>simp</code>."
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
          "t": "p",
          "h": "Where do the six components come from? If you write <code>refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩</code> instead of supplying them, Lean shows you the skeleton of a <code>∗</code> goal directly, with the two heaps as metavariables that the later goals refer to:"
        },
        {
          "t": "state",
          "src": "case refine_1\n⊢ Heap\n\ncase refine_2\n⊢ Heap\n\ncase refine_3\n⊢ Heap.disjoint ?refine_1 ?refine_2\n\ncase refine_4\n⊢ { store := σ.set x v, heap := Heap.singleton l v }.heap = Heap.union ?refine_1 ?refine_2\n\ncase refine_5\n⊢ _root_.pure (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store ?refine_1\n\ncase refine_6\n⊢ (l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store ?refine_2",
          "cap": "Hypotheses elided. The first two goals are literally “produce a heap”; the last four then constrain those choices. This is the anatomy of every ∗-introduction you will do for the rest of the workbook."
        },
        {
          "t": "cmp",
          "left": {
            "t": "The forced cut",
            "kind": "good",
            "h": "<code>h₁ := Heap.empty</code>, <code>h₂ := Heap.singleton l v</code>. Goal 5 becomes <code>pure φ … Heap.empty</code>, whose <code>emp</code> half is <code>rfl</code>; goal 6 becomes <code>(l ↦ v) … (Heap.singleton l v)</code>, also <code>rfl</code>. Only the store fact is left.",
            "src": "refine ⟨Heap.empty, Heap.singleton l v,\n        disjoint_empty_left _, (union_empty_left _).symm,\n        ⟨?_, rfl⟩, rfl⟩"
          },
          "right": {
            "t": "The other cut",
            "kind": "bad",
            "h": "Swap the two heaps. The disjointness and union obligations still go through — <code>disjoint_empty_right</code> and <code>union_empty_right</code> are just as available as their mirror images — so nothing complains until the last two components. Then both conjuncts land on the wrong heap. Leave all three of them as holes and Lean shows you the damage.",
            "src": "refine ⟨Heap.singleton l v, Heap.empty,\n        disjoint_empty_right _, (union_empty_right _).symm,\n        ⟨?_, ?_⟩, ?_⟩"
          }
        },
        {
          "t": "state",
          "src": "case refine_1\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store (Heap.singleton l v)\n\ncase refine_2\n⊢ emp { store := σ.set x v, heap := Heap.singleton l v }.store (Heap.singleton l v)\n\ncase refine_3\n⊢ (l ↦ v) { store := σ.set x v, heap := Heap.singleton l v }.store Heap.empty",
          "cap": "The swapped cut, hypotheses elided (they are the same four — `x`, `l`, `v`, `σ` — in each goal). Goal 1 is fine: `fact` ignores its heap, so it is still the store equation. Goals 2 and 3 are the two false ones. `emp … (Heap.singleton l v)` asks you to prove `Heap.singleton l v = Heap.empty`; `(l ↦ v) … Heap.empty` asks for `Heap.empty = Heap.singleton l v`. Both are refutable — they are exactly the contradictions the two counterexamples below turn on."
        },
        {
          "t": "detail",
          "title": "Two ways to break the load rule",
          "tag": "counterexample",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "First: you cannot drop the cell from the postcondition. <code>load</code> does not change the heap, so the final heap is still a singleton and cannot satisfy anything ending in <code>emp</code>. The proof cites <code>star_emp_forces_empty</code>, which is the second snippet in “Why <code>pure</code> and not <code>fact</code>” near the top of the chapter — you need both in scope for this to compile."
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem load_must_return_the_cell (x : Var) (l : Loc) (v : Val) :\n    ¬ Hoare (l ↦ v) (.load x l) (pure (fun σ => σ x = v) ∗ emp) := by\n  intro hbad\n  obtain ⟨s', hex, hq⟩ := hbad (fun _ => 0) (Heap.singleton l v) rfl\n  cases hex with\n  | load hl =>\n      have hempty : Heap.singleton l v = Heap.empty := star_emp_forces_empty _ _ _ hq\n      have h1 : Heap.singleton l v l = Heap.empty l := by rw [hempty]\n      rw [singleton_same] at h1\n      exact absurd h1 (by simp [Heap.empty])"
            },
            {
              "t": "p",
              "h": "Second: you cannot weaken the precondition to <code>emp</code>. The failure is of a completely different kind — the command <i>faults</i>, and the existential in <code>Hoare</code> is precisely what forbids that. Nothing about the postcondition is involved, which is why <code>Q</code> here is arbitrary:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem load_from_emp_impossible (x : Var) (l : Loc) (Q : Assertion) :\n    ¬ Hoare emp (.load x l) Q := by\n  intro hbad\n  obtain ⟨s', hex, _⟩ := hbad (fun _ => 0) Heap.empty rfl\n  cases hex with\n  | load hl =>\n      have hne : Heap.empty l = some _ := hl\n      exact absurd hne (by simp [Heap.empty])"
            },
            {
              "t": "p",
              "h": "<code>cases hex</code> is the move that turns an <code>Exec</code> hypothesis into information. There is only one constructor that can produce <code>Exec (.load x l) _ _</code>, so the single branch <code>| load hl</code> hands you its side condition — and that side condition is the contradiction."
            }
          ]
        }
      ],
      "pitfall": "Dropping the <code>show</code>. After the second <code>refine</code> the goal is <code>fact (fun σ => σ x = v) { store := σ.set x v, heap := Heap.singleton l v }.store Heap.empty</code>, and <code>simp [Store.set]</code> alone does not close it: <code>fact</code> is a plain <code>def</code>, not marked <code>@[simp]</code>, so <code>simp</code> beta-reduces the projections and then stops, leaving <code>fact (fun σ => σ x = v) (σ.set x v) Heap.empty</code> — and it will additionally warn you that the <code>Store.set</code> argument went unused, which is a good clue that it never got as far as the store. The fix is the <code>show</code>, exactly as in <code>assign_constant</code> in M6. Adding <code>fact</code> to the simp set also works and is worse: it makes the tactic do the reader’s job invisibly.",
      "variants": "<b>Swap the conjuncts.</b> <code>(l ↦ v) ∗ pure (fun σ => σ x = v)</code> is equally provable — take the mirror cut <code>⟨Heap.singleton l v, Heap.empty, disjoint_empty_right _, (union_empty_right _).symm, rfl, ⟨?_, rfl⟩⟩</code>. Nothing deep happened; <code>∗</code> is commutative (M4), and the two proofs are the same length. <b>Weaken <code>pure</code> to <code>fact</code>.</b> Still provable, and strictly less useful: as the aside above shows, <code>fact φ ∗ P</code> permits the left conjunct to own memory, so the postcondition would stop pinning the final heap and the rule would no longer be small-footprint. <b>Drop the cell.</b> <code>pure (fun σ => σ x = v) ∗ emp</code> is false, because the load leaves the heap alone. <b>Drop the precondition to <code>emp</code>.</b> Also false, for the unrelated reason that the command faults. Both are proved above."
    },
    {
      "t": "ex",
      "id": "m7-2",
      "name": "hoare_write",
      "hard": false,
      "why": "The postcondition is written as an explicit lambda because it depends on the store: the value stored is <code>e</code> evaluated <i>in the final store</i>, which for a write is the same as the initial one. Beyond that, this is the exercise that teaches the layering discipline: a Hoare-triple proof should never contain a <code>funext</code>. The heap algebra was all done in M1; the triple is a wrapper around one citation.",
      "setup": "You will need <code>singleton_same</code> for the side condition and <code>write_singleton</code> for the postcondition. Both are from M1.",
      "goal": "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) (.write l e)\n      (fun σ h => (l ↦ (e.eval σ)) σ h)",
      "hints": [
        "Same opening as the load rule: <code>intro σ h hp</code>, then <code>subst hp</code>. After that the only heap in sight is <code>Heap.singleton l old</code>.",
        "Read the final state off <code>Exec.write</code>: it keeps the store and produces <code>Heap.write s.heap l (e.eval s.store)</code>. With the precondition substituted, that is <code>⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩</code>.",
        "The side condition on <code>Exec.write</code> is about the value that is <i>already</i> there — the cell must exist before you write to it. So it is <code>singleton_same l old</code>, not <code>singleton_same l (e.eval σ)</code>.",
        "That leaves the postcondition: <code>Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l (e.eval σ)</code>. This is <code>write_singleton l old (e.eval σ)</code>. Since all three components are now terms, the whole thing is a single <code>exact ⟨…, …, …⟩</code>."
      ],
      "sol": "theorem hoare_write (l : Loc) (e : Atom) (old : Val) :\n    Hoare (l ↦ old) ((.write l e)) (fun σ h => (l ↦ (e.eval σ)) σ h) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,\n         Exec.write (singleton_same l old),\n         write_singleton l old (e.eval σ)⟩",
      "expl": "If you proved <code>write_singleton</code> in M1 as suggested, this is a single application. If you did not, you are now doing a <code>funext</code> plus case split inside a Hoare-triple proof, which is exactly the kind of layering violation the “separate heap algebra from program semantics” discipline is meant to prevent.",
      "walk": [
        {
          "tac": "intro σ h hp",
          "h": "Opens the triple. Goal: <code>∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ …</code>."
        },
        {
          "tac": "subst hp",
          "h": "Replaces <code>h</code> by <code>Heap.singleton l old</code> and clears both <code>h</code> and <code>hp</code>."
        },
        {
          "tac": "exact ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩,",
          "h": "The final state. The store is unchanged — a write touches memory only — and the heap is the singleton with <code>l</code> overwritten by the value of <code>e</code> in <code>σ</code>. This must be written exactly as <code>Exec.write</code> will produce it, or the next component will not typecheck."
        },
        {
          "tac": "Exec.write (singleton_same l old),",
          "h": "The execution. Its argument is the side condition “<code>l</code> already holds something”, and the something is <code>old</code> — the value in the precondition, not the value being written."
        },
        {
          "tac": "write_singleton l old (e.eval σ)⟩",
          "h": "The postcondition, which after reduction is the heap equation <code>Heap.write (Heap.singleton l old) l (e.eval σ) = Heap.singleton l (e.eval σ)</code>. One M1 lemma, applied to its three arguments. No tactic needed."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_write, tactic by tactic",
          "start": "l : Loc\ne : Atom\nold : Val\n⊢ Hoare (l ↦ old) (Cmd.write l e) fun σ h => (l ↦ Atom.eval σ e) σ h",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "l : Loc\ne : Atom\nold : Val\nσ : Store\nh : Heap\nhp : (l ↦ old) σ h\n⊢ ∃ s', Exec (Cmd.write l e) { store := σ, heap := h } s' ∧ (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap",
              "h": "Lean prints <code>e.eval σ</code> back as <code>Atom.eval σ e</code>: the source used dot notation, the pretty-printer does not. Same term."
            },
            {
              "tac": "subst hp",
              "state": "l : Loc\ne : Atom\nold : Val\nσ : Store\n⊢ ∃ s',\n    Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old } s' ∧\n      (fun σ h => (l ↦ Atom.eval σ e) σ h) s'.store s'.heap",
              "h": "As before."
            },
            {
              "tac": "refine ⟨⟨σ, Heap.write (Heap.singleton l old) l (e.eval σ)⟩, ?_, ?_⟩",
              "state": "case refine_1\n⊢ Exec (Cmd.write l e) { store := σ, heap := Heap.singleton l old }\n    { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }\n\ncase refine_2\n⊢ (fun σ h => (l ↦ Atom.eval σ e) σ h) { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.store\n    { store := σ, heap := (Heap.singleton l old).write l (Atom.eval σ e) }.heap",
              "h": "Not in the solution — the solution supplies both components at once with <code>exact</code>. Splitting them out with <code>refine</code> is how you find out what you owe. Goal 1 is closed by <code>Exec.write (singleton_same l old)</code>; goal 2 reduces to the M1 equation and is closed by <code>write_singleton l old (e.eval σ)</code>. Hypotheses elided."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why the postcondition is a lambda and not just l ↦ e",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "<code>e</code> is a syntactic <code>Atom</code>, not a value, so “<code>l</code> points to <code>e</code>” is not even well typed. What we mean is “<code>l</code> points to the <i>value of</i> <code>e</code>”, and that value depends on the store. An <code>Assertion</code> is a function of a store, so the only way to say it is to bind the store: <code>fun σ h => (l ↦ (e.eval σ)) σ h</code>."
            },
            {
              "t": "p",
              "h": "When <code>e</code> is a constant, the dependence is vacuous and the lambda eta-reduces to a plain <code>↦</code> — that is exactly what makes the next exercise a one-liner. When <code>e</code> mentions a variable, it does not:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem copyVar_spec (x : Var) (l : Loc) (old : Val) :\n    Hoare (l ↦ old) (.write l (.var x)) (fun σ h => (l ↦ σ x) σ h) :=\n  hoare_write l (.var x) old"
            },
            {
              "t": "p",
              "h": "There is no constant <code>c</code> for which <code>l ↦ c</code> states that specification. M9 introduces a variant that moves the awkwardness to the precondition, where it is easier to discharge: <code>hoare_write_val (l : Loc) (e : Atom) (old v : Val) : Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v)</code>. You now name the value <code>v</code> yourself and owe a hypothesis that <code>e</code> evaluates to it; in exchange the postcondition is a plain <code>↦</code> that the next rule can match. Note it is <code>aAnd</code> with <code>fact</code>, not <code>∗</code> with <code>pure</code> — the precondition’s heap is the cell, not empty, so the fact has to be conjoined <i>on the same heap</i>, not separated from it."
            }
          ]
        },
        {
          "t": "detail",
          "title": "The wrong side condition, and what Lean says",
          "tag": "error",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Supplying <code>singleton_same l (e.eval σ)</code> — the value being written — instead of <code>singleton_same l old</code> gives:"
            },
            {
              "t": "state",
              "src": "error: Application type mismatch: The argument\n  singleton_same l (Atom.eval σ e)\nhas type\n  Heap.singleton l (Atom.eval σ e) l = some (Atom.eval σ e)\nbut is expected to have type\n  { store := σ, heap := Heap.singleton l old }.heap l = some ?m.23\nin the application\n  Exec.write (singleton_same l (Atom.eval σ e))"
            },
            {
              "t": "p",
              "h": "Read it as: the constructor asked about the heap <i>before</i> the write, and you told it about the heap after. The <code>?m.23</code> is the implicit <code>old</code> of <code>Exec.write</code>, still waiting to be determined; Lean was happy to infer it from your argument and then found the heaps did not match."
            }
          ]
        }
      ],
      "pitfall": "Proving the heap equation inline. If you skipped <code>write_singleton</code> in M1, the natural reflex is <code>funext x; by_cases hx : x = l</code> right here, inside the triple. It works, and it is in the wrong place: you now have a proof about the operational semantics with a proof about partial functions embedded in it, and the next such proof will embed the same argument again. The rule is worth stating flatly — <b>if a Hoare proof contains <code>funext</code>, a heap lemma is missing.</b> The other reflex, reaching for <code>simp</code> on the postcondition, does nothing useful: <code>Heap.write</code> and <code>Heap.singleton</code> are ordinary <code>def</code>s and <code>simp</code> will not unfold them unless you say so, at which point you are doing the <code>funext</code> proof again with extra steps.",
      "variants": "<b>Weaken the precondition to <code>emp</code>.</b> False, and for the operational reason: <code>Exec.write</code> requires <code>s.heap l = some old</code>, so a write to a cell you do not own is a fault, and the existential in <code>Hoare</code> rules it out. The refutation is <code>load_from_emp_impossible</code> above with <code>load</code> replaced by <code>write</code> throughout — same six lines, same contradiction extracted from the side condition, and again the postcondition is an arbitrary <code>Q</code> because it plays no part. <b>Fix the postcondition to <code>l ↦ 0</code>.</b> False as soon as <code>e</code> is <code>.var x</code> and the store maps <code>x</code> elsewhere. The lambda is not decoration. <b>Drop <code>old</code>.</b> You cannot: it is the witness that the cell exists, and it is the only thing the precondition can say, since the write does not care what was there. That indifference is why <code>write_singleton</code> is stated with two independent values <code>v</code> and <code>w</code>."
    },
    {
      "t": "ex",
      "id": "m7-3",
      "name": "hoare_free",
      "hard": false,
      "why": "Mechanically this is the write rule with <code>erase</code> in place of <code>write</code>, and you should be able to do it by editing three words. It earns its place for a different reason: it is the rule that is <b>false</b> under any inexact reading of <code>↦</code>. Prove it in three lines, then read the counterexample at the top of the chapter again and notice that the three lines only worked because the precondition was an equation.",
      "setup": "You need <code>singleton_same</code> for the side condition of <code>Exec.free</code>, and <code>erase_singleton</code> for the postcondition.",
      "goal": "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) (.free l) emp",
      "hints": [
        "Copy the shape of <code>hoare_write</code> and change three words.",
        "<code>Exec.free</code> keeps the store and erases from the heap, so the final state is <code>⟨σ, Heap.erase (Heap.singleton l v) l⟩</code>. Its side condition is again “the cell exists”: <code>singleton_same l v</code>.",
        "The postcondition <code>emp</code> is <code>fun _ h => h = Heap.empty</code>, so what you owe is <code>Heap.erase (Heap.singleton l v) l = Heap.empty</code>. That is <code>erase_singleton l v</code> — supply it directly with <code>exact</code>; do not try to rewrite with it."
      ],
      "sol": "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) ((.free l)) (emp) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,\n         Exec.free (singleton_same l v),\n         erase_singleton l v⟩",
      "expl": "Three lines, and the mathematical content is entirely in <code>erase_singleton : Heap.erase (Heap.singleton l v) l = Heap.empty</code>. This is the rule that would be unsound with an inexact <code>↦</code>; here it is trivial.",
      "walk": [
        {
          "tac": "intro σ h hp",
          "h": "Opens the triple; goal becomes <code>∃ s', Exec (Cmd.free l) { store := σ, heap := h } s' ∧ emp s'.store s'.heap</code>."
        },
        {
          "tac": "subst hp",
          "h": "Replaces <code>h</code> by <code>Heap.singleton l v</code> throughout and clears the variable."
        },
        {
          "tac": "exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,",
          "h": "The final state: same store, heap with <code>l</code> removed. Written exactly as <code>Exec.free</code> will produce it."
        },
        {
          "tac": "Exec.free (singleton_same l v),",
          "h": "The execution derivation. You may not free a cell you do not own, and this argument is where you prove you own it."
        },
        {
          "tac": "erase_singleton l v⟩",
          "h": "The postcondition. <code>emp s'.store s'.heap</code> reduces to <code>Heap.erase (Heap.singleton l v) l = Heap.empty</code>, which is this lemma applied to its two arguments."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_free, tactic by tactic",
          "start": "l : Loc\nv : Val\n⊢ Hoare (l ↦ v) (Cmd.free l) emp",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "l : Loc\nv : Val\nσ : Store\nh : Heap\nhp : (l ↦ v) σ h\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := h } s' ∧ emp s'.store s'.heap",
              "h": "The postcondition is displayed as <code>emp s'.store s'.heap</code> — <code>emp</code> ignores the store, but an <code>Assertion</code> takes both, so both are passed."
            },
            {
              "tac": "subst hp",
              "state": "l : Loc\nv : Val\nσ : Store\n⊢ ∃ s', Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } s' ∧ emp s'.store s'.heap",
              "h": ""
            },
            {
              "tac": "refine ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_⟩",
              "state": "case refine_1\n⊢ Exec (Cmd.free l) { store := σ, heap := Heap.singleton l v } { store := σ, heap := (Heap.singleton l v).erase l }\n\ncase refine_2\n⊢ emp { store := σ, heap := (Heap.singleton l v).erase l }.store\n    { store := σ, heap := (Heap.singleton l v).erase l }.heap",
              "h": "Again not in the solution, but this is what the two components of the <code>exact</code> are proving. Hypotheses elided. Goal 2 <i>is</i> <code>erase_singleton l v</code>, once the projection reduces — which is why <code>exact</code> accepts the lemma with no massaging."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "anat",
          "src": "theorem hoare_free (l : Loc) (v : Val) : Hoare (l ↦ v) ((.free l)) (emp) := by\n  intro σ h hp\n  subst hp\n  exact ⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,\n         Exec.free (singleton_same l v),\n         erase_singleton l v⟩",
          "parts": [
            {
              "m": "((.free l))",
              "h": "The doubled parentheses are an artefact of how the statement was generated, not syntax you need. <code>.free l</code> is <code>Cmd.free l</code>. The leading dot is <i>not</i> the anonymous constructor <code>⟨…⟩</code> — it is Lean looking the name up in the namespace of the <b>expected</b> type. <code>Hoare</code>’s second argument must be a <code>Cmd</code>, so <code>.free</code> resolves to <code>Cmd.free</code>. Where the expected type is unknown you get an error rather than a guess: <code>#check .free 0</code> reports “the expected type of <code>.free</code> could not be determined” and then lists <code>Cmd.free</code> and <code>Exec.free</code> as the candidates it was choosing between."
            },
            {
              "m": "⟨⟨σ, Heap.erase (Heap.singleton l v) l⟩,",
              "h": "Two nested anonymous constructors. The outer one builds the <code>∃ s', _ ∧ _</code>; the inner one builds the <code>State</code> structure from a store and a heap. <code>⟨…⟩</code> flattens across the existential and the conjunction, which is why three components suffice for what is formally a pair-of-a-pair."
            },
            {
              "m": "Exec.free (singleton_same l v)",
              "h": "Where non-faulting is established. Every memory operation in this language has a constructor with a side condition of this form, and every one of these proofs discharges it with <code>singleton_same</code>."
            },
            {
              "m": "erase_singleton l v",
              "h": "The whole theorem. Everything above it is plumbing between <code>Hoare</code> and <code>Exec</code>; this is the only line with content, and it was proved back in M1 by <code>funext</code> and a case split."
            }
          ]
        }
      ],
      "pitfall": "Reaching for <code>rw [erase_singleton]</code> instead of <code>exact erase_singleton l v</code>. It looks like it should work and it half does: <code>rw</code> rewrites inside the state and leaves you with <code>⊢ emp { store := σ, heap := Heap.empty }.store { store := σ, heap := Heap.empty }.heap</code> and an “unsolved goals” error, because the <code>rfl</code> that <code>rw</code> tries afterwards does not unfold <code>emp</code>. Adding a bare <code>rfl</code> on the next line fixes it, but the direct <code>exact</code> was always available — application typechecks up to reduction, and <code>emp … …</code> reduces to the equation. Same story with <code>simp [emp]</code>: it turns the goal into <code>(Heap.singleton l v).erase l = Heap.empty</code>, which is progress you did not need to make.",
      "variants": "<b>Make <code>↦</code> inexact.</b> The rule becomes false; the counterexample is at the top of this chapter, with the heap <code>fun _ => some 0</code> as witness. This is the single most important “what breaks” in the module. <b>Weaken the precondition to <code>emp</code>.</b> False — <code>Exec.free</code> demands the cell exists. <b>Strengthen the postcondition to <code>l ↦ v</code>.</b> False, obviously: the cell is gone. Worth writing down anyway, because the corresponding claim for <code>load</code> is <i>true</i> and the asymmetry is the substructural character of the logic showing through. <b>Free twice.</b> <code>.free l ;; .free l</code> has no valid triple from <code>l ↦ v</code>, because the second <code>Exec.free</code> cannot find the cell. Compare with M14, where allocation is the operation that puts one back."
    },
    {
      "t": "sec",
      "s": "Exercises · two derived programs"
    },
    {
      "t": "ex",
      "id": "m7-4",
      "name": "clearCell_spec",
      "hard": false,
      "why": "Your first specification of a <i>named program</i> rather than a bare command, and a free lesson in Lean’s definitional equality. Three separate unfoldings happen silently between the general write rule and this statement; if any one of them did not, you would have to insert <code>hoare_consequence</code> here, and the proof would be five lines instead of one. Knowing which identifications Lean makes for free is a large part of writing short Lean proofs.",
      "setup": "<code>hoare_write</code> from the previous exercise, and nothing else. The proof is a term, not a tactic block.",
      "goal": "def clearCell (l : Loc) : Cmd := .write l (.const 0)\n\ntheorem clearCell_spec (l : Loc) (old : Val) :\n    Hoare (l ↦ old) (clearCell l) (l ↦ 0)",
      "hints": [
        "You do not need <code>by</code> at all. <code>hoare_write</code> already has the right shape; the only question is what to instantiate it with.",
        "The instance is <code>e := .const 0</code>. So the candidate term is <code>hoare_write l (.const 0) old</code> — write it and see whether Lean complains.",
        "It does not complain. If you want to know why, ask Lean directly: <code>example (σ : Store) : (Atom.const 0).eval σ = 0 := rfl</code> and <code>example (l : Loc) : (fun σ h => (l ↦ ((Atom.const 0).eval σ)) σ h) = (l ↦ (0 : Val)) := rfl</code> both compile."
      ],
      "sol": "def clearCell (l : Loc) : Cmd := .write l (.const 0)\n\ntheorem clearCell_spec (l : Loc) (old : Val) : Hoare (l ↦ old) ((clearCell l)) (l ↦ 0) :=\n  hoare_write l (.const 0) old",
      "expl": "<code>(Atom.const 0).eval σ</code> reduces to <code>0</code> definitionally, so the specialised postcondition matches on the nose and no <code>hoare_consequence</code> is needed.",
      "walk": [
        {
          "tac": "def clearCell (l : Loc) : Cmd := .write l (.const 0)",
          "h": "The program. <code>.write</code> and <code>.const</code> are constructors of <code>Cmd</code> and <code>Atom</code>, written with the leading dot because the expected type is known from the signature. Naming it matters: from here on you can state and reuse a specification for <code>clearCell</code> without re-mentioning its body."
        },
        {
          "tac": ":=",
          "h": "No <code>by</code>. A theorem whose proof is a single application is better written as a term — there is no goal state to inspect, no tactic to fail, and the elaborator reports the mismatch directly if there is one."
        },
        {
          "tac": "hoare_write l (.const 0) old",
          "h": "The general write rule at <code>e := .const 0</code>. Its type is <code>Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h</code>, which is <i>not</i> syntactically the stated goal. Lean accepts it because the two are definitionally equal, by three separate reductions."
        }
      ],
      "deep": [
        {
          "t": "steps",
          "title": "The three silent identifications",
          "items": [
            {
              "k": "δ — unfold the def",
              "h": [
                {
                  "t": "p",
                  "h": "<code>clearCell l</code> is a defined constant; unfolding it gives <code>Cmd.write l (Atom.const 0)</code>. This one is uncontroversial, but note that it is not free in every proof assistant, and that <code>rw</code> would not have done it for you."
                },
                {
                  "t": "code",
                  "tag": "illustration",
                  "src": "example (l : Loc) : clearCell l = Cmd.write l (.const 0) := rfl"
                }
              ]
            },
            {
              "k": "ι — evaluate the match",
              "h": [
                {
                  "t": "p",
                  "h": "<code>Atom.eval</code> is defined by pattern matching. Applied to a literal constructor <code>Atom.const 0</code> it selects a branch and returns <code>0</code>. Applied to a <i>variable</i> <code>e</code> it is stuck, which is why the general rule has to keep the lambda."
                },
                {
                  "t": "code",
                  "tag": "illustration",
                  "src": "example (σ : Store) : (Atom.const 0).eval σ = 0 := rfl"
                }
              ]
            },
            {
              "k": "η — collapse the lambda",
              "h": [
                {
                  "t": "p",
                  "h": "After the previous step the postcondition is <code>fun σ h => (l ↦ 0) σ h</code>, and the goal wants <code>l ↦ 0</code>. In Lean 4 eta-equality for functions is part of definitional equality, so these are the same term and there is no lemma to invoke. In a system without eta you would need <code>funext</code> twice, and this exercise would be a genuine proof."
                },
                {
                  "t": "code",
                  "tag": "illustration",
                  "src": "example (l : Loc) :\n    (fun σ h => (l ↦ ((Atom.const 0).eval σ)) σ h) = (l ↦ (0 : Val)) := rfl"
                }
              ]
            }
          ]
        },
        {
          "t": "p",
          "h": "You can watch the elaborator do it. <code>#check fun (l : Loc) (old : Val) => hoare_write l (.const 0) old</code> prints the type <i>before</i> any of the three reductions:"
        },
        {
          "t": "state",
          "src": "fun l old =>\n  hoare_write l (Atom.const 0)\n    old : ∀ (l : Loc) (old : Val),\n  Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) fun σ h => (l ↦ Atom.eval σ (Atom.const 0)) σ h",
          "cap": "Compare with the goal, `Hoare (l ↦ old) (clearCell l) (l ↦ 0)`. Three differences, all of them definitional."
        }
      ],
      "pitfall": "Dropping into <code>by</code> and trying to open the definitions by hand before applying the lemma. Both <code>rw [clearCell]</code> and <code>simp [clearCell]</code> do work — Lean generates an equation lemma for every <code>def</code>, so a bare definition name is a legal rewrite — and both leave you at <code>⊢ Hoare (l ↦ old) (Cmd.write l (Atom.const 0)) (l ↦ 0)</code>, which is no closer to anything. Push on to the next reduction and it stops working: <code>rw [Atom.eval]</code> fails with <code>Failed to rewrite using equation theorems for &#39;Atom.eval&#39;</code>, because a function defined by pattern matching compiles to a matcher and has no single equation to rewrite with. None of it was needed — the term already typechecks. The general habit worth forming: when you suspect two statements are definitionally equal, do not guess and do not fight the tactic — ask Lean with <code>example : A = B := rfl</code>. If it compiles, you can apply one where the other is expected, and you will never need a lemma. If it does not, you know you genuinely need <code>hoare_consequence</code>.",
      "variants": "<b>Use a store-dependent atom.</b> Replace <code>.const 0</code> by <code>.var x</code> and the postcondition can no longer be written <code>l ↦ c</code> for any constant <code>c</code>; the best you can state is <code>fun σ h => (l ↦ σ x) σ h</code>, which is <code>copyVar_spec</code> in the previous exercise’s notes. The ι-step disappears and the η-step has nothing to collapse. <b>Change the postcondition to <code>l ↦ 1</code>.</b> The term stops typechecking, and no amount of <code>rfl</code> will help — you would need a false lemma. <b>Change the precondition to <code>emp</code>.</b> False: <code>clearCell</code> writes, and writing needs the cell. It does not allocate; nothing in this language does until M14."
    },
    {
      "t": "ex",
      "id": "m7-5",
      "name": "readAndFree_spec",
      "hard": false,
      "why": "Read a cell, then give the memory back, keeping only the knowledge. The postcondition owns nothing — the value survives in a variable. It is also the exercise built to make you want the frame rule: the obvious composition does not typecheck, and finding out exactly why is worth more than the proof itself.",
      "setup": "You have <code>hoare_seq</code> from M6 and the three rules you just proved. You do <b>not</b> have <code>hoare_frame</code>; that is M8.",
      "goal": "def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l\n\ntheorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v))",
      "hints": [
        "Try the obvious thing first — <code>hoare_seq (hoare_load x l v) (hoare_free l v)</code> — and read the error carefully. The mismatch it reports is the entire point of the exercise.",
        "Since you cannot compose the triples, go underneath them. Same opening as everything else in this chapter: <code>intro σ h hp</code>, <code>subst hp</code>.",
        "Name the final state of the <i>whole program</i>, not of one step: the load sets <code>x</code> to <code>v</code>, the free erases <code>l</code>. That is <code>⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩</code>. Both steps look at the cell before it is freed, so both side conditions are the same <code>singleton_same l v</code>, and <code>Exec.seq</code> glues the two derivations.",
        "<code>pure φ</code> is <code>aAnd (fact φ) emp</code>, i.e. a conjunction, so once the state is named the goal flattens into three obligations: the execution, the store fact, and the heap being empty. Use <code>refine ⟨⟨…⟩, ?_, ?_, ?_⟩</code> and take them with <code>·</code> bullets. The middle one needs a <code>show</code> before <code>simp</code>, exactly as in the load rule."
      ],
      "sol": "def readAndFree (x : Var) (l : Loc) : Cmd := .load x l ;; .free l\n\ntheorem readAndFree_spec (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) ((readAndFree x l)) (pure (fun σ => σ x = v)) := by\n  intro σ h hp\n  subst hp\n  refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩\n  · exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))\n  · show Store.set σ x v x = v\n    simp [Store.set]\n  · exact erase_singleton l v",
      "expl": "Do this once by hand, and notice the discomfort: to sequence the two rules you had to abandon them and go back to the operational semantics, because the load’s postcondition <code>pure … ∗ l ↦ v</code> does not literally match the free’s precondition <code>l ↦ v</code>. The missing tool is the frame rule, and M8 is precisely about earning it. M9 then redoes proofs of this shape — <code>copyCell</code>, <code>moveCell</code>, <code>swap</code> — out of nothing but <code>hoare_seq</code>, <code>hoare_frame</code> and <code>hoare_consequence</code>. Those proofs are not shorter on the page; what they no longer contain is a final state you had to invent, a <code>singleton_same</code>, or the word <code>Exec</code>.",
      "walk": [
        {
          "tac": "intro σ h hp",
          "h": "Opens the triple, as always."
        },
        {
          "tac": "subst hp",
          "h": "Replaces <code>h</code> by <code>Heap.singleton l v</code>."
        },
        {
          "tac": "refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩",
          "h": "Names the final state of the whole two-command program and defers all three remaining obligations. Three, not two, because <code>pure φ</code> is a conjunction and the anonymous constructor flattens it into the existential."
        },
        {
          "tac": "· exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))",
          "h": "The execution. <code>Exec.seq</code> takes two derivations and an implicit intermediate state, which Lean infers: it is <code>⟨Store.set σ x v, Heap.singleton l v⟩</code>, the state after the load. Both side conditions are the <i>same</i> proof term, because the load did not change the heap."
        },
        {
          "tac": "· show Store.set σ x v x = v",
          "h": "The <code>fact</code> half of <code>pure</code>. As in <code>hoare_load</code>, the goal is definitionally this equation but does not display as one, and <code>simp</code> will not get there on its own."
        },
        {
          "tac": "simp [Store.set]",
          "h": "Closes it by unfolding <code>Store.set</code> and evaluating the <code>if</code>."
        },
        {
          "tac": "· exact erase_singleton l v",
          "h": "The <code>emp</code> half: the final heap is <code>Heap.erase (Heap.singleton l v) l</code>, and that equals <code>Heap.empty</code>. This is the free rule’s content, cited again — and it is the only sense in which this proof reuses <code>hoare_free</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "readAndFree_spec, tactic by tactic",
          "start": "x : Var\nl : Loc\nv : Val\n⊢ Hoare (l ↦ v) (readAndFree x l) (_root_.pure fun σ => σ x = v)",
          "steps": [
            {
              "tac": "intro σ h hp ; subst hp",
              "state": "x : Var\nl : Loc\nv : Val\nσ : Store\n⊢ ∃ s',\n    Exec (readAndFree x l) { store := σ, heap := Heap.singleton l v } s' ∧\n      _root_.pure (fun σ => σ x = v) s'.store s'.heap",
              "h": "Note that <code>readAndFree x l</code> is <i>not</i> unfolded in the display. It will be unfolded when <code>Exec.seq</code> is applied, because the constructor’s conclusion has to match <code>Exec (c₁ ;; c₂) _ _</code> and that match reduces the definition."
            },
            {
              "tac": "refine ⟨⟨Store.set σ x v, Heap.erase (Heap.singleton l v) l⟩, ?_, ?_, ?_⟩",
              "state": "case refine_1\n⊢ Exec (readAndFree x l) { store := σ, heap := Heap.singleton l v }\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }\n\ncase refine_2\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap\n\ncase refine_3\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
              "h": "Three goals, one per <code>?_</code>. Hypotheses elided; they are the same four in each case. Goal 2 and goal 3 are the two halves of <code>pure</code>: <code>aAnd (fact φ) emp</code> unfolded."
            },
            {
              "tac": "· exact Exec.seq (Exec.load (singleton_same l v)) (Exec.free (singleton_same l v))",
              "state": "case refine_2\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ fact (fun σ => σ x = v) { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap\n\ncase refine_3\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
              "h": "Two goals left, and both are shown — the bullet closed <code>refine_1</code> and handed the rest back. The bullet <code>·</code> focuses on the first goal and requires it to be closed before moving on; without bullets the three goals stay in a pile and a stray tactic can silently act on the wrong one. The next two lines run <i>inside</i> the second bullet, so from here on the display shows <code>refine_2</code> alone."
            },
            {
              "tac": "· show Store.set σ x v x = v",
              "state": "case refine_2\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ σ.set x v x = v",
              "h": "Two reductions at once: <code>fact φ σ h</code> becomes <code>φ σ</code>, and <code>{…}.store</code> becomes <code>σ.set x v</code>."
            },
            {
              "tac": "simp [Store.set]",
              "state": "case refine_3\nx : Var\nl : Loc\nv : Val\nσ : Store\n⊢ emp { store := σ.set x v, heap := (Heap.singleton l v).erase l }.store\n    { store := σ.set x v, heap := (Heap.singleton l v).erase l }.heap",
              "h": "Goal 2 closed, so the second bullet ends and the display returns to the outer level. One goal left: the heap is empty, which is <code>erase_singleton l v</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "The proof you cannot write yet",
          "tag": "error",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Here is the composition anyone would try first, and Lean’s answer:"
            },
            {
              "t": "code",
              "tag": "sketch",
              "src": "theorem naive (x : Var) (l : Loc) (v : Val) :\n    Hoare (l ↦ v) (readAndFree x l) (pure (fun σ => σ x = v)) :=\n  hoare_seq (hoare_load x l v) (hoare_free l v)"
            },
            {
              "t": "state",
              "src": "error: Application type mismatch: The argument\n  hoare_free l v\nhas type\n  Hoare (l ↦ v) (Cmd.free l) emp\nbut is expected to have type\n  Hoare ((_root_.pure fun σ => σ x = v) ∗ l ↦ v) (Cmd.free l) (_root_.pure fun σ => σ x = v)\nin the application\n  hoare_seq (hoare_load x l v) (hoare_free l v)"
            },
            {
              "t": "p",
              "h": "Read the two types against each other. <code>hoare_seq</code> requires the postcondition of the first triple to be <i>the same assertion</i> as the precondition of the second — Lean unified the intermediate assertion <code>Q</code> with the load’s output, <code>pure … ∗ l ↦ v</code>, and then demanded a triple for <code>free</code> starting there. What you have starts at <code>l ↦ v</code>."
            },
            {
              "t": "steps",
              "title": "What would actually close the gap",
              "items": [
                {
                  "k": "Carry the pure fact through the free",
                  "h": "The free has to run with <code>pure φ</code> along for the ride. That is the frame rule, which M8 states as <code>hoare_frame : Hoare P c Q → HeapLocal c → Preserves c R → Hoare (P ∗ R) c (Q ∗ R)</code> — note the frame lands on the <b>right</b> of both stars. So <code>hoare_free l v</code> with <code>R := pure φ</code> buys you <code>Hoare ((l ↦ v) ∗ pure φ) (.free l) (emp ∗ pure φ)</code>, and it costs two side conditions: <code>HeapLocal (.free l)</code>, that freeing behaves the same inside a larger heap, and <code>Preserves (.free l) (pure φ)</code>, that freeing does not disturb the store <code>φ</code> talks about. Both are M8 exercises."
                },
                {
                  "k": "Reshape both ends",
                  "h": "Neither end matches yet, and for different reasons. The load hands you <code>pure φ ∗ (l ↦ v)</code> while the framed rule wants <code>(l ↦ v) ∗ pure φ</code>: that is <code>star_comm</code>, and it is needed <i>because</i> the frame goes on the right. The postcondition <code>emp ∗ pure φ</code> collapses to <code>pure φ</code> by <code>star_emp_left</code>. Feed the two to <code>hoare_consequence</code>, then <code>hoare_seq</code> the result onto <code>hoare_load</code>. Structural rules only; no <code>Exec</code>."
                },
                {
                  "k": "Notice what you avoided",
                  "h": "In the frame-rule proof you would never write down the final state, never cite <code>singleton_same</code>, and never mention <code>Heap.erase</code>. The whole reason M8 is worth six exercises is that it deletes those three obligations from every proof at once."
                }
              ]
            }
          ]
        },
        {
          "t": "detail",
          "title": "Breaking it two ways",
          "tag": "counterexample",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The postcondition cannot keep the cell — the program gave it back:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem no_cell_in_empty (φ : Store → Prop) (l : Loc) (v : Val) (σ : Store) :\n    ¬ (pure φ ∗ (l ↦ v)) σ Heap.empty := by\n  intro ⟨h₁, h₂, _, hu, ⟨_, he₁⟩, he₂⟩\n  subst he₁; subst he₂\n  rw [union_empty_left] at hu\n  have h1 : Heap.empty l = Heap.singleton l v l := by rw [hu]\n  rw [singleton_same] at h1\n  exact absurd h1 (by simp [Heap.empty])"
            },
            {
              "t": "p",
              "h": "And the two commands do not commute — reversing them makes the program fault, so <i>no</i> postcondition is provable, not even <code>aTrue</code>:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem free_then_load_faults (x : Var) (l : Loc) (v : Val) :\n    ¬ Hoare (l ↦ v) (.free l ;; .load x l) aTrue := by\n  intro hbad\n  obtain ⟨s', hex, _⟩ := hbad (fun _ => 0) (Heap.singleton l v) rfl\n  cases hex with\n  | seq h1 h2 =>\n      cases h1 with\n      | free hl =>\n          cases h2 with\n          | load hl2 =>\n              have hgone : Heap.erase (Heap.singleton l v) l l = some _ := hl2\n              rw [erase_same] at hgone\n              exact absurd hgone (by simp)"
            },
            {
              "t": "p",
              "h": "Three nested <code>cases</code>, one per constructor in the derivation, and then the contradiction falls out of the innermost side condition. This is the shape of every “that program faults” argument in the workbook."
            }
          ]
        }
      ],
      "pitfall": "Forgetting the <code>show</code> in the middle bullet, and then trusting <code>simp</code>. You get an <code>unsolved goals</code> error with residue <code>fact (fun σ => σ x = v) (σ.set x v) ((Heap.singleton l v).erase l)</code> and a warning that the <code>Store.set</code> simp argument was unused — <code>simp</code> reduced the two projections and stopped at <code>fact</code>, which it has no reason to unfold. The second, subtler point is the count: it is <code>refine ⟨⟨…⟩, ?_, ?_, ?_⟩</code> with <b>three</b> holes, not two, because <code>pure φ</code> is <code>aAnd (fact φ) emp</code> and the anonymous constructor flattens that conjunction into the existential. Two holes is <i>also</i> accepted — you then get one goal <code>_root_.pure (fun σ => σ x = v) {…}.store {…}.heap</code> which you must split by hand with <code>constructor</code> or another <code>⟨_, _⟩</code>. Neither is wrong; what will confuse you is expecting a fixed number of holes for a <code>refine</code>. The anonymous constructor takes as many as you give it and nests the remainder.",
      "variants": "<b>Reverse the commands.</b> <code>.free l ;; .load x l</code> admits no triple at all from <code>l ↦ v</code>: the load faults on a cell that is gone. Proved above. <b>Keep the cell in the postcondition.</b> <code>pure (fun σ => σ x = v) ∗ (l ↦ v)</code> is false — the final heap is empty and cannot be split so that one part is a singleton. Also proved above. <b>Drop the pure fact.</b> <code>Hoare (l ↦ v) (readAndFree x l) emp</code> is true and considerably easier; the point of keeping the fact is that it is the only trace of the data that survives, and it costs no memory to keep. <b>Change the precondition to <code>l ↦ w</code> and leave the postcondition saying <code>σ x = v</code>.</b> False whenever <code>w ≠ v</code>, and the failure is not operational — the program runs perfectly well, it just leaves <code>w</code> in <code>x</code>. The <code>v</code> in the postcondition is tied to the <code>v</code> in the precondition by the load rule and by nothing else; the command <code>.load x l</code> does not mention a value at all. That is the general shape of a data-flow fact in this logic: it always travels through an assertion, never through the syntax of the program."
    },
    {
      "t": "h3",
      "s": "What is missing"
    },
    {
      "t": "p",
      "h": "Look back at the five proofs. Three of them are the same four lines with different nouns; the fourth is those four lines instantiated, for free, by definitional equality; the fifth is the same four lines again, done by hand, because there was no other option. That is a good sign for the rules and a bad sign for the method. The effort in the last exercise scaled with the <i>program</i> — two commands, two <code>Exec</code> derivations, one state written out in full — and the moment a specification mentions two cells instead of one, the same proof will scale with the <i>heap</i> as well."
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Where this goes",
      "h": "M8 proves the frame rule — <b>from</b> the operational semantics, not as an axiom — which lets you apply any of these three triples inside an arbitrary larger heap without changing a character of the proof. M9 then adds the four-lemma vocabulary (<code>hoare_seq</code>, <code>hoare_frame</code>, <code>hoare_consequence</code>, and the small rules) that makes real programs routine, and states the discipline flatly: if <code>Exec</code> appears in your proof, you are missing a lemma."
    },
    {
      "t": "dod",
      "h": "You have proved the local rules for load, write and free directly from the operational semantics, and you have felt the need for a structural rule to compose them."
    }
  ]
});
